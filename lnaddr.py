#! /usr/bin/env python3
from bech32 import bech32_encode, bech32_decode, CHARSET
from binascii import hexlify, unhexlify
from bitstring import BitArray
from collections import defaultdict
from decimal import Decimal
from enum import IntFlag
from typing import Sequence

import base58
import bitstring
import enum
import hashlib
import math
import re
import secp256k1
import sys
import time


# BOLT #11:
#
# A writer MUST encode `amount` as a positive decimal integer with no
# leading zeroes, SHOULD use the shortest representation possible.
def shorten_amount(amount):
    """ Given an amount in bitcoin, shorten it
    """
    # Convert to pico initially
    amount = int(amount * 10**12)
    units = ['p', 'n', 'u', 'm', '']
    for unit in units:
        if amount % 1000 == 0:
            amount //= 1000
        else:
            break
    return str(amount) + unit

def unshorten_amount(amount):
    """ Given a shortened amount, convert it into a decimal
    """
    # BOLT #11:
    # The following `multiplier` letters are defined:
    #
    #* `m` (milli): multiply by 0.001
    #* `u` (micro): multiply by 0.000001
    #* `n` (nano): multiply by 0.000000001
    #* `p` (pico): multiply by 0.000000000001
    units = {
        'p': 10**12,
        'n': 10**9,
        'u': 10**6,
        'm': 10**3,
    }
    unit = str(amount)[-1]
    # BOLT #11:
    # A reader SHOULD fail if `amount` contains a non-digit, or is followed by
    # anything except a `multiplier` in the table above.
    if not re.fullmatch("\d+[pnum]?", str(amount)):
        raise ValueError("Invalid amount '{}'".format(amount))

    if unit in units.keys():
        return Decimal(amount[:-1]) / units[unit]
    else:
        return Decimal(amount)

# Bech32 spits out array of 5-bit values.  Shim here.
def u5_to_bitarray(arr):
    ret = bitstring.BitArray()
    for a in arr:
        ret += bitstring.pack("uint:5", a)
    return ret

def bitarray_to_u5(barr):
    assert barr.len % 5 == 0
    ret = []
    s = bitstring.ConstBitStream(barr)
    while s.pos != s.len:
        ret.append(s.read(5).uint)
    return ret

def encode_fallback(fallback, currency):
    """ Encode all supported fallback addresses.
    """
    if currency == 'mona' or currency == 'tmona':
        fbhrp, witness = bech32_decode(fallback)
        if fbhrp:
            if fbhrp != currency:
                raise ValueError("Not a bech32 address for this currency")
            wver = witness[0]
            if wver > 16:
                raise ValueError("Invalid witness version {}".format(witness[0]))
            wprog = u5_to_bitarray(witness[1:])
        else:
            addr = base58.b58decode_check(fallback)
            if is_p2pkh(currency, addr[0]):
                wver = 17
            elif is_p2sh(currency, addr[0]):
                wver = 18
            else:
                raise ValueError("Unknown address type for {}".format(currency))
            wprog = addr[1:]
        return tagged('f', bitstring.pack("uint:5", wver) + wprog)
    else:
        raise NotImplementedError("Support for currency {} not implemented".format(currency))

def parse_fallback(fallback, currency):
    if currency == 'mona' or currency == 'tmona':
        wver = fallback[0:5].uint
        if wver == 17:
            addr=base58.b58encode_check(bytes([base58_prefix_map[currency][0]])
                                        + fallback[5:].tobytes())
        elif wver == 18:
            addr=base58.b58encode_check(bytes([base58_prefix_map[currency][1]])
                                        + fallback[5:].tobytes())
        elif wver <= 16:
            addr=bech32_encode(currency, bitarray_to_u5(fallback))
        else:
            return None
    else:
        addr=fallback.tobytes()
    return addr


# Map of classical and witness address prefixes
base58_prefix_map = {
    'mona' : (50, 55),
    'tmona' : (111, 117)
}

def is_p2pkh(currency, prefix):
    return prefix == base58_prefix_map[currency][0]

def is_p2sh(currency, prefix):
    return prefix == base58_prefix_map[currency][1]

# Tagged field containing BitArray
def tagged(char, l):
    # Tagged fields need to be zero-padded to 5 bits.
    while l.len % 5 != 0:
        l.append('0b0')
    return bitstring.pack("uint:5, uint:5, uint:5",
                          CHARSET.find(char),
                          (l.len / 5) / 32, (l.len / 5) % 32) + l

# Tagged field containing bytes
def tagged_bytes(char, l):
    return tagged(char, bitstring.BitArray(l))

# Discard trailing bits, convert to bytes.
def trim_to_bytes(barr):
    # Adds a byte if necessary.
    b = barr.tobytes()
    if barr.len % 8 != 0:
        return b[:-1]
    return b

# Try to pull out tagged data: returns tag, tagged data and remainder.
def pull_tagged(stream):
    tag = stream.read(5).uint
    length = stream.read(5).uint * 32 + stream.read(5).uint
    return (CHARSET[tag], stream.read(length * 5), stream)

# from electrum
def list_enabled_bits(x: int) -> Sequence[int]:
    """e.g. 77 (0b1001101) --> (0, 2, 3, 6)"""
    binary = bin(x)[2:]
    rev_bin = reversed(binary)
    return tuple(i for i, b in enumerate(rev_bin) if b == '1')

class LnFeatureContexts(enum.Flag):
    INIT = enum.auto()
    NODE_ANN = enum.auto()
    CHAN_ANN_AS_IS = enum.auto()
    CHAN_ANN_ALWAYS_ODD = enum.auto()
    CHAN_ANN_ALWAYS_EVEN = enum.auto()
    INVOICE = enum.auto()

LNFC = LnFeatureContexts

_ln_feature_direct_dependencies = defaultdict(set)  # type: Dict[LnFeatures, Set[LnFeatures]]
_ln_feature_contexts = {}  # type: Dict[LnFeatures, LnFeatureContexts]

class LnFeatures(IntFlag):
    OPTION_DATA_LOSS_PROTECT_REQ = 1 << 0
    OPTION_DATA_LOSS_PROTECT_OPT = 1 << 1
    _ln_feature_contexts[OPTION_DATA_LOSS_PROTECT_OPT] = (LNFC.INIT | LnFeatureContexts.NODE_ANN)
    _ln_feature_contexts[OPTION_DATA_LOSS_PROTECT_REQ] = (LNFC.INIT | LnFeatureContexts.NODE_ANN)

    INITIAL_ROUTING_SYNC = 1 << 3
    _ln_feature_contexts[INITIAL_ROUTING_SYNC] = LNFC.INIT

    OPTION_UPFRONT_SHUTDOWN_SCRIPT_REQ = 1 << 4
    OPTION_UPFRONT_SHUTDOWN_SCRIPT_OPT = 1 << 5
    _ln_feature_contexts[OPTION_UPFRONT_SHUTDOWN_SCRIPT_OPT] = (LNFC.INIT | LNFC.NODE_ANN)
    _ln_feature_contexts[OPTION_UPFRONT_SHUTDOWN_SCRIPT_REQ] = (LNFC.INIT | LNFC.NODE_ANN)

    GOSSIP_QUERIES_REQ = 1 << 6
    GOSSIP_QUERIES_OPT = 1 << 7
    _ln_feature_contexts[GOSSIP_QUERIES_OPT] = (LNFC.INIT | LNFC.NODE_ANN)
    _ln_feature_contexts[GOSSIP_QUERIES_REQ] = (LNFC.INIT | LNFC.NODE_ANN)

    VAR_ONION_REQ = 1 << 8
    VAR_ONION_OPT = 1 << 9
    _ln_feature_contexts[VAR_ONION_OPT] = (LNFC.INIT | LNFC.NODE_ANN | LNFC.INVOICE)
    _ln_feature_contexts[VAR_ONION_REQ] = (LNFC.INIT | LNFC.NODE_ANN | LNFC.INVOICE)

    GOSSIP_QUERIES_EX_REQ = 1 << 10
    GOSSIP_QUERIES_EX_OPT = 1 << 11
    _ln_feature_direct_dependencies[GOSSIP_QUERIES_EX_OPT] = {GOSSIP_QUERIES_OPT}
    _ln_feature_contexts[GOSSIP_QUERIES_EX_OPT] = (LNFC.INIT | LNFC.NODE_ANN)
    _ln_feature_contexts[GOSSIP_QUERIES_EX_REQ] = (LNFC.INIT | LNFC.NODE_ANN)

    OPTION_STATIC_REMOTEKEY_REQ = 1 << 12
    OPTION_STATIC_REMOTEKEY_OPT = 1 << 13
    _ln_feature_contexts[OPTION_STATIC_REMOTEKEY_OPT] = (LNFC.INIT | LNFC.NODE_ANN)
    _ln_feature_contexts[OPTION_STATIC_REMOTEKEY_REQ] = (LNFC.INIT | LNFC.NODE_ANN)

    PAYMENT_SECRET_REQ = 1 << 14
    PAYMENT_SECRET_OPT = 1 << 15
    _ln_feature_direct_dependencies[PAYMENT_SECRET_OPT] = {VAR_ONION_OPT}
    _ln_feature_contexts[PAYMENT_SECRET_OPT] = (LNFC.INIT | LNFC.NODE_ANN | LNFC.INVOICE)
    _ln_feature_contexts[PAYMENT_SECRET_REQ] = (LNFC.INIT | LNFC.NODE_ANN | LNFC.INVOICE)

    BASIC_MPP_REQ = 1 << 16
    BASIC_MPP_OPT = 1 << 17
    _ln_feature_direct_dependencies[BASIC_MPP_OPT] = {PAYMENT_SECRET_OPT}
    _ln_feature_contexts[BASIC_MPP_OPT] = (LNFC.INIT | LNFC.NODE_ANN | LNFC.INVOICE)
    _ln_feature_contexts[BASIC_MPP_REQ] = (LNFC.INIT | LNFC.NODE_ANN | LNFC.INVOICE)

    OPTION_SUPPORT_LARGE_CHANNEL_REQ = 1 << 18
    OPTION_SUPPORT_LARGE_CHANNEL_OPT = 1 << 19
    _ln_feature_contexts[OPTION_SUPPORT_LARGE_CHANNEL_OPT] = (LNFC.INIT | LNFC.NODE_ANN | LNFC.CHAN_ANN_ALWAYS_EVEN)
    _ln_feature_contexts[OPTION_SUPPORT_LARGE_CHANNEL_REQ] = (LNFC.INIT | LNFC.NODE_ANN | LNFC.CHAN_ANN_ALWAYS_EVEN)

    def validate_transitive_dependecies(self) -> bool:
        # for all even bit set, set corresponding odd bit:
        features = self  # copy
        flags = list_enabled_bits(features)
        for flag in flags:
            if flag % 2 == 0:
                features |= 1 << get_ln_flag_pair_of_bit(flag)
        # Check dependencies. We only check that the direct dependencies of each flag set
        # are satisfied: this implies that transitive dependencies are also satisfied.
        flags = list_enabled_bits(features)
        for flag in flags:
            for dependency in _ln_feature_direct_dependencies[1 << flag]:
                if not (dependency & features):
                    return False
        return True

    def for_init_message(self) -> 'LnFeatures':
        features = LnFeatures(0)
        for flag in list_enabled_bits(self):
            if LnFeatureContexts.INIT & _ln_feature_contexts[1 << flag]:
                features |= (1 << flag)
        return features

    def for_node_announcement(self) -> 'LnFeatures':
        features = LnFeatures(0)
        for flag in list_enabled_bits(self):
            if LnFeatureContexts.NODE_ANN & _ln_feature_contexts[1 << flag]:
                features |= (1 << flag)
        return features

    def for_invoice(self) -> 'LnFeatures':
        features = LnFeatures(0)
        for flag in list_enabled_bits(self):
            if LnFeatureContexts.INVOICE & _ln_feature_contexts[1 << flag]:
                features |= (1 << flag)
        return features

    def for_channel_announcement(self) -> 'LnFeatures':
        features = LnFeatures(0)
        for flag in list_enabled_bits(self):
            ctxs = _ln_feature_contexts[1 << flag]
            if LnFeatureContexts.CHAN_ANN_AS_IS & ctxs:
                features |= (1 << flag)
            elif LnFeatureContexts.CHAN_ANN_ALWAYS_EVEN & ctxs:
                if flag % 2 == 0:
                    features |= (1 << flag)
            elif LnFeatureContexts.CHAN_ANN_ALWAYS_ODD & ctxs:
                if flag % 2 == 0:
                    flag = get_ln_flag_pair_of_bit(flag)
                features |= (1 << flag)
        return features

def validate_features(features: int) -> None:
    """Raises IncompatibleOrInsaneFeatures if
    - a mandatory feature is listed that we don't recognize, or
    - the features are inconsistent
    """
    features = LnFeatures(features)
    enabled_features = list_enabled_bits(features)
    for fbit in enabled_features:
        if (1 << fbit) & LN_FEATURES_IMPLEMENTED == 0 and fbit % 2 == 0:
            raise UnknownEvenFeatureBits(fbit)
    if not features.validate_transitive_dependecies():
        raise IncompatibleOrInsaneFeatures("not all transitive dependencies are set")

def trim_to_min_length(bits):
    """Ensures 'bits' have min number of leading zeroes.
    Assumes 'bits' is big-endian, and that it needs to be encoded in 5 bit blocks.
    """
    bits = bits[:]  # copy
    # make sure we can be split into 5 bit blocks
    while bits.len % 5 != 0:
        bits.prepend('0b0')
    # Get minimal length by trimming leading 5 bits at a time.
    while bits.startswith('0b00000'):
        if len(bits) == 5:
            break  # v == 0
        bits = bits[5:]
    return bits

def lnencode(addr, privkey):
    if addr.amount:
        amount = Decimal(str(addr.amount))
        # We can only send down to millisatoshi.
        if amount * 10**12 % 10:
            raise ValueError("Cannot encode {}: too many decimal places".format(
                addr.amount))

        amount = addr.currency + shorten_amount(amount)
    else:
        amount = addr.currency if addr.currency else ''

    hrp = 'ln' + amount

    # Start with the timestamp
    data = bitstring.pack('uint:35', addr.date)

    tags_set = set()

    # Payment hash
    data += tagged_bytes('p', addr.paymenthash)
    tags_set.add('p')


    for k, v in addr.tags:

        # BOLT #11:
        #
        # A writer MUST NOT include more than one `d`, `h`, `n` or `x` fields,
        if k in ('d', 'h', 'n', 'x', 'p', 's'):
            if k in tags_set:
                raise ValueError("Duplicate '{}' tag".format(k))

        if k == 'r':
            route = bitstring.BitArray()
            for step in v:
                pubkey, channel, feebase, feerate, cltv = step
                route.append(bitstring.BitArray(pubkey) + bitstring.BitArray(channel) + bitstring.pack('intbe:32', feebase) + bitstring.pack('intbe:32', feerate) + bitstring.pack('intbe:16', cltv))
            data += tagged('r', route)
        elif k == 'f':
            data += encode_fallback(v, addr.currency)
        elif k == 'd':
            data += tagged_bytes('d', v.encode())
        elif k == 'x':
            expirybits = bitstring.pack('intbe:64', v)
            expirybits = trim_to_min_length(expirybits)
            data += tagged('x', expirybits)
        elif k == 'h':
            data += tagged_bytes('h', hashlib.sha256(v.encode('utf-8')).digest())
        elif k == 'n':
            data += tagged_bytes('n', v)
        elif k == 'c':
            finalcltvbits = bitstring.pack('intbe:64', v)
            finalcltvbits = trim_to_min_length(finalcltvbits)
            data += tagged('c', finalcltvbits)
        elif k == '9':
            if v == 0:
                continue
            feature_bits = bitstring.BitArray(uint=v, length=v.bit_length())
            feature_bits = trim_to_min_length(feature_bits)
            data += tagged('9', feature_bits)
        else:
            # FIXME: Support unknown tags?
            raise ValueError("Unknown tag {}".format(k))

        tags_set.add(k)

    # Payment secret
    if addr.paymentsecret is not None:
        data += tagged_bytes('s', addr.paymentsecret)
        tags_set.add('s')

    print(data)
    # BOLT #11:
    #
    # A writer MUST include either a `d` or `h` field, and MUST NOT include
    # both.
    if 'd' in tags_set and 'h' in tags_set:
        raise ValueError("Cannot include both 'd' and 'h'")
    if not 'd' in tags_set and not 'h' in tags_set:
        raise ValueError("Must include either 'd' or 'h'")
    
    # We actually sign the hrp, then data (padded to 8 bits with zeroes).
    privkey = secp256k1.PrivateKey(bytes(unhexlify(privkey)))
    sig = privkey.ecdsa_sign_recoverable(bytearray([ord(c) for c in hrp]) + data.tobytes())
    # This doesn't actually serialize, but returns a pair of values :(
    sig, recid = privkey.ecdsa_recoverable_serialize(sig)
    data += bytes(sig) + bytes([recid])

    return bech32_encode(hrp, bitarray_to_u5(data))

class LnAddr(object):
    def __init__(self, paymenthash: bytes = None, amount=None, currency='mona', tags=None, date=None, paymentsecret: bytes = None):
        self.date = int(time.time()) if not date else int(date)
        self.tags = [] if not tags else tags
        self.unknown_tags = []
        self.paymenthash=paymenthash
        self.paymentsecret = paymentsecret
        self.signature = None
        self.pubkey = None
        self.currency = currency
        self.amount = amount
        self.min_final_cltv_expiry = 9

    def __str__(self):
        return "LnAddr[{}, amount={}{} tags=[{}]]".format(
            hexlify(self.pubkey.serialize()).decode('utf-8'),
            self.amount, self.currency,
            ", ".join([k + '=' + str(v) for k, v in self.tags])
        )

def lndecode(a, verbose=False):
    hrp, data = bech32_decode(a)
    if not hrp:
        raise ValueError("Bad bech32 checksum")

    # BOLT #11:
    #
    # A reader MUST fail if it does not understand the `prefix`.
    if not hrp.startswith('ln'):
        raise ValueError("Does not start with ln")

    data = u5_to_bitarray(data);

    # Final signature 65 bytes, split it off.
    if len(data) < 65*8:
        raise ValueError("Too short to contain signature")
    sigdecoded = data[-65*8:].tobytes()
    data = bitstring.ConstBitStream(data[:-65*8])

    addr = LnAddr()
    addr.pubkey = None

    m = re.search("[^\d]+", hrp[2:])
    if m:
        addr.currency = m.group(0)
        amountstr = hrp[2+m.end():]
        # BOLT #11:
        #
        # A reader SHOULD indicate if amount is unspecified, otherwise it MUST
        # multiply `amount` by the `multiplier` value (if any) to derive the
        # amount required for payment.
        if amountstr != '':
            addr.amount = unshorten_amount(amountstr)

    addr.date = data.read(35).uint

    while data.pos != data.len:
        tag, tagdata, data = pull_tagged(data)

        # BOLT #11:
        #
        # A reader MUST skip over unknown fields, an `f` field with unknown
        # `version`, or a `p`, `h`, or `n` field which does not have
        # `data_length` 52, 52, or 53 respectively.
        data_length = len(tagdata) / 5
        
        if tag == 'r':
            # BOLT #11:
            #
            # * `r` (3): `data_length` variable.  One or more entries
            # containing extra routing information for a private route;
            # there may be more than one `r` field, too.
            #    * `pubkey` (264 bits)
            #    * `short_channel_id` (64 bits)
            #    * `feebase` (32 bits, big-endian)
            #    * `feerate` (32 bits, big-endian)
            #    * `cltv_expiry_delta` (16 bits, big-endian)
            route=[]
            s = bitstring.ConstBitStream(tagdata)
            while s.pos + 264 + 64 + 32 + 32 + 16 < s.len:
                route.append((s.read(264).tobytes(),
                              s.read(64).tobytes(),
                              s.read(32).intbe,
                              s.read(32).intbe,
                              s.read(16).intbe))
            addr.tags.append(('r',route))                
        elif tag == 'f':
            fallback = parse_fallback(tagdata, addr.currency)
            if fallback:
                addr.tags.append(('f', fallback))
            else:
                # Incorrect version.
                addr.unknown_tags.append((tag, tagdata))
                continue

        elif tag == 'd':
            addr.tags.append(('d', trim_to_bytes(tagdata).decode('utf-8')))

        elif tag == 'h':
            if data_length != 52:
                addr.unknown_tags.append((tag, tagdata))
                continue
            addr.tags.append(('h', trim_to_bytes(tagdata)))

        elif tag == 'x':
            addr.tags.append(('x', tagdata.uint))

        elif tag == 'p':
            if data_length != 52:
                addr.unknown_tags.append((tag, tagdata))
                continue
            addr.paymenthash = trim_to_bytes(tagdata)

        elif tag == 's':
            if data_length != 52:
                addr.unknown_tags.append((tag, tagdata))
                continue
            addr.paymentsecret = trim_to_bytes(tagdata)

        elif tag == 'n':
            if data_length != 53:
                addr.unknown_tags.append((tag, tagdata))
                continue
            addr.pubkey = secp256k1.PublicKey(flags=secp256k1.ALL_FLAGS)
            addr.pubkey.deserialize(trim_to_bytes(tagdata))

        elif tag == 'c':
            addr.min_final_cltv_expiry = tagdata.int

        elif tag == '9':
            features = tagdata.uint
            addr.tags.append(('9', features))
            self.validate_features(features)

        else:
            addr.unknown_tags.append((tag, tagdata))

    if verbose:
        print('hex of signature data (32 byte r, 32 byte s): {}'
              .format(hexlify(sigdecoded[0:64])))
        print('recovery flag: {}'.format(sigdecoded[64]))
        print('hex of data for signing: {}'
              .format(hexlify(bytearray([ord(c) for c in hrp])
                              + data.tobytes())))
        print('SHA256 of above: {}'.format(hashlib.sha256(bytearray([ord(c) for c in hrp]) + data.tobytes()).hexdigest()))

    # BOLT #11:
    #
    # A reader MUST check that the `signature` is valid (see the `n` tagged
    # field specified below).
    if addr.pubkey: # Specified by `n`
        # BOLT #11:
        #
        # A reader MUST use the `n` field to validate the signature instead of
        # performing signature recovery if a valid `n` field is provided.
        addr.signature = addr.pubkey.ecdsa_deserialize_compact(sigdecoded[0:65])
        if not addr.pubkey.ecdsa_verify(bytearray([ord(c) for c in hrp]) + data.tobytes(), addr.signature):
            raise ValueError('Invalid signature')
    else: # Recover pubkey from signature.
        addr.pubkey = secp256k1.PublicKey(flags=secp256k1.ALL_FLAGS)
        addr.signature = addr.pubkey.ecdsa_recoverable_deserialize(
            sigdecoded[0:64], sigdecoded[64])
        addr.pubkey.public_key = addr.pubkey.ecdsa_recover(
            bytearray([ord(c) for c in hrp]) + data.tobytes(), addr.signature)

    return addr
