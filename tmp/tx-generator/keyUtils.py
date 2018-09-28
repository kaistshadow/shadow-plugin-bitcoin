# https://pypi.python.org/pypi/ecdsa/0.10
import ecdsa
import ecdsa.der
import ecdsa.util
import hashlib
import unittest
import random
import re
import struct

import utils
from binascii import hexlify

# https://en.bitcoin.it/wiki/Wallet_import_format
def privateKeyToWif(key_hex):    
    return utils.base58CheckEncode(0x80, key_hex.decode('hex'))

def privateKeyToPublicKey(s, compressed=False):
    sk = ecdsa.SigningKey.from_string(s.decode('hex'), curve=ecdsa.SECP256k1)
    vk = sk.verifying_key
    # return ('\04' + sk.verifying_key.to_string()).encode('hex')

    if compressed:
        from ecdsa.util import number_to_string
        order = vk.pubkey.order
        # print "order", order
        x_str = number_to_string(vk.pubkey.point.x(), order).encode('hex')
        # print "x_str", x_str 
        sign = '02' if vk.pubkey.point.y() % 2 == 0 else '03'
        # print "sign", sign 
        return (sign+x_str)
    else:
        return ('\04' + vk.to_string()).encode('hex')

    # order = ecdsa.SigningKey.from_string(s.decode('hex'), curve=ecdsa.SECP256k1).curve.generator.order()
    # p = ecdsa.SigningKey.from_string(s.decode('hex'), curve=ecdsa.SECP256k1).verifying_key.pubkey.point
    # x_str = ecdsa.util.number_to_string(p.x(), order)
    # y_str = ecdsa.util.number_to_string(p.y(), order)
    # compressed = hexlify(bytes(chr(2 + (p.y() & 1))) + x_str).decode('ascii')
    # uncompressed = hexlify(bytes(chr(4)) + x_str + y_str).decode('ascii')
    
def pow_mod(x, y, z):
    "Calculate (x ** y) % z efficiently."
    number = 1
    while y:
        if y & 1:
            number = number * x % z
        y >>= 1
        x = x * x % z
    return number

def getFullPubKeyFromCompressed(compressed_key):
    y_parity = int(compressed_key[:2]) - 2
    if y_parity == 4:
        return compressed_key
    p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
    x = int(compressed_key[2:], 16)
    a = (pow_mod(x, 3, p) + 7) % p
    y = pow_mod(a, (p+1)//4, p)
    if y % 2 != y_parity:
        y = -y % p
    uncompressed_key = '04{:x}{:x}'.format(x, y)
    return uncompressed_key

def pubKeyToAddr(s):
    ripemd160 = hashlib.new('ripemd160')
    ripemd160.update(hashlib.sha256(s.decode('hex')).digest())
    return utils.base58CheckEncode(0, ripemd160.digest())

def keyToAddr(s):
    return pubKeyToAddr(privateKeyToPublicKey(s, True))


def addrHashToScriptPubKey(b58str):
    print len(b58str)
    assert(len(b58str) == 34)
    # 76     A9      14 (20 bytes)                                 88             AC
    return '76a914' + utils.base58CheckDecode(b58str).encode('hex') + '88ac'

def wifToPrivateKey(s):
    if s[0] == "K" or s[0] == "L" or s[0] == "c":
        b = utils.base58CheckDecode(s, pk_for_compressed=True)
        print "aa"
    else:
        b = utils.base58CheckDecode(s)
    return b.encode('hex')


# Input is a hex-encoded, DER-encoded signature
# Output is a 64-byte hex-encoded signature
def derSigToHexSig(s):
    s, junk = ecdsa.der.remove_sequence(s.decode('hex'))
    if junk != '':
        print 'JUNK', junk.encode('hex')
    assert(junk == '')
    x, s = ecdsa.der.remove_integer(s)
    y, s = ecdsa.der.remove_integer(s)
    return '%064x%064x' % (x, y)
