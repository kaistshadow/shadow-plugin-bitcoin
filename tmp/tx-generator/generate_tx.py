#!/usr/bin/python
import ecdsa
import ecdsa.der
import ecdsa.util
import hashlib
import random

import utils
import keyUtils
import struct

import socket
import time

import binascii, hmac

from bitcoin import *

#### pybitcointools code start
P = 2**256-2**32-2**9-2**8-2**7-2**6-2**4-1
N = 115792089237316195423570985008687907852837564279074904382605163141518161494337
A = 0
Gx = 55066263022277343669578718895168534326250603453777594175500187360389116729240
Gy = 32670510020758816978083085130507043184471273380659243275938904335757337482424
G = (Gx,Gy)

def isinf(p): return p[0] == 0 and p[1] == 0

def inv(a,n):
  lm, hm = 1,0
  low, high = a%n,n
  while low > 1:
    r = high/low
    nm, new = hm-lm*r, high-low*r
    lm, low, hm, high = nm, new, lm, low
  return lm % n

def get_code_string(base):
   if base == 2: return '01'
   elif base == 10: return '0123456789'
   elif base == 16: return "0123456789abcdef"
   elif base == 58: return "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
   elif base == 256: return ''.join([chr(x) for x in range(256)])
   else: raise ValueError("Invalid base!")

def decode(string,base):
   base = int(base)
   code_string = get_code_string(base)
   result = 0
   if base == 16: string = string.lower()
   while len(string) > 0:
      result *= base
      result += code_string.find(string[0])
      string = string[1:]
   return result

def encode(val,base,minlen=0):
   base, minlen = int(base), int(minlen)
   code_string = get_code_string(base)
   result = ""   
   while val > 0:
      result = code_string[val % base] + result
      val /= base
   if len(result) < minlen:
      result = code_string[0]*(minlen-len(result))+result
   return result

def changebase(string,frm,to,minlen=0):
   return encode(decode(string,frm),to,minlen)

def hash_to_int(x):
    if len(x) in [40,64]: return decode(x,16)
    else: return decode(x,256)

# https://tools.ietf.org/html/rfc6979#section-3.2
def deterministic_generate_k(msghash,priv):
    v = '\x01' * 32
    k = '\x00' * 32
    priv = encode_privkey(priv,'bin')
    msghash = encode(hash_to_int(msghash),256,32)
    k = hmac.new(k, v+'\x00'+priv+msghash, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()
    k = hmac.new(k, v+'\x01'+priv+msghash, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()
    return decode(hmac.new(k, v, hashlib.sha256).digest(),256)

def base10_add(a,b):
    if isinf(a): return b[0],b[1]
    if isinf(b): return a[0],a[1]
    if a[0] == b[0]: 
        if a[1] == b[1]: 
            return base10_double(a[0],a[1])
        else: 
            return (0,0)
    m = ((b[1]-a[1]) * inv(b[0]-a[0],P)) % P
    x = (m*m-a[0]-b[0]) % P
    y = (m*(a[0]-x)-a[1]) % P
    return (x,y)
    
def base10_double(a):
    if isinf(a): return (0,0)
    m = ((3*a[0]*a[0]+A)*inv(2*a[1],P)) % P
    x = (m*m-2*a[0]) % P
    y = (m*(a[0]-x)-a[1]) % P
    return (x,y)

def base10_multiply(a,n):
    if isinf(a) or n == 0: return (0,0)
    if n == 1: return a
    if n < 0 or n >= N: return base10_multiply(a,n%N)
    if (n%2) == 0: return base10_double(base10_multiply(a,n/2))
    if (n%2) == 1: return base10_add(base10_double(base10_multiply(a,n/2)),a)

def bin_to_b58check(inp,magicbyte=0):
    inp_fmtd = chr(int(magicbyte)) + inp
    leadingzbytes = len(re.match('^\x00*',inp_fmtd).group(0))
    checksum = bin_dbl_sha256(inp_fmtd)[:4]
    return '1' * leadingzbytes + changebase(inp_fmtd+checksum,256,58)

def bin_dbl_sha256(string):
    return hashlib.sha256(hashlib.sha256(string).digest()).digest()

def get_privkey_format(priv):
    if isinstance(priv,(int,long)): return 'decimal'
    elif len(priv) == 32: return 'bin'
    elif len(priv) == 33: return 'bin_compressed'
    elif len(priv) == 64: return 'hex'
    elif len(priv) == 66: return 'hex_compressed'
    else:
        bin_p = b58check_to_bin(priv)
        if len(bin_p) == 32: return 'wif'
        elif len(bin_p) == 33: return 'wif_compressed'
        else: raise Exception("WIF does not represent privkey")

def encode_privkey(priv,formt):
    if not isinstance(priv,(int,long)):
        return encode_privkey(decode_privkey(priv),formt)
    if formt == 'decimal': return priv
    elif formt == 'bin': return encode(priv,256,32)
    elif formt == 'bin_compressed': return encode(priv,256,32)+'\x01'
    elif formt == 'hex': return encode(priv,16,64)
    elif formt == 'hex_compressed': return encode(priv,16,64)+'01'
    elif formt == 'wif': return bin_to_b58check(encode(priv,256,32),128)
    elif formt == 'wif_compressed': return bin_to_b58check(encode(priv,256,32)+'\x01',128)
    else: raise Exception("Invalid format!")

def decode_privkey(priv,formt=None):
    if not formt: formt = get_privkey_format(priv)
    if formt == 'decimal': return priv
    elif formt == 'bin': return decode(priv,256)
    elif formt == 'bin_compressed': return decode(priv[:32],256)
    elif formt == 'hex': return decode(priv,16)
    elif formt == 'hex_compressed': return decode(priv[:64],16)
    else:
        bin_p = b58check_to_bin(priv)
        if len(bin_p) == 32: return decode(bin_p,256)
        elif len(bin_p) == 33: return decode(bin_p[:32],256)
        else: raise Exception("WIF does not represent privkey")

def ecdsa_raw_sign(msghash,priv):
    z = hash_to_int(msghash)
    k = deterministic_generate_k(msghash,priv)

    r,y = base10_multiply(G,k)
    s = inv(k,N) * (z + r*decode_privkey(priv)) % N

    return 27+(y%2),r,s

def der_encode_sig(*args):
    """Takes ([vbyte], r, s) as ints and returns hex der encode sig"""
    if len(args) == 3:
        v,r,s = args
    elif len(args) == 2:
        r,s = args
    elif len(args) == 1 and isinstance(args[0], tuple):
        return der_encode_sig(*args[0])
    b1, b2 = encode(r, 256), encode(s, 256)
    if len(b1) and changebase(b1[0], 256, 16, 1) in "89abcdef":# add null bytes if interpreted as negative number
        b1 = b'\x00' + b1
    if len(b2) and ord(b2[0]) & 0x80:
        b2 = b'\x00' + b2
    left  = b'\x02' + encode(len(b1), 256, 1) + b1
    right = b'\x02' + encode(len(b2), 256, 1) + b2
    sighex = binascii.hexlify(b'\x30' + encode(len(left+right), 256, 1) + left + right)
    #assert is_bip66(sighex)
    return sighex


def ecdsa_tx_sign(txhash, priv):
    """Returns DER sig for rawtx w/ hashcode appended"""
    rawsig = ecdsa_raw_sign(txhash, priv)
    return der_encode_sig(*rawsig)

def pybitcointools_sig(txhash, sk):
    return ecdsa_tx_sign(txhash, sk)

def is_bip66(sig):
    """Checks hex DER sig for BIP66 compliance"""
    #https://raw.githubusercontent.com/bitcoin/bips/master/bip-0066.mediawiki
    #0x30  [total-len]  0x02  [R-len]  [R]  0x02  [S-len]  [S]  [sighash]
    # sig = bytearray.fromhex(sig) if (isinstance(sig, string_types) and
    #                                  RE_HEX_CHARS.match(sig)) else bytearray(sig)
    sig = bytearray.fromhex(sig)

    if sig[1] == len(sig)-2: 
        sig.extend(b"\1")# add SIGHASH for BIP66 check

    if len(sig) < 9 or len(sig) > 73: return False
    if (sig[0] != 0x30): return False
    if (sig[1] != len(sig)-3): return False
    rlen = sig[3]
    if (5+rlen >= len(sig)): return False
    slen = sig[5+rlen]
    if (rlen + slen + 7 != len(sig)): return False
    if (sig[2] != 0x02): return False
    if (rlen == 0): return False
    if (sig[4] & 0x80): return False
    if (rlen > 1 and (sig[4] == 0) and not (sig[5] & 0x80)): return False
    if (sig[4+rlen] != 0x02): return False
    if (slen == 0): return False
    if (sig[rlen+6] & 0x80): return False
    if (slen > 1 and (sig[6+rlen] == 0) and not (sig[7+rlen] & 0x80)): return False
    
    return True

#### pybitcointools code end

#### petertodd/python-bitcoinlib code start
def IsLowDERSignature(sig):
    """
    Loosely correlates with IsLowDERSignature() from script/interpreter.cpp
    Verifies that the S value in a DER signature is the lowest possible value.
    Used by BIP62 malleability fixes.
    """
    length_r = sig[3]
    if isinstance(length_r, str):
        length_r = int(struct.unpack('B', length_r)[0])
    length_s = sig[5 + length_r]
    if isinstance(length_s, str):
        length_s = int(struct.unpack('B', length_s)[0])
    s_val = list(struct.unpack(str(length_s) + 'B', sig[6 + length_r:6 + length_r + length_s]))

    # If the S value is above the order of the curve divided by two, its
    # complement modulo the order could have been used instead, which is
    # one byte shorter when encoded correctly.
    max_mod_half_order = [
      0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0x5d,0x57,0x6e,0x73,0x57,0xa4,0x50,0x1d,
      0xdf,0xe9,0x2f,0x46,0x68,0x1b,0x20,0xa0]

    return CompareBigEndian(s_val, [0]) > 0 and \
      CompareBigEndian(s_val, max_mod_half_order) <= 0

def CompareBigEndian(c1, c2):
    """
    Loosely matches CompareBigEndian() from eccryptoverify.cpp
    Compares two arrays of bytes, and returns a negative value if the first is
    less than the second, 0 if they're equal, and a positive value if the
    first is greater than the second.
    """
    c1 = list(c1)
    c2 = list(c2)

    # Adjust starting positions until remaining lengths of the two arrays match
    while len(c1) > len(c2):
        if c1.pop(0) > 0:
            return 1
    while len(c2) > len(c1):
        if c2.pop(0) > 0:
            return -1

    while len(c1) > 0:
        diff = c1.pop(0) - c2.pop(0)
        if diff != 0:
            return diff

    return 0

#### petertodd/python-bitcoinlib code end



# Returns [first, sig, pub, rest]
def parseTxn(txn):
    first = txn[0:41*2]
    scriptLen = int(txn[41*2:42*2], 16)
    script = txn[42*2:42*2+2*scriptLen]
    sigLen = int(script[0:2], 16)
    sig = script[2:2+sigLen*2]
    pubLen = int(script[2+sigLen*2:2+sigLen*2+2], 16)
    pub = script[2+sigLen*2+2:]

    assert(len(pub) == pubLen*2)
    rest = txn[42*2+2*scriptLen:]

    # first = txn[0:43*2]
    # scriptLen = int(txn[43*2:44*2], 16)
    # script = txn[44*2:44*2+2*scriptLen]
    # sigLen = int(script[0:2], 16)
    # sig = script[2:2+sigLen*2]
    # pubLen = int(script[2+sigLen*2:2+sigLen*2+2], 16)
    # pub = script[2+sigLen*2+2:]
            
    # assert(len(pub) == pubLen*2)
    # rest = txn[44*2+2*scriptLen:]
    return [first, sig, pub, rest]   

# Substitutes the scriptPubKey into the transaction, appends SIGN_ALL to make the version
# of the transaction that can be signed
def getSignableTxn(parsed):
    first, sig, pub, rest = parsed
    inputAddr = utils.base58CheckDecode(keyUtils.pubKeyToAddr(pub))
    return first + "1976a914" + inputAddr.encode('hex') + "88ac" + rest + "01000000"

###############
# Makes a transaction from the inputs
# outputs is a list of [redemptionSatoshis, outputScript]
def makeRawTransaction(outputTransactionHash, sourceIndex, scriptSig, outputs):
    def makeOutput(data):
        redemptionSatoshis, outputScript = data
        return (struct.pack("<Q", redemptionSatoshis).encode('hex') +
        '%02x' % len(outputScript.decode('hex')) + outputScript)
    formattedOutputs = ''.join(map(makeOutput, outputs))
    return (
        # "01000000" + # 4 bytes version
        "02000000" + # 4 bytes version
        # "0001" + # segwit marker, flag
        "01" + # varint for number of inputs
        outputTransactionHash.decode('hex')[::-1].encode('hex') + # reverse outputTransactionHash
        struct.pack('<I', sourceIndex).encode('hex') +
        '%02x' % len(scriptSig.decode('hex')) + scriptSig +
        "ffffffff" + # sequence
        "%02x" % len(outputs) + # number of outputs
        formattedOutputs +
        # "0100" + # segwit witness
        "00000000" # lockTime
        )

def makeSignedTransaction(privateKey, outputTransactionHash, sourceIndex, scriptPubKey, outputs):
    myTxn_forSig = (makeRawTransaction(outputTransactionHash, sourceIndex, scriptPubKey, outputs)
         + "01000000") # hash code

    print "priv", privateKey
    print "tx", myTxn_forSig

    # signing with ecdsa module
    s256 = hashlib.sha256(hashlib.sha256(myTxn_forSig.decode('hex')).digest()).digest()
    sk = ecdsa.SigningKey.from_string(privateKey.decode('hex'), curve=ecdsa.SECP256k1)
    while True:
        sig = sk.sign_digest(s256, sigencode=ecdsa.util.sigencode_der)
        print is_bip66(binascii.hexlify(sig))
        if IsLowDERSignature(bytearray.fromhex(binascii.hexlify(sig))):
            break
    sig = sig + '\01'
    # sig = pybitcointools_sig(s256, privateKey) + '01'
    # sig = sig.decode('hex')
    print "sig",len(sig),[binascii.hexlify(sig)]
    pubKey = keyUtils.privateKeyToPublicKey(privateKey, True)
    scriptSig = utils.varstr(sig).encode('hex') + utils.varstr(pubKey.decode('hex')).encode('hex')
    signed_txn = makeRawTransaction(outputTransactionHash, sourceIndex, scriptSig, outputs)
    print "signed_txn", signed_txn
    verifyTxnSignature(signed_txn)
    return signed_txn

def verifyTxnSignature(txn):                    
    parsed = parseTxn(txn)      
    signableTxn = getSignableTxn(parsed)
    hashToSign = hashlib.sha256(hashlib.sha256(signableTxn.decode('hex')).digest()).digest().encode('hex')
    assert(parsed[1][-2:] == '01') # hashtype
    sig = keyUtils.derSigToHexSig(parsed[1][:-2])
    public_key = parsed[2]
    print "public_key:", public_key
    public_key = keyUtils.getFullPubKeyFromCompressed(public_key)
    print "uncompressed public_key:", public_key
    vk = ecdsa.VerifyingKey.from_string(public_key[2:].decode('hex'), curve=ecdsa.SECP256k1)
    assert(vk.verify_digest(sig.decode('hex'), hashToSign.decode('hex')))

# Warning: this random function is not cryptographically strong and is just for example
private_key = ''.join(['%x' % random.randrange(16) for x in range(0, 64)])
print keyUtils.privateKeyToWif(private_key)
print keyUtils.keyToAddr(private_key)

# privateKey = keyUtils.wifToPrivateKey("5HusYj2b2x4nroApgfvaSfKYZhRbKFH41bVyPooymbC6KfgSXdD") #1MMMM

# signed_txn = makeSignedTransaction(privateKey,
#         "81b4c832d70cb56ff957589752eb4125a4cab78a25a8fc52d6a09e5bd4404d48", # output (prev) transaction hash
#         0, # sourceIndex
#         keyUtils.addrHashToScriptPubKey("1MMMMSUb1piy2ufrSguNUdFmAcvqrQF8M5"),
#         [[91234, #satoshis
#         keyUtils.addrHashToScriptPubKey("1KKKK6N21XKo48zWKuQKXdvSsCf95ibHFa")]]
#         )
# 5HusYj2b2x4nroApgfvaSfKYZhRbKFH41bVyPooymbC6KfgSXdD
# KyFvbums8LKuiVFHRzq2iEUsg7wvXC6fMkJC3PFLjGVQaaN9F1Ln
# cU1UcuA7HRMNoJMamquHLpGMnkDQtwhSt8d3Z2UpGFdx1E4osE7D    
# 5JhuTf9i4fXU8nkonyWDuY8B9vq3LiqQ6vCKH7VpLib4f7hty42

# privateKey = keyUtils.wifToPrivateKey("cU1UcuA7HRMNoJMamquHLpGMnkDQtwhSt8d3Z2UpGFdx1E4osE7D") #1MMMM


# signed_txn = makeSignedTransaction(privateKey,
#         "d70cd6ad2c0a8211b2e22954b3e450a6eaffc4b22d4c35fd760805aae08269a3", # output (prev) transaction hash
#         0, # sourceIndex
#         keyUtils.addrHashToScriptPubKey("mvTpAzhJZQs2FVBR33WdTyYVWakvKNNkLh"),
#         [[100, #satoshis
#         keyUtils.addrHashToScriptPubKey("mtdynEM1zSiSiYQntprR8kep5NEeAqQfco")]]
#         )

# privateKey = keyUtils.wifToPrivateKey("cPk3QpypBp6qvmFgcM6zAQ6ZEw7FHaWwixmgBQ92LE5nzkBE9TKi") #1MMMM
# privateKey = keyUtils.wifToPrivateKey("cRqUESTM4izdtd1p8wsZVYeLwqPP2zgRvBjLnzhUGwK4FwRTncUr") #1MMMM
privateKey = keyUtils.wifToPrivateKey("cVdRR5qP9UW7D3Gf6s6sFKmVzxD7z5cPu6eLtnBP49FPEFrViNvc") #1MMMM

print "privateKey", [privateKey]

# signed_txn = makeSignedTransaction(privateKey,
#         "c0e9e5a845cf222cc78220685fcc295db73608c64bde5d32689ef85e27c72fb5", # output (prev) transaction hash
#         0, # sourceIndex
#         keyUtils.addrHashToScriptPubKey("mxh1vzqUYPT3Udi8c7u2Gu62uj3CnQX5cG"),
#         [[30000000, #satoshis
#           keyUtils.addrHashToScriptPubKey("mrWrZGUatJUdcuF3hcnQSjZVcLaw3g1VAi")], 
#          [550000000, 
#           keyUtils.addrHashToScriptPubKey("mxh1vzqUYPT3Udi8c7u2Gu62uj3CnQX5cG")]]
#         )
signed_txn = makeSignedTransaction(privateKey,
        "73cb8c38c3f0ea7a022bc3d93a78d2b45fc2ed0b44664c17c0225c59f06f490d", # output (prev) transaction hash
        0, # sourceIndex
        keyUtils.addrHashToScriptPubKey("myskqqCrQtvfMDS7nwyrbvm71dCtNzCybU"),
        [[149000000, #satoshis
          keyUtils.addrHashToScriptPubKey("myskqqCrQtvfMDS7nwyrbvm71dCtNzCybU")], 
         [100000000, 
          keyUtils.addrHashToScriptPubKey("n2zpHDvYkFucM7XP8UdYMMKyq4L18UThf2")]]
        )

print signed_txn

verifyTxnSignature(signed_txn)
print 'SIGNED TXN', signed_txn

########## Send to peer
# magic = 0xd9b4bef9 # mainnet
magic = 0xdab5bffa  # testnet

def makeMessage(magic, command, payload):
    # print binascii.hexlify(hashlib.sha256(payload).digest()[0:4])
    checksum = hashlib.sha256(hashlib.sha256(payload).digest()).digest()[0:4]
    # print [checksum, payload]
    return struct.pack('I12sI4s', magic, command, len(payload), checksum) + payload
    # return struct.pack('I', magic) + "version" + 5 *"\00" + struct.pack('I', len(payload)) + checksum + payload + struct.pack('?', True)

def getTxMsg(payload):
  return makeMessage(magic, 'tx', payload)

def getVersionMsg():
    # version = 60002
    version = 70015
    services = 0
    timestamp = int(time.time())
    addr_me = utils.netaddr(socket.inet_aton("127.0.0.1"), 18444)
    addr_you = utils.netaddr(socket.inet_aton("127.0.0.1"), 18444)
    nonce = random.getrandbits(64)
    # sub_version_num = utils.varstr('')
    user_agent_bytes = 0
    start_height = 0
    relay = True

    # print ["addr_me", addr_me]

    payload = struct.pack('<iQQ26s26sQBi?', version, services, timestamp, addr_me,
                          addr_you, nonce, user_agent_bytes, start_height, relay)
    return makeMessage(magic, 'version', payload)

sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
print sock.connect(("143.248.38.189", 18444))
print "connect?"

versionMsg = getVersionMsg()
print [versionMsg]
sock.send(versionMsg)
print [sock.recv(131072)] # receive version
verackMsg = makeMessage(magic, 'verack', "")
sock.send(verackMsg)
print [sock.recv(131072)] # receive version, verack


sock.send(getTxMsg(signed_txn.decode('hex')))

i = 0
try:
    while True:
        sock.settimeout(5)
        print [i, sock.recv(131072)]
        i += 1
except socket.timeout:
    print "sock timeout"

generateMsg = makeMessage(magic, 'generate', "")
sock.send(generateMsg)

i = 0
try:
    while True:
        sock.settimeout(5)
        print [i, sock.recv(131072)]
        i += 1
except socket.timeout:
    print "sock timeout"

# print ["aa", sock.recv(131072)] # receive 
# print ["bb", sock.recv(131072)] # receive 
# print ["cc", sock.recv(131072)] # receive 
# print ["dd", sock.recv(131072)] # receive 
# print ["ee", sock.recv(131072)] # receive 
# print ["ff", sock.recv(131072)] # receive 
# sock.recv(131072)

sock.close()



