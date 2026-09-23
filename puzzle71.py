#!/usr/bin/env python3
"""
Generate Bitcoin (legacy P2PKH) addresses for a range of private keys.

Set START and END below (inclusive). They can be plain integers or hex
strings like "0x1a" / "1a". The script walks every key in the range and
prints a two-column table; optionally it also writes a CSV.

Speed trick: instead of a fresh scalar multiplication per key, it computes
the start point once and then adds G to step to the next key, since
key(k+1)*G = key(k)*G + G. That makes even large ranges quick.

Random mode: set RANDOM_MODE = True to draw keys at random inside [START, END]
instead of scanning in order. Note the add-G shortcut above only works for a
sequential walk, so random mode falls back to a full scalar multiplication per
key (slower per key) and, over a large range, only ever touches a tiny fraction
of it.
"""

import csv
import hashlib
import random

# ======================= CONFIGURE HERE =======================
START       = 0x5EA55B36588996CDA1       # first private key (int or hex str, e.g. "0x1")
END         = 0x5FFFFFFFFFFFFFFFFF       # last private key, inclusive
COMPRESSED  = True     # True -> 33-byte pubkey (bc "1..." compressed); False -> uncompressed
HEX_FULL    = False    # True -> full 32-byte hex (64 chars, how a real key looks); False -> compact hex
CSV_PATH    = ""       # e.g. "addresses.csv" to also save a file; "" to skip

# --- random sampling instead of a sequential walk ---------------------------
RANDOM_MODE  = False   # True -> pick keys at random inside [START, END]; False -> scan in order
RANDOM_COUNT = 0    # random mode: how many keys to output (None or 0 -> run until stopped)
RANDOM_SEED  = None    # random mode: int for a repeatable run, None for fresh randomness each time

# --- optional filter based on runs of consecutive zeros in the key number ----
ZERO_FILTER   = "exclude"  # "off" | "only" (keep keys WITH a zero run) | "exclude" (drop them)
MIN_ZERO_RUN  = 2      # a "zero run" = this many consecutive zeros (2 = "00" appears)
ZERO_BASE     = 16     # 10 -> check decimal digits (like 540000000003033919); 16 -> check hex digits
# ==============================================================


# --- secp256k1 parameters --------------------------------------------------
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A  = 0
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G  = (Gx, Gy)


# --- elliptic-curve math ---------------------------------------------------
def point_add(p1, p2):
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if x1 == x2 and y1 == y2:
        s = (3 * x1 * x1 + A) * pow(2 * y1, -1, P) % P
    else:
        s = (y2 - y1) * pow(x2 - x1, -1, P) % P
    x3 = (s * s - x1 - x2) % P
    y3 = (s * (x1 - x3) - y1) % P
    return (x3, y3)


def scalar_mult(k, point):
    result, addend = None, point
    while k:
        if k & 1:
            result = point_add(result, addend)
        addend = point_add(addend, addend)
        k >>= 1
    return result


# --- hashing + base58 ------------------------------------------------------
B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def base58_encode(data: bytes) -> str:
    num = int.from_bytes(data, "big")
    enc = ""
    while num > 0:
        num, rem = divmod(num, 58)
        enc = B58[rem] + enc
    for byte in data:
        if byte == 0:
            enc = "1" + enc
        else:
            break
    return enc


def ripemd160(b: bytes) -> bytes:
    try:
        h = hashlib.new("ripemd160")
        h.update(b)
        return h.digest()
    except (ValueError, TypeError):
        return _ripemd160_pure(b)


def point_to_address(point, compressed: bool) -> str:
    x, y = point
    if compressed:
        pubkey = (b"\x02" if y % 2 == 0 else b"\x03") + x.to_bytes(32, "big")
    else:
        pubkey = b"\x04" + x.to_bytes(32, "big") + y.to_bytes(32, "big")
    h160 = ripemd160(hashlib.sha256(pubkey).digest())
    versioned = b"\x00" + h160
    checksum = hashlib.sha256(hashlib.sha256(versioned).digest()).digest()[:4]
    return base58_encode(versioned + checksum)


# --- the range generator ---------------------------------------------------
def parse_key(v):
    if isinstance(v, int):
        return v
    v = str(v).strip().lower()
    return int(v, 16) if (v.startswith("0x") or any(c in "abcdef" for c in v)) else int(v)


def has_zero_run(k: int, min_run: int, base: int) -> bool:
    """True if the key's number (unpadded) contains >= min_run consecutive zeros."""
    s = format(k, "x") if base == 16 else str(k)   # significant digits, no leading zeros
    return ("0" * min_run) in s


def _validate_range(start, end):
    start, end = parse_key(start), parse_key(end)
    if start < 1:
        print("note: skipping keys < 1 (key 0 has no address); starting at 1")
        start = 1
    if end >= N:
        raise ValueError("end is >= curve order N; no valid keys above N-1")
    if end < start:
        raise ValueError("END must be >= START")
    return start, end


def generate(start, end, compressed=True, key_filter=None):
    """Yield (private_key_int, address) for keys in [start, end] passing key_filter.

    key_filter is checked BEFORE deriving the address, so non-matching keys
    skip the SHA256/RIPEMD160/Base58 work entirely.
    """
    start, end = _validate_range(start, end)

    point = scalar_mult(start, G)          # one scalar mult for the first key
    k = start
    while k <= end:
        if key_filter is None or key_filter(k):
            yield k, point_to_address(point, compressed)
        point = point_add(point, G)        # step to the next key by adding G
        k += 1


def generate_random(start, end, compressed=True, count=None, key_filter=None, seed=None):
    """Yield (private_key_int, address) for keys drawn at random from [start, end].

    Unlike generate(), there's no add-G shortcut here: each random key needs its
    own full scalar multiplication, so this is much slower per key. Filtered-out
    keys are re-drawn and don't count toward `count`. `count=None` (or 0) runs
    until you Ctrl-C or hit the break in __main__.
    """
    start, end = _validate_range(start, end)

    rng = random.Random(seed)
    produced = 0
    while count is None or produced < count:
        k = rng.randint(start, end)
        if key_filter is not None and not key_filter(k):
            continue
        yield k, point_to_address(scalar_mult(k, G), compressed)
        produced += 1


# --- pure-Python RIPEMD-160 fallback (used only if hashlib lacks it) -------
def _ripemd160_pure(message: bytes) -> bytes:
    import struct
    def rol(x, n): return ((x << n) | (x >> (32 - n))) & 0xFFFFFFFF
    rl=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,
        3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12,1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,
        4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13]
    rr=[5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12,6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,
        15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13,8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,
        12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11]
    sl=[11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8,7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,
        11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5,11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12,
        9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6]
    sr=[8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6,9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,
        9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5,15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,
        8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11]
    kl=[0x00000000,0x5A827999,0x6ED9EBA1,0x8F1BBCDC,0xA953FD4E]
    kr=[0x50A28BE6,0x5C4DD124,0x6D703EF3,0x7A6D76E9,0x00000000]
    def f(j,x,y,z):
        if j<16: return x^y^z
        if j<32: return (x&y)|(~x&z)
        if j<48: return (x|~y)^z
        if j<64: return (x&z)|(y&~z)
        return x^(y|~z)
    h0,h1,h2,h3,h4=0x67452301,0xEFCDAB89,0x98BADCFE,0x10325476,0xC3D2E1F0
    msg=bytearray(message); ml=len(msg)*8; msg.append(0x80)
    while len(msg)%64!=56: msg.append(0)
    msg+=struct.pack("<Q", ml & 0xFFFFFFFFFFFFFFFF)
    for off in range(0,len(msg),64):
        X=list(struct.unpack("<16I",msg[off:off+64]))
        al,bl,cl,dl,el=h0,h1,h2,h3,h4; ar,br,cr,dr,er=h0,h1,h2,h3,h4
        for j in range(80):
            t=(al+f(j,bl,cl,dl)+X[rl[j]]+kl[j//16])&0xFFFFFFFF
            t=(rol(t,sl[j])+el)&0xFFFFFFFF; al,el,dl,cl,bl=el,dl,rol(cl,10),bl,t
            t=(ar+f(79-j,br,cr,dr)+X[rr[j]]+kr[j//16])&0xFFFFFFFF
            t=(rol(t,sr[j])+er)&0xFFFFFFFF; ar,er,dr,cr,br=er,dr,rol(cr,10),br,t
        t=(h1+cl+dr)&0xFFFFFFFF; h1=(h2+dl+er)&0xFFFFFFFF; h2=(h3+el+ar)&0xFFFFFFFF
        h3=(h4+al+br)&0xFFFFFFFF; h4=(h0+bl+cr)&0xFFFFFFFF; h0=t
    return struct.pack("<5I",h0,h1,h2,h3,h4)


# --- run -------------------------------------------------------------------
def priv_hex(k: int) -> str:
    # full 32-byte private key = 64 hex chars, zero-padded; else compact hex
    return format(k, "064x") if HEX_FULL else format(k, "x")


if __name__ == "__main__":
    import sys

    kind = "compressed" if COMPRESSED else "uncompressed"
    kw = 64 if HEX_FULL else 12          # fixed column width (no need to see all rows first)
    if RANDOM_MODE:
        n_desc = "unbounded" if RANDOM_COUNT in (None, 0) else f"{RANDOM_COUNT} samples"
        print(f"\nRandom keys in {parse_key(START)}..{parse_key(END)}  ({kind}, {n_desc})\n", flush=True)
    else:
        print(f"\nPrivate keys {parse_key(START)}..{parse_key(END)}  ({kind})\n", flush=True)
    print(f"{'PRIVATE KEY (hex)'.ljust(kw)}  WALLET ADDRESS", flush=True)
    print(f"{'-'*kw}  {'-'*34}", flush=True)

    # open the CSV up front (if requested) so rows are written as they're produced
    csv_fh = open(CSV_PATH, "w", newline="") if CSV_PATH else None
    csv_writer = None
    if csv_fh:
        csv_writer = csv.writer(csv_fh)
        csv_writer.writerow(["private_key_hex", "wallet_address"])

    key_filter = None
    if ZERO_FILTER != "off":
        base_name = "hex" if ZERO_BASE == 16 else "decimal"
        if ZERO_FILTER == "only":
            key_filter = lambda k: has_zero_run(k, MIN_ZERO_RUN, ZERO_BASE)
            print(f"(filter: keep only keys WITH >= {MIN_ZERO_RUN} consecutive zeros in {base_name})\n", flush=True)
        elif ZERO_FILTER == "exclude":
            key_filter = lambda k: not has_zero_run(k, MIN_ZERO_RUN, ZERO_BASE)
            print(f"(filter: exclude keys with >= {MIN_ZERO_RUN} consecutive zeros in {base_name})\n", flush=True)
        else:
            raise ValueError('ZERO_FILTER must be "off", "only", or "exclude"')

    # pick the sequential walk or the random sampler
    if RANDOM_MODE:
        rows = generate_random(START, END, COMPRESSED,
                               (None if RANDOM_COUNT in (None, 0) else RANDOM_COUNT),
                               key_filter, RANDOM_SEED)
    else:
        rows = generate(START, END, COMPRESSED, key_filter)

    count = 0
    for k, addr in rows:                                 # iterate the generator directly
        hexk = priv_hex(k)
        print(f"{hexk.ljust(kw)}  {addr}", flush=True)  # flush -> shows up right away
        if csv_writer:
            csv_writer.writerow([hexk, addr])
            csv_fh.flush()                              # persist each row immediately too
        count += 1
        if addr == "1PWo3JeB9jrGwfHDNpdGK54CRas7fsVzXU":  # puzzle 71
            break  # stop printing after the first match, if any
    if csv_fh:
        csv_fh.close()
        print(f"\nSaved {count} rows to {CSV_PATH}", flush=True)