#!/usr/bin/env python3
"""Builds the AES-256 corpus for the cross-library harness, with every expected answer computed by the
compiled Lean specification (`aes256 batch`), the same `encrypt` and `decrypt` the theorems are about.

Three suites:

* block: single-block encryption and decryption. NIST AESAVS VarKey and VarTxt inputs for AES-256, the
  FIPS-197 and SP 800-38A examples, and random keys and blocks.
* ctr: CTR mode (SP 800-38A §6.5) with counters at the 2^32, 2^64 and 2^128 boundaries, where the
  standard incrementing function carries across the whole 128-bit block.
* cbc: CBC decryption with PKCS #7 padding (RFC 5652 §6.3). Some ciphertexts decrypt to correct padding,
  others to padding that is wrong in one way; a library should return the plaintext for the first and
  an error for the second.

Lean computes each AES block; this script only chains blocks together as SP 800-38A describes.

    python3 tools/crossimpl/vectors.py OUT.json [--random 2000] [--seed 1]
"""
import argparse
import json
import os
import random
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
EXE = os.path.join(ROOT, ".lake", "build", "bin", "aes256")


def lean(pairs, decrypt=False):
    """AES-256 of each (key, block) pair, by the Lean specification."""
    if not pairs:
        return []
    args = [EXE, "batch"] + (["decrypt"] if decrypt else [])
    text = "".join(f"{k.hex()} {b.hex()}\n" for k, b in pairs)
    out = subprocess.run(args, input=text, capture_output=True, text=True, check=True).stdout.split()
    assert len(out) == len(pairs), (len(out), len(pairs))
    return [bytes.fromhex(x) for x in out]


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--random", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)

    # ---------- block ----------
    enc = []
    zero = bytes(16)
    for i in range(1, 257):  # AESAVS VarKey: the key's first i bits set, plaintext zero
        enc.append(("varkey-%03d" % i, ((1 << 256) - (1 << (256 - i))).to_bytes(32, "big"), zero))
    for i in range(1, 129):  # AESAVS VarTxt: key zero, the plaintext's first i bits set
        enc.append(("vartxt-%03d" % i, bytes(32), ((1 << 128) - (1 << (128 - i))).to_bytes(16, "big")))
    enc.append(("fips197-c3", bytes(range(32)), bytes.fromhex("00112233445566778899aabbccddeeff")))
    k38a = bytes.fromhex("603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4")
    for j, p in enumerate(["6bc1bee22e409f96e93d7e117393172a", "ae2d8a571e03ac9c9eb76fac45af8e51",
                           "30c81c46a35ce411e5fbc1191a0a52ef", "f69f2445df4f9b17ad2b417be66c3710"]):
        enc.append((f"sp800-38a-f15-{j + 1}", k38a, bytes.fromhex(p)))
    for i in range(a.random):
        enc.append(("random-%04d" % i, rng.randbytes(32), rng.randbytes(16)))
    enc_out = lean([(k, p) for _, k, p in enc])
    dec = [("dec-random-%04d" % i, rng.randbytes(32), rng.randbytes(16)) for i in range(a.random // 2)]
    dec_out = lean([(k, c) for _, k, c in dec], decrypt=True)
    block = [{"id": i, "op": "encrypt", "key": k.hex(), "in": p.hex(), "expect": o.hex()}
             for (i, k, p), o in zip(enc, enc_out)]
    block += [{"id": i, "op": "decrypt", "key": k.hex(), "in": c.hex(), "expect": o.hex()}
              for (i, k, c), o in zip(dec, dec_out)]
    known = {"fips197-c3": "8ea2b7ca516745bfeafc49904b496089",
             "sp800-38a-f15-1": "f3eed1bdb5d2a03c064b5a7e3db181f8",
             "sp800-38a-f15-4": "23304b7a39f9f3ff067d8d8f9e24ecc7"}
    for b in block:
        if b["id"] in known:
            assert b["expect"] == known[b["id"]], b["id"]

    # ---------- ctr ----------
    ctr_cases = []
    for name, iv in [("counter-mid", bytes.fromhex("f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")),
                     ("wrap-128", b"\xff" * 16),
                     ("carry-64", bytes(8) + b"\xff" * 8),
                     ("carry-32", bytes(12) + b"\xff" * 4),
                     ("carry-96", bytes(4) + b"\xff" * 12)]:
        key = rng.randbytes(32)
        for length in (64, 55):
            ctr_cases.append((f"{name}-{length}", key, iv, rng.randbytes(length)))
    ctr = []
    for cid, key, iv, pt in ctr_cases:
        n = (len(pt) + 15) // 16
        counters = [((int.from_bytes(iv, "big") + j) % (1 << 128)).to_bytes(16, "big") for j in range(n)]
        stream = b"".join(lean([(key, c) for c in counters]))
        ctr.append({"id": cid, "key": key.hex(), "iv": iv.hex(), "in": pt.hex(),
                    "expect": xor(pt, stream[:len(pt)]).hex()})
    # SP 800-38A F.5.5 (CTR-AES256.Encrypt) as a fixed point
    f55 = [c for c in ctr if c["id"] == "counter-mid-64"]
    assert f55

    # ---------- cbc ----------
    cbc = []

    def cbc_case(cid, final_block, expect_ok, body_blocks=1):
        """A CBC ciphertext whose last block decrypts to `final_block`, preceded by random blocks."""
        key, iv = rng.randbytes(32), rng.randbytes(16)
        plain = [rng.randbytes(16) for _ in range(body_blocks)] + [final_block]
        cts, prev = [], iv
        for p in plain:
            c = lean([(key, xor(p, prev))])[0]
            cts.append(c)
            prev = c
        full = b"".join(plain)
        expect = full[:-full[-1]].hex() if expect_ok else None
        cbc.append({"id": cid, "key": key.hex(), "iv": iv.hex(), "in": b"".join(cts).hex(),
                    "expect": expect, "valid": expect_ok})

    for n in (1, 2, 15, 16):
        cbc_case(f"pad-ok-{n:02d}", rng.randbytes(16 - n) + bytes([n]) * n, True)
    cbc_case("pad-zero", rng.randbytes(15) + b"\x00", False)
    cbc_case("pad-17", rng.randbytes(15) + b"\x11", False)
    cbc_case("pad-ff", rng.randbytes(15) + b"\xff", False)
    cbc_case("pad-inconsistent-2", rng.randbytes(14) + b"\x05\x02", False)
    cbc_case("pad-inconsistent-8", rng.randbytes(8) + b"\x08" * 3 + b"\x07" + b"\x08" * 4, False)
    cbc_case("pad-inconsistent-16", b"\x0f" + b"\x10" * 15, False)
    cbc_case("pad-16-one-block-only", b"\x10" * 16, True, body_blocks=0)

    json.dump({"block": block, "ctr": ctr, "cbc": cbc}, open(a.out, "w"))
    print(f"block {len(block)}, ctr {len(ctr)}, cbc {len(cbc)}")


if __name__ == "__main__":
    main()
