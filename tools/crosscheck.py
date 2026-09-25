#!/usr/bin/env python3
"""Compare the compiled specification with OpenSSL on random keys and blocks.

The theorems say the Lean definitions decrypt what they encrypt and match the published vectors; this
says they also agree with a production implementation on inputs nobody chose. It needs `openssl` and a
built `aes256` (`lake build aes256`).

    python3 tools/crosscheck.py [--keys 64] [--blocks 16] [--seed N]
"""
import argparse
import os
import random
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXE = os.path.join(ROOT, ".lake", "build", "bin", "aes256")


def openssl_ecb(key: bytes, data: bytes) -> bytes:
    out = subprocess.run(["openssl", "enc", "-aes-256-ecb", "-nopad", "-K", key.hex()],
                         input=data, capture_output=True, check=True)
    return out.stdout


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--keys", type=int, default=64)
    ap.add_argument("--blocks", type=int, default=16)
    ap.add_argument("--seed", type=int, default=None)
    a = ap.parse_args()
    seed = a.seed if a.seed is not None else random.SystemRandom().randrange(2**32)
    rng = random.Random(seed)

    cases, expected = [], []
    for _ in range(a.keys):
        key = rng.randbytes(32)
        blocks = [rng.randbytes(16) for _ in range(a.blocks)]
        ct = openssl_ecb(key, b"".join(blocks))
        for i, blk in enumerate(blocks):
            cases.append(f"{key.hex()} {blk.hex()}")
            expected.append(ct[16 * i:16 * i + 16].hex())

    got = subprocess.run([EXE, "batch"], input="\n".join(cases) + "\n", capture_output=True, text=True,
                         check=True).stdout.split()
    bad = [(c, e, g) for c, e, g in zip(cases, expected, got) if e != g]
    if len(got) != len(expected) or bad:
        for c, e, g in bad[:5]:
            print(f"MISMATCH {c}: openssl {e}, lean {g}")
        print(f"FAIL: {len(bad)} of {len(expected)} differ (seed {seed})")
        return 1
    print(f"OK: {len(expected)} blocks under {a.keys} random keys agree with OpenSSL (seed {seed})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
