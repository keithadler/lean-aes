#!/usr/bin/env python3
"""Python `cryptography` (OpenSSL underneath for AES): ECB, CTR, and CBC with its PKCS7 unpadder."""
import sys

from cryptography.hazmat.primitives import padding
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

for line in sys.stdin:
    suite, cid, op, key, iv, data = line.rstrip("\n").split("\t")
    key, data = bytes.fromhex(key), bytes.fromhex(data)
    try:
        if suite == "block":
            c = Cipher(algorithms.AES(key), modes.ECB())
            ctx = c.decryptor() if op == "decrypt" else c.encryptor()
            out = (ctx.update(data) + ctx.finalize()).hex()
        elif suite == "ctr":
            ctx = Cipher(algorithms.AES(key), modes.CTR(bytes.fromhex(iv))).encryptor()
            out = (ctx.update(data) + ctx.finalize()).hex()
        else:
            ctx = Cipher(algorithms.AES(key), modes.CBC(bytes.fromhex(iv))).decryptor()
            padded = ctx.update(data) + ctx.finalize()
            u = padding.PKCS7(128).unpadder()
            out = (u.update(padded) + u.finalize()).hex()
    except Exception as e:  # noqa: BLE001
        out = f"ERR:{type(e).__name__}: {e}"
    print(f"{suite}\t{cid}\t{out}", flush=True)
