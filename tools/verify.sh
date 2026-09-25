#!/usr/bin/env bash
# Everything this repository claims, checked from scratch: Lean's kernel builds it, the compiled
# specification agrees with OpenSSL, and Tenet, an independent kernel, re-derives every declaration and
# reports what each headline theorem rests on.
#
# Needs elan, openssl, and Tenet (`dotnet tool install -g tenet`, or TENET="dotnet path/to/tenet.dll").
set -euo pipefail
cd "$(dirname "$0")/.."
TENET=${TENET:-tenet}

echo "== Lean: build (every theorem is checked by Lean's kernel as it compiles)"
lake build

echo "== OpenSSL: the compiled specification on random inputs"
python3 tools/crosscheck.py

echo "== Tenet: re-check the whole import closure"
$TENET check . --all --quiet --report check.json

# The gate: every declaration of the project must rest on nothing beyond propext, Classical.choice and
# Quot.sound. That rules out sorry, a project axiom, and Lean.ofReduceBool (native_decide, bv_decide)
# in one test. (`check --fail-on-axiom` names a single axiom; given twice, only the last counts.)
echo "== Tenet: audit"
$TENET audit .
$TENET audit . --json | python3 -c '
import json, sys
a = json.load(sys.stdin)
if not a["ok"] or a["restingOnAssumption"] or a["redefinesTrustedNames"]:
    sys.exit(f"FAIL: {a}")
print("gate: all %d declarations unconditional" % a["unconditional"])'

echo "== Tenet: what the headline theorems rest on"
$TENET axioms . \
  AES.fips197_C3_encrypt AES.sp800_38a_F15 AES.decrypt_encrypt AES.encrypt_decrypt \
  AES.sbox_eq_affine_inv AES.ddt_le_four AES.agree_bounds \
  AES.branch_mixColumn AES.four_rounds_active
