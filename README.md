# AES-256 in Lean

[![ci](https://github.com/keithadler/lean-aes/actions/workflows/ci.yml/badge.svg)](https://github.com/keithadler/lean-aes/actions/workflows/ci.yml)

**AES-256 written from FIPS-197 in Lean 4, with its correctness and the structural facts behind its
security proved, and every proof re-derived by a second, independent kernel.**

The cipher is the standard's own algorithms, `Cipher`, `InvCipher` and `KeyExpansion`, with the S-box
tables copied from it. On top of that:

| | theorem | file |
| --- | --- | --- |
| The published answers | FIPS-197 C.3 encrypts and decrypts, A.3's key expansion, SP 800-38A F.1.5's four blocks | [Vectors](AES/Vectors.lean) |
| Decryption undoes encryption | `decrypt k (encrypt k p) = p`, and the converse, for every key and block | [RoundTrip](AES/RoundTrip.lean) |
| The S-box is what FIPS-197 says | Table 4 is the GF(2⁸) inverse followed by the affine map, byte for byte; Table 6 inverts it | [SBox](AES/SBox.lean) |
| Differential uniformity 4 | a nonzero input difference reaches any output difference for at most 4 of 256 inputs, and 4 is reached | [SBoxProps](AES/SBoxProps.lean) |
| Nonlinearity 112 | every linear approximation `a·x = b·S(x)`, `b ≠ 0`, holds on 112 to 144 inputs, and 112 is reached | [SBoxProps](AES/SBoxProps.lean) |
| Branch number 5 | a nonzero column and its `MixColumns` image have at least 5 nonzero bytes between them, and 5 is reached | [Branch](AES/Branch.lean) |
| **The wide-trail bound** | **any four consecutive rounds, under any keys, activate at least 25 S-boxes for any two different blocks** | [WideTrail](AES/WideTrail.lean) |

Together the last three give the classic consequence: a single four-round differential trail has
probability at most `(4/256)²⁵ = 2⁻¹⁵⁰`, and a single linear trail correlation at most `(2⁻³)²⁵ = 2⁻⁷⁵`.
That multiplication is not formalized here; the three facts it multiplies are.

The headline statements, as Lean states them:

```lean
theorem decrypt_encrypt (key : Key) (p : State) : decrypt key (encrypt key p) = p

theorem fips197_C3_encrypt :
    encrypt keyC3 (.ofNat 0x00112233445566778899aabbccddeeff) = .ofNat 0x8ea2b7ca516745bfeafc49904b496089

theorem ddt_le_four (a b : Byte) (ha : a ≠ 0) : ddt a b ≤ 4
theorem agree_bounds (a b : Byte) (hb : b ≠ 0) : 112 ≤ agree a b ∧ agree a b ≤ 144
theorem branch_mixColumn (a : Word) (ha : a ≠ 0) : 5 ≤ a.wt + (mixColumn a).wt

theorem four_rounds_active (k1 k2 k3 x y : State) (h : x ≠ y) :
    25 ≤ active x y + active (aesRound k1 x) (aesRound k1 y) +
      active (aesRound k2 (aesRound k1 x)) (aesRound k2 (aesRound k1 y)) +
      active (aesRound k3 (aesRound k2 (aesRound k1 x))) (aesRound k3 (aesRound k2 (aesRound k1 y)))
```

## What is not claimed

- **That AES is secure.** Nobody can prove AES-256 is a pseudorandom permutation, in Lean or anywhere
  else; it would settle open questions at the level of P vs NP. Formal cryptography (EasyCrypt,
  CryptHOL, HACL*) assumes it and proves what is built on it. The results here are the ones that can
  be proved: facts about the design that rule out whole families of attack.
- **More than single trails.** The bound is on one trail at a time. Differentials that collect many
  trails, linear hulls, and related-key attacks on the AES-256 key schedule are outside it.
- **Anything about an implementation's timing.** `aes256` is the specification compiled, for checking
  against other implementations. It is not constant-time and not for production use; a constant-time
  proof needs a model of the machine, which is what AWS's LNSym provides.

## How it is checked

Five tools, each asked a different question.

**Lean's kernel** checks every proof as the project builds. No proof uses `native_decide` or
`bv_decide`, which would trust compiled code; everything computational, from the test vectors to the
65,280 rows of the S-box's difference and linear tables, is run by the kernel itself through
`decide +kernel`. The whole project rests on the axioms `propext`, `Quot.sound` and, for a few proofs,
`Classical.choice`, and on nothing else.

**[Tenet](https://github.com/keithadler/tenet)**, an independent implementation of Lean's kernel,
re-derives every declaration from the compiled `.olean` files, Lean's core library included:

```
$ tenet check . --all
OK: 65446 checked in 662 modules, 0 failed, 662 modules mapped, 125.4s, 4 jobs

$ tenet audit .
.: 640 declarations defined by this project in 13 modules
  unconditional (nothing beyond propext, Classical.choice, Quot.sound): 640 (100.0%)
  resting on an assumption: 0 (0.0%)
  no assumptions: this project introduces no axioms and no sorry
```

Tenet declines, with its own exit status, to accept anything that rests on compiled code, which is
the second reason for avoiding `native_decide`: a proof here is one two kernels can each follow to the
end. CI fails unless Tenet's audit finds every declaration unconditional, which rules out `sorry`, a
project axiom and `Lean.ofReduceBool` in one test. That gate was tried on a planted `sorry` and fails
as it should.

**OpenSSL** checks the definitions themselves, which no proof can: `tools/crosscheck.py` runs random
keys and blocks through the compiled specification and through OpenSSL and compares them.

```
$ python3 tools/crosscheck.py
OK: 1024 blocks under 64 random keys agree with OpenSSL (seed 1492312056)
```

**[Lean Studio](https://github.com/keithadler/leanstudio)** is the editor this was written for. Build
gives each declaration Tenet's badge in the gutter, and its project map summarizes the result:

```
$ python3 tools/leanstudio.py verify project_map
== verify
Tenet checked 353 declarations in 13 modules (Lean 4.34.0): 353 verified, 0 resting on an assumption, 0 rejected.
== project_map
343 declarations: 343 fully proved, 0 rest on sorry, 0 are or rest on a project axiom.
Everything is fully proved.
```

Its linters and import checker were run over every file and their findings fixed, and its proof
walkthroughs of the tactic proofs are in [`docs/walkthroughs`](docs/walkthroughs): each proof step by
step, with the goals before and after every tactic.

**[LeanViz](https://github.com/keithadler/leanviz)** turns the build into a site with a page per
declaration: its statement, docstring and source, what it uses and what uses it, the axioms it rests on,
and Tenet's verdict. CI builds it on every push and publishes it from `main`; `tools/leanviz.sh --serve`
builds and serves it locally.

## Layout

| file | what |
| --- | --- |
| [`AES/Basic.lean`](AES/Basic.lean) | bytes, words and the state, as plain structures the kernel can evaluate |
| [`AES/GF.lean`](AES/GF.lean) | GF(2⁸): `xtime`, multiplication, inverses, and the field laws |
| [`AES/SBox.lean`](AES/SBox.lean) | Tables 4 and 6, and what they are |
| [`AES/Spec.lean`](AES/Spec.lean) | the transformations, `KeyExpansion`, `Cipher`, `InvCipher`, `encrypt`, `decrypt` |
| [`AES/Vectors.lean`](AES/Vectors.lean) | the known-answer tests, as theorems |
| [`AES/Linear.lean`](AES/Linear.lean) | columns as vectors, and `InvMixColumns ∘ MixColumns = id` |
| [`AES/RoundTrip.lean`](AES/RoundTrip.lean) | decryption undoes encryption |
| [`AES/Branch.lean`](AES/Branch.lean) | the branch number of `MixColumns` |
| [`AES/WideTrail.lean`](AES/WideTrail.lean) | 25 active S-boxes in four rounds |
| [`AES/Digits.lean`](AES/Digits.lean) | counting with one big number per table row |
| [`AES/SBoxProps.lean`](AES/SBoxProps.lean) | differential uniformity and nonlinearity |
| [`Main.lean`](Main.lean) | `aes256`, the specification as a command-line tool |
| [`tools/`](tools) | `verify.sh`, `crosscheck.py`, `leanviz.sh`, `leanstudio.py` |
| [`.leanstudio/commands.json`](.leanstudio/commands.json) | the project's commands in Lean Studio's palette |

## Reproduce it

You need [elan](https://github.com/leanprover/elan), `openssl`, and for the independent check the .NET 10
SDK with Tenet (`dotnet tool install -g tenet`).

```bash
git clone https://github.com/keithadler/lean-aes && cd lean-aes
lake build                      # Lean 4.34.0; about three minutes, most of it the kernel computing
lake exe aes256 encrypt 000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f \
                        00112233445566778899aabbccddeeff    # 8ea2b7ca516745bfeafc49904b496089
tools/verify.sh                 # build, OpenSSL, Tenet's check, audit and axioms
tools/leanviz.sh --serve        # the navigator at http://localhost:8787/?p=aes
```

In Lean Studio, open the folder and press Build: every declaration gets Tenet's check mark. The
commands in `.leanstudio/commands.json` show in the palette as *Project: …*: the full verification, the
OpenSSL cross-check, Tenet's axioms or reasons for the name under the cursor, and the LeanViz site.
Assistants that speak MCP can drive the same checks through `LeanStudio --mcp`; `tools/leanstudio.py`
is a minimal client (`LEANSTUDIO="dotnet path/to/LeanStudio.dll" python3 tools/leanstudio.py build verify`).

## How the heavy facts are proved

A SAT solver would settle the 2³² cases of the branch number, and `native_decide` would tabulate the
S-box in a second. Both would put trust in code outside the kernel, which is what this repository is
set up to avoid, so the proofs are arranged so that what the kernel computes stays small.

- **The field laws come from one fact.** `xtime` is additive, a bit-level argument about a shift and a
  conditional XOR. From it, multiplication by any `a` is additive and commutes with `xtime`, so any two
  multiplications commute, and commutativity and associativity follow by putting `1` in the right place.
  Only the one-variable facts, `a • 1 = a` and `b • b⁻¹ = 1`, are checked byte by byte.
- **`InvMixColumns ∘ MixColumns = id` is a matrix product.** Applying two matrices in turn is applying
  their product, proved once for any matrices; the kernel multiplies the two of FIPS-197 and sees the
  identity.
- **The branch number is 1,544 small cases, not 2³².** `MixColumns` commutes with scaling a column by a
  nonzero byte, which does not move its zeros, so a column with two nonzero bytes can be scaled until the
  first is `1`. For three or four nonzero bytes, look at the output: if it had one nonzero byte, the input
  would be a multiple of a column of the inverse matrix, which has four.
- **A table row is 256 big additions, not 65,536 counts.** Each row of the difference or linear table is
  held as one number, a base-2¹⁶ digit per entry, and the kernel does arithmetic on numbers with GMP, so
  the contribution of one input to all 256 entries of a row is a single addition. [`Digits.lean`](AES/Digits.lean) proves that reading the digits
  back gives exactly the counts the statements are about.
- **The wide-trail bound is the book's proof.** Two rounds: branch number 5, column by column, gives at
  least `5 ×` the active columns entering `MixColumns`. Four rounds: `ShiftRows` takes one byte from each
  column, so an active column in round 2 has at most as many bytes as round 1 has active columns, and
  branch number 5 gives the rest.

| module | build | Tenet |
| --- | ---: | ---: |
| `GF` | 20 s | 17 s for `mul_inv` |
| `SBox` | 62 s | 30 s for the inverse table |
| `Vectors` | 31 s | 13 s for SP 800-38A |
| `Branch` | 23 s | 14 s for the weight-two cases |
| `SBoxProps` | 48 s | 22 s for the linear table |
| everything else | under 2 s each | |

## License

[MIT](LICENSE).
