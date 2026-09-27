import Pictures.Common

/-!
# AES-256, one step at a time

FIPS-197 Appendix C.3 encrypted step by step: the state after every `SubBytes`, `ShiftRows`,
`MixColumns` and `AddRoundKey` of all fourteen rounds, with the round key each `AddRoundKey` uses.
Put the cursor on the `#widget` line at the bottom and open the infoview.

`trace_ends_in_encrypt` proves the last state drawn is `encrypt keyC3 p`, and `fips197_C3_encrypt` proves
that is the standard's published ciphertext.
-/

namespace Pictures

open Lean AES

/-- Rounds `r, r+1, …` of Algorithm 1, `n` of them, keeping the state after every step. -/
def roundsTrace (rk : Nat → State) : Nat → Nat → State → List (String × Nat × State × Option State)
  | 0, _, _ => []
  | n + 1, r, s =>
    let a := subBytes s
    let b := shiftRows a
    let c := mixColumns b
    let d := addRoundKey c (rk r)
    [("SubBytes", r, a, none), ("ShiftRows", r, b, none), ("MixColumns", r, c, none),
      ("AddRoundKey", r, d, some (rk r))] ++ roundsTrace rk n (r + 1) d

/-- Algorithm 1 with every intermediate state: the input, round 0's `AddRoundKey`, rounds 1 to 13, and the
final round without `MixColumns`. -/
def trace (key : Key) (p : State) : List (String × Nat × State × Option State) :=
  let rk := roundKey (keyExpansion key)
  let s0 := addRoundKey p (rk 0)
  let mid := roundsTrace rk (Nr - 1) 1 s0
  let last := (mid.getLast?.map fun t => t.2.2.1).getD s0
  let a := subBytes last
  let b := shiftRows a
  let c := addRoundKey b (rk Nr)
  [("Input", 0, p, none), ("AddRoundKey", 0, s0, some (rk 0))] ++ mid ++
    [("SubBytes", Nr, a, none), ("ShiftRows", Nr, b, none), ("AddRoundKey", Nr, c, some (rk Nr))]

/-- The plaintext of FIPS-197 Appendix C.3. -/
def plainC3 : State := .ofNat 0x00112233445566778899aabbccddeeff

/-- The drawn trace ends in the cipher's output. -/
theorem trace_ends_in_encrypt :
    ((trace keyC3 plainC3).getLast?.map fun t => t.2.2.1) = some (encrypt keyC3 plainC3) := by
  decide +kernel

def stepJson (t : String × Nat × State × Option State) : Json :=
  json% {
    label: $(t.1),
    round: $(t.2.1),
    state: $(stateJson t.2.2.1),
    key: $(match t.2.2.2 with | some k => stateJson k | none => Json.null)
  }

def roundsProps : Json :=
  json% {
    steps: $((trace keyC3 plainC3).toArray.map stepJson),
    cipherKey: "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    proved: $(#[
      "Pictures.trace_ends_in_encrypt: the last state drawn is encrypt keyC3 plainC3",
      "AES.fips197_C3_encrypt: … = 8ea2b7ca516745bfeafc49904b496089, the FIPS-197 C.3 ciphertext",
      "AES.decrypt_encrypt: decrypt k (encrypt k p) = p for every key and block"])
  }

@[widget_module]
def RoundsWidget : Widget.Module where
  javascript := include_str "rounds.js"

end Pictures

open Pictures in
#widget RoundsWidget with roundsProps
