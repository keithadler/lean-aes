import Pictures.Common

/-!
# Twenty-five active S-boxes, and a pair that hits exactly 25

`four_rounds_active` proves any four consecutive rounds activate at least 25 S-boxes for two different
blocks. This picture draws the differences round by round, and `tight_pair_25` shows the bound cannot be
raised: the pair below activates exactly 4 + 1 + 4 + 16 = 25 under the FIPS-197 C.3 round keys. Put the
cursor on the `#widget` line at the bottom and open the infoview.

The pair is built backwards. `MixColumns` is invertible, so `invMixColumn ⟨1, 0, 0, 0⟩` is a column
difference that `MixColumns` turns into a single byte. Placing it on the diagonal that `ShiftRows` gathers
into column 0, through the S-box, gives 4 active bytes that leave the first round as 1. Branch number 5
then forces 4 and 16.
-/

namespace Pictures

open Lean AES

/-- The FIPS-197 C.3 plaintext, the first block of the pair. -/
def trailX : State := .ofNat 0x00112233445566778899aabbccddeeff

/-- The column difference `MixColumns` maps to `⟨1, 0, 0, 0⟩`. -/
def gathered : Word := invMixColumn ⟨1, 0, 0, 0⟩

/-- Change byte `b` so that its S-box output changes by `d`. -/
def nudge (b d : Byte) : Byte := invSbox (sbox b ^^^ d)

/-- The second block: `trailX` with the diagonal bytes `s[r, r]` nudged by `gathered`. -/
def trailY : State :=
  let x := trailX
  ⟨{ x.c0 with b0 := nudge x.c0.b0 gathered.b0 }, { x.c1 with b1 := nudge x.c1.b1 gathered.b1 },
   { x.c2 with b2 := nudge x.c2.b2 gathered.b2 }, { x.c3 with b3 := nudge x.c3.b3 gathered.b3 }⟩

/-- A second pair for contrast: one byte apart. -/
def oneByteY : State := { trailX with c0 := { trailX.c0 with b0 := trailX.c0.b0 ^^^ 1 } }

/-- The round keys 1, 2, 3 of FIPS-197 C.3. -/
def rk (r : Nat) : State := roundKey (keyExpansion keyC3) r

/-- The four inputs to `SubBytes` over four rounds, for a pair. -/
def layers (x y : State) : List (State × State) :=
  let x1 := aesRound (rk 1) x
  let y1 := aesRound (rk 1) y
  let x2 := aesRound (rk 2) x1
  let y2 := aesRound (rk 2) y1
  let x3 := aesRound (rk 3) x2
  let y3 := aesRound (rk 3) y2
  [(x, y), (x1, y1), (x2, y2), (x3, y3)]

theorem trail_pair_ne : trailX ≠ trailY := by decide +kernel

/-- The bound of `four_rounds_active` is reached: this pair activates exactly 25 S-boxes. -/
theorem tight_pair_25 :
    active trailX trailY + active (aesRound (rk 1) trailX) (aesRound (rk 1) trailY) +
      active (aesRound (rk 2) (aesRound (rk 1) trailX)) (aesRound (rk 2) (aesRound (rk 1) trailY)) +
      active (aesRound (rk 3) (aesRound (rk 2) (aesRound (rk 1) trailX)))
        (aesRound (rk 3) (aesRound (rk 2) (aesRound (rk 1) trailY))) = 25 := by
  decide +kernel

def pairJson (name note : String) (x y : State) : Json :=
  json% {
    name: $(name),
    note: $(note),
    layers: $((layers x y).toArray.map fun (a, b) =>
      json% { x: $(stateJson a), y: $(stateJson b), diff: $(stateJson (a ^^^ b)), active: $(active a b) })
  }

def trailProps : Json :=
  json% {
    pairs: $(#[
      pairJson "The tight pair" "4 + 1 + 4 + 16 = 25: the bound is reached" trailX trailY,
      pairJson "One byte apart" "1 + 4 + 16 + 16 = 37: a typical pair" trailX oneByteY]),
    proved: $(#[
      "AES.four_rounds_active: x ≠ y → 25 ≤ the active S-boxes of four rounds, any keys",
      "Pictures.tight_pair_25: this pair activates exactly 25, so 25 cannot be raised",
      "AES.branch_mixColumn: why 1 becomes 4 and 4 becomes 16"])
  }

@[widget_module]
def TrailWidget : Widget.Module where
  javascript := include_str "trail.js"

end Pictures

open Pictures in
#widget TrailWidget with trailProps
