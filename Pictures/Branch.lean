import Pictures.Common

/-!
# MixColumns spreads every difference

Type any nonzero column and see `MixColumns` of it. `branch_mixColumn` proves the nonzero bytes going in
and coming out always add up to at least 5, the branch number, and `branch_mixColumn_tight` that 5 is
reached. Put the cursor on the `#widget` line at the bottom and open the infoview.

The page multiplies with tables of `mul 2` and `mul 3` computed here, and before drawing anything it
compares its `MixColumns` with Lean's `mixColumn` on the sample columns below.
-/

namespace Pictures

open Lean AES

/-- Columns of weight 2 whose image has weight 3, the tight case: `⟨v, 1, 0, 0⟩` for the `v` that work. -/
def tightColumns : Array Word :=
  (allBytes.extract 1 256).filterMap fun v =>
    let a : Word := ⟨v, 1, 0, 0⟩
    if (mixColumn a).wt == 3 then some a else none

/-- Columns to check the page against, spread over all weights. -/
def sampleColumns : Array Word :=
  (Array.range 48).map fun i =>
    let b (k : Nat) : Byte := ((i * 97 + k * 61 + i * i * 13) % 256).toUInt8
    ⟨b 0, if i % 3 = 0 then 0 else b 1, if i % 4 = 0 then 0 else b 2, if i % 5 = 0 then 0 else b 3⟩

def branchProps : Json :=
  json% {
    mul2: $(allBytes.map fun x => byteJson (mul 0x02 x)),
    mul3: $(allBytes.map fun x => byteJson (mul 0x03 x)),
    samples: $(sampleColumns.map fun w => Json.arr #[wordJson w, wordJson (mixColumn w)]),
    tight: $(tightColumns.map wordJson),
    proved: $(#[
      "AES.branch_mixColumn: a ≠ 0 → 5 ≤ a.wt + (mixColumn a).wt",
      "AES.branch_mixColumn_tight: some nonzero column reaches exactly 5"])
  }

@[widget_module]
def BranchWidget : Widget.Module where
  javascript := include_str "branch.js"

end Pictures

open Pictures in
#widget BranchWidget with branchProps
