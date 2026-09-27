import Pictures.Common

/-!
# The S-box's difference table

Row `a`, column `b`: how many of the 256 inputs `x` have `S(x ⊕ a) ⊕ S(x) = b`, which is `ddt a b`. A
differential attack wants a big entry. `ddt_le_four` proves none exceeds 4 once `a ≠ 0`, and `ddt_eq_four`
that 4 is reached. Put the cursor on the `#widget` line at the bottom and open the infoview; hover a cell
for its inputs.
-/

namespace Pictures

open Lean AES

/-- Row `a` of the table, by one pass over the inputs: `row[b] = ddt a b`. -/
def ddtRow (a : Byte) : Array Nat := Id.run do
  let mut row := Array.replicate 256 0
  for x in allBytes do
    let b := (sbox (x ^^^ a) ^^^ sbox x).toNat
    row := row.modify b (· + 1)
  return row

/-- Rows `1 … 255` as one string, a character per cell: `0`, `2` or `4` inputs become `0`, `1`, `2`. -/
def ddtCells : String := Id.run do
  let mut out := ""
  for a in (allBytes.extract 1 256) do
    for n in ddtRow a do
      out := out.push (Char.ofNat (48 + n / 2))
  return out

def differencesProps : Json :=
  json% {
    cells: $(ddtCells),
    sbox: $(allBytes.map fun x => byteJson (sbox x)),
    proved: $(#[
      "AES.ddt_le_four: a ≠ 0 → ddt a b ≤ 4, for all 65,280 cells",
      "AES.ddt_eq_four: ddt 1 31 = 4, so 4 is reached",
      "Pictures.ddtRow_one (DifferencesCheck.lean): the drawn row a = 1 is ddt 1 b, cell by cell"])
  }

@[widget_module]
def DifferencesWidget : Widget.Module where
  javascript := include_str "differences.js"

end Pictures

open Pictures in
#widget DifferencesWidget with differencesProps
