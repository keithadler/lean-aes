import AES
import Lean.Data.Json
import Lean.Widget.UserWidget
import Lean.Widget.Commands

/-!
# What the pictures share

Every number a picture draws is computed here, in Lean, by the same definitions the proofs are about, and
handed to the page as JSON. The page only lays it out.
-/

namespace Pictures

open Lean AES

/-- A byte as a JSON number. -/
def byteJson (b : Byte) : Json := toJson b.toNat

/-- A state as sixteen bytes in input order: index `r + 4c` is `s[r, c]`. -/
def stateJson (s : State) : Json := Json.arr (s.toList.toArray.map byteJson)

/-- A word as four bytes, row 0 first. -/
def wordJson (w : Word) : Json := Json.arr #[byteJson w.b0, byteJson w.b1, byteJson w.b2, byteJson w.b3]

/-- The 256 bytes `0 … 255`, as an array to loop over. -/
def allBytes : Array Byte := (Array.range 256).map Nat.toUInt8

end Pictures
