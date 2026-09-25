import AES.SBox
import AES.Digits

/-!
# Differential uniformity 4, nonlinearity 112

The two numbers that make the S-box a good S-box (*The Design of Rijndael*, §3.6 and §9.1):

* **Differential uniformity 4.** For any nonzero input difference `a` and any output difference `b`, at
  most 4 of the 256 inputs `x` satisfy `S(x ⊕ a) ⊕ S(x) = b`. So a difference passes one S-box with
  probability at most 4/256 = 2⁻⁶.
* **Nonlinearity 112.** For any input mask `a` and nonzero output mask `b`, the parity of `b · S(x)`
  agrees with the parity of `a · x` on between 112 and 144 of the 256 inputs. So a linear approximation
  of one S-box holds with bias at most 16/256 = 2⁻⁴, a correlation of at most 2⁻³.

Both are stated below about `sbox`, the FIPS-197 table, with the tables counted the obvious way by
`List.countP`. They are proved by running a check in the kernel over all 65,280 table rows, each row
held as one number with a base-2¹⁶ digit per entry (`Digits.lean`), and then proving that the check
means what the statements say.
-/

namespace AES

open Digits

set_option maxHeartbeats 0

/-! ## What is claimed -/

/-- The 256 bytes. -/
def bytes : List Byte := (List.range 256).map Nat.toUInt8

/-- Entry `(a, b)` of the difference distribution table: how many inputs `x` take the input difference
`a` to the output difference `b`. -/
def ddt (a b : Byte) : Nat := bytes.countP fun x => sbox (x ^^^ a) ^^^ sbox x == b

/-- The parity of a byte: the XOR of its eight bits. `parity (a &&& x)` is the inner product `a · x`. -/
def parity (b : Byte) : Bool :=
  bit b 0 ^^ bit b 1 ^^ bit b 2 ^^ bit b 3 ^^ bit b 4 ^^ bit b 5 ^^ bit b 6 ^^ bit b 7

/-- Entry `(a, b)` of the linear approximation table, as a count: how many inputs `x` have
`a · x = b · S(x)`. The correlation of the approximation is `(agree a b - 128) / 128`. -/
def agree (a b : Byte) : Nat := bytes.countP fun x => parity (a &&& x) == parity (b &&& sbox x)

/-! ## Fast tables for the kernel -/

/-- The S-box as one 2048-bit number, `S(x)` in bits `8x … 8x + 7`. -/
def SBOXN : Nat := 0x16bb54b00f2d99416842e6bf0d89a18cdf2855cee9871e9b948ed9691198f8e19e1dc186b95735610ef6034866b53e708a8bbd4b1f74dde8c6b4a61c2e2578ba08ae7a65eaf4566ca94ed58d6d37c8e779e4959162acd3c25c2406490a3a32e0db0b5ede14b8ee4688902a22dc4f816073195d643d7ea7c41744975fec130ccdd2f3ff1021dab6bcf5389d928f40a351a89f3c507f02f94585334d43fbaaefd0cf584c4a39becb6a5bb1fc20ed00d153842fe329b3d63b52a05a6e1b1a2c830975b227ebe28012079a059618c323c7041531d871f1e5a534ccf73f362693fdb7c072a49cafa2d4adf04759fa7dc982ca76abd7fe2b670130c56f6bf27b777c63

/-- The parity of each byte as one 256-bit number, `parity x` in bit `x`. -/
def PARN : Nat := 0x6996966996696996966969966996966996696996699696696996966996696996

/-- `S(x)` in one shift and one remainder, both done by GMP in the kernel. -/
def sboxN (x : Nat) : Nat := Nat.mod (Nat.shiftRight SBOXN (Nat.mul 8 x)) 256

/-- `parity x` in one shift and one remainder. -/
def parN (x : Nat) : Bool := Nat.beq (Nat.mod (Nat.shiftRight PARN x) 2) 1

theorem sboxN_spec (x : Byte) : sboxN x.toNat = (sbox x).toNat := by
  have : allBytes (fun x => sboxN x.toNat == (sbox x).toNat) = true := by decide +kernel
  simpa using allBytes_spec this x

theorem parN_spec (x : Byte) : parN x.toNat = parity x := by
  have : allBytes (fun x => parN x.toNat == parity x) = true := by decide +kernel
  simpa using allBytes_spec this x

theorem sboxN_lt (x : Nat) : sboxN x < 256 := Nat.mod_lt _ (by decide)

theorem toNat_toUInt8 {x : Nat} (h : x < 256) : x.toUInt8.toNat = x := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

/-! ## Differential uniformity -/

/-- The output difference for input `x` and input difference `a`. -/
def dN (a x : Nat) : Nat := Nat.xor (sboxN (Nat.xor x a)) (sboxN x)

/-- Row `a` of the difference table, one digit per output difference. -/
def duRow (a : Nat) : Nat := sum (fun x => Nat.pow B (dN a x)) 256

/-- Every row but the first has every entry at most 4. -/
def duCheck : Bool := allBelow 256 fun a => Nat.beq a 0 || digitsIn 0 4 256 (duRow a)

theorem duCheck_eq : duCheck = true := by decide +kernel

theorem dN_lt (a x : Nat) : dN a x < 256 :=
  Nat.xor_lt_two_pow (n := 8) (sboxN_lt _) (sboxN_lt _)

theorem duRow_eq (a : Nat) :
    duRow a = ofDigits (fun k => sum (fun x => if k = 0 + dN a x then 1 else 0) 256) 256 0 := by
  rw [← sum_ofDigits]
  exact sum_congr fun x _ => (ofDigits_single 256 0 _ (dN_lt a x)).symm

theorem ddt_eq (a b : Byte) : ddt a b = sum (fun x => if b.toNat = 0 + dN a.toNat x then 1 else 0) 256 := by
  rw [ddt, bytes, List.countP_map, countP_range]
  apply sum_congr
  intro x hx
  have hd : dN a.toNat x = (sbox (x.toUInt8 ^^^ a) ^^^ sbox x.toUInt8).toNat := by
    rw [UInt8.toNat_xor, ← sboxN_spec, ← sboxN_spec, UInt8.toNat_xor, toNat_toUInt8 hx]; rfl
  have e : (sbox (x.toUInt8 ^^^ a) ^^^ sbox x.toUInt8 == b) = (b.toNat == 0 + dN a.toNat x) := by
    rw [Nat.zero_add, hd]
    generalize sbox (x.toUInt8 ^^^ a) ^^^ sbox x.toUInt8 = u
    by_cases h : u = b
    · simp [h]
    · have : b.toNat ≠ u.toNat := fun h' => h (UInt8.toNat_inj.mp h').symm
      rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr this]
  simp only [Function.comp_def, e, beq_iff_eq]

/-- Differential uniformity 4. A nonzero input difference goes to any given output difference for
at most 4 of the 256 inputs. -/
theorem ddt_le_four (a b : Byte) (ha : a ≠ 0) : ddt a b ≤ 4 := by
  have hrow := allBelow_spec duCheck_eq a.toNat a.toNat_lt
  have ha' : Nat.beq a.toNat 0 = false := by
    cases h : Nat.beq a.toNat 0
    · rfl
    · exact absurd (UInt8.toNat_inj.mp (by rw [Nat.eq_of_beq_eq_true h]; rfl)) ha
  simp only [ha', Bool.false_or] at hrow
  rw [duRow_eq] at hrow
  have hd := digitsIn_ofDigits (fun k => Nat.lt_of_le_of_lt (sum_le _ (fun x => by split <;> omega) 256)
    (by decide : 256 < B)) hrow b.toNat (Nat.zero_le _) b.toNat_lt
  rw [ddt_eq]
  exact hd.2

/-- and exactly 4: the bound is reached. -/
theorem ddt_eq_four : ddt 1 31 = 4 := by decide +kernel

/-! ## Nonlinearity -/

/-- The digits `[a · x = 0]`, one for each mask `a`. -/
def P0 (x : Nat) : Nat := ofDigits (fun a => cond (parN (Nat.land a x)) 0 1) 256 0
/-- The digits `[a · x = 1]`, one for each mask `a`. -/
def P1 (x : Nat) : Nat := ofDigits (fun a => cond (parN (Nat.land a x)) 1 0) 256 0

/-- Column `b` of the linear table, one digit per input mask `a`. For each input `x`, the masks `a`
that agree are the ones whose parity `a · x` equals `b · S(x)`, which is `P0 x` or `P1 x`. -/
def nlCol (b : Nat) : Nat := sum (fun x => cond (parN (Nat.land b (sboxN x))) (P1 x) (P0 x)) 256

/-- Every column but the first has every entry between 112 and 144. -/
def nlCheck : Bool := allBelow 256 fun b => Nat.beq b 0 || digitsIn 112 144 256 (nlCol b)

theorem nlCheck_eq : nlCheck = true := by decide +kernel

theorem nlCol_eq (b : Nat) :
    nlCol b = ofDigits (fun a => sum (fun x =>
      if parN (Nat.land a x) = parN (Nat.land b (sboxN x)) then 1 else 0) 256) 256 0 := by
  rw [nlCol, ← sum_ofDigits]
  apply sum_congr
  intro x _
  cases h : parN (Nat.land b (sboxN x)) <;> simp only [cond, P0, P1] <;>
    exact ofDigits_congr fun a _ _ => by cases parN (Nat.land a x) <;> rfl

theorem agree_eq (a b : Byte) :
    agree a b = sum (fun x => if parN (Nat.land a.toNat x) = parN (Nat.land b.toNat (sboxN x)) then 1 else 0) 256 := by
  rw [agree, bytes, List.countP_map, countP_range]
  apply sum_congr
  intro x hx
  have e1 : parity (a &&& x.toUInt8) = parN (Nat.land a.toNat x) := by
    rw [← parN_spec, UInt8.toNat_and, toNat_toUInt8 hx]; rfl
  have e2 : parity (b &&& sbox x.toUInt8) = parN (Nat.land b.toNat (sboxN x)) := by
    rw [← parN_spec, UInt8.toNat_and, ← sboxN_spec, toNat_toUInt8 hx]; rfl
  simp only [Function.comp_def, e1, e2, beq_iff_eq]

/-- Nonlinearity 112. Every linear approximation `a · x = b · S(x)` with `b ≠ 0` holds for between
112 and 144 of the 256 inputs: its bias is at most 16/256. -/
theorem agree_bounds (a b : Byte) (hb : b ≠ 0) : 112 ≤ agree a b ∧ agree a b ≤ 144 := by
  have hcol := allBelow_spec nlCheck_eq b.toNat b.toNat_lt
  have hb' : Nat.beq b.toNat 0 = false := by
    cases h : Nat.beq b.toNat 0
    · rfl
    · exact absurd (UInt8.toNat_inj.mp (by rw [Nat.eq_of_beq_eq_true h]; rfl)) hb
  simp only [hb', Bool.false_or] at hcol
  rw [nlCol_eq] at hcol
  have hd := digitsIn_ofDigits (fun k => Nat.lt_of_le_of_lt (sum_le _ (fun x => by split <;> omega) 256)
    (by decide : 256 < B)) hcol a.toNat (Nat.zero_le _) a.toNat_lt
  rw [agree_eq]
  exact hd

/-- and exactly 112: the bound is reached, so the nonlinearity is 112, not more. -/
theorem agree_eq_112 : agree 45 1 = 112 := by decide +kernel

end AES
