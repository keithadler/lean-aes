import AES.Branch
import AES.RoundTrip

/-!
# Four rounds activate at least 25 S-boxes

The wide-trail bound of Daemen and Rijmen (*The Design of Rijndael*, Theorem 9.5.1), stated for the
actual cipher rather than for an abstraction of it. Run two different blocks through four consecutive
rounds under the same round keys. An S-box is *active* when its two inputs differ. Then at least 25 of
the 64 S-box applications are active, whatever the key and whatever the two blocks.

That is the fact behind AES's resistance to differential cryptanalysis: every active S-box passes a
difference with probability at most 4/256 (`differential uniformity 4`, in `SBoxProps.lean`), so any
single four-round differential trail has probability at most `(2⁻⁶)²⁵ = 2⁻¹⁵⁰`. The linear bound is the
same argument with nonlinearity 112 in place of uniformity 4.

The proof is the one in the book, with nothing assumed:

1. **Two rounds.** Before `MixColumns`, the difference has as many nonzero bytes as the round's input
   difference did, since `SubBytes` is a bijection and `ShiftRows` a permutation. Each active column
   of it, together with the same column after `MixColumns`, has at least five nonzero bytes (branch
   number 5). So a round's input difference and the next round's together have at least
   `5 ×` (the number of active columns entering `MixColumns`).
2. **Four rounds.** That gives `5 × (a₀ + a₂)` with `aᵢ` those column counts in rounds 1 and 3. Some
   column entering round 2's `MixColumns` is active, and `ShiftRows` gave it at most one byte from each
   column active after round 1's, so it has at most `a₀` nonzero bytes. Branch number 5 leaves at least
   `5 - a₀` nonzero bytes in that column after `MixColumns`, and `ShiftRows` spreads them over as many
   different columns in round 3. So `a₂ ≥ 5 - a₀`, and the total is at least `5 × 5`.
-/

namespace AES

/-- A full middle round, as in lines 5–8 of Algorithm 1. -/
def aesRound (k s : State) : State := addRoundKey (mixColumns (shiftRows (subBytes s))) k

/-- The number of nonzero bytes of a state: for a difference, the number of active S-boxes it meets. -/
def State.wt (s : State) : Nat := s.c0.wt + s.c1.wt + s.c2.wt + s.c3.wt

/-- `1` if the column is nonzero. -/
def nzw (w : Word) : Nat := if w.wt = 0 then 0 else 1

/-- The number of nonzero columns. -/
def State.ac (s : State) : Nat := nzw s.c0 + nzw s.c1 + nzw s.c2 + nzw s.c3

/-! ## Bytes and columns -/

theorem nzw_le (w : Word) : nzw w ≤ 1 := by unfold nzw; split <;> omega

theorem nz_le_nzw (a b c d : Byte) :
    nz a ≤ nzw ⟨a, b, c, d⟩ ∧ nz b ≤ nzw ⟨a, b, c, d⟩ ∧ nz c ≤ nzw ⟨a, b, c, d⟩ ∧ nz d ≤ nzw ⟨a, b, c, d⟩ := by
  have := nz_le a; have := nz_le b; have := nz_le c; have := nz_le d
  unfold nzw Word.wt
  split <;> simp_all <;> omega

theorem nzw_le_wt (w : Word) : nzw w ≤ w.wt := by unfold nzw; split <;> omega

/-- `SubBytes` keeps the pattern of a difference: two bytes differ after the S-box exactly when they
differed before. -/
theorem nz_sbox_xor (a b : Byte) : nz (sbox a ^^^ sbox b) = nz (a ^^^ b) := by
  unfold nz
  have : sbox a = sbox b ↔ a = b := ⟨sbox_injective, fun h => h ▸ rfl⟩
  simp only [UInt8.xor_eq_zero_iff, this]

theorem wt_map_sbox_xor (a b : Word) : (a.map sbox ^^^ b.map sbox).wt = (a ^^^ b).wt := by
  simp only [Word.wt, Word.map, Word.xor_def, nz_sbox_xor]

/-- `MixColumns` keeps whether a column difference is zero. -/
theorem nzw_mixColumn_xor (a b : Word) : nzw (mixColumn a ^^^ mixColumn b) = nzw (a ^^^ b) := by
  rw [← mixColumn_xor]
  unfold nzw
  have : mixColumn (a ^^^ b) = 0 ↔ a ^^^ b = 0 := by
    constructor
    · intro h; rw [← invMixColumn_mixColumn (a ^^^ b), h, invMixColumn_eq, Mat.apply_zero]
    · intro h; rw [h, mixColumn_eq, Mat.apply_zero]
  simp only [Word.wt_eq_zero, this]

/-- A column difference and its image under `MixColumns`: at least five nonzero bytes if active. -/
theorem branch_col (a b : Word) : 5 * nzw (a ^^^ b) ≤ (a ^^^ b).wt + (mixColumn a ^^^ mixColumn b).wt := by
  by_cases h : a = b
  · subst h; simp [nzw, Word.wt_eq_zero]
  · have := branch_mixColumn_diff h
    have := nzw_le (a ^^^ b)
    omega

/-! ## States -/

/-- The difference entering `MixColumns` in a round, from the round's two inputs. -/
def mcIn (x y : State) : State := shiftRows (subBytes x) ^^^ shiftRows (subBytes y)

theorem wt_mcIn (x y : State) : (mcIn x y).wt = (x ^^^ y).wt := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := x
  obtain ⟨⟨e0, e1, e2, e3⟩, ⟨f0, f1, f2, f3⟩, ⟨g0, g1, g2, g3⟩, ⟨h0, h1, h2, h3⟩⟩ := y
  simp only [mcIn, State.wt, Word.wt, shiftRows, subBytes, State.mapCols, Word.map, State.xor_def,
    Word.xor_def, nz_sbox_xor]
  omega

/-- The difference after a round is `MixColumns` applied, column by column, to `mcIn`; the round keys
cancel. -/
theorem aesRound_xor (k x y : State) :
    aesRound k x ^^^ aesRound k y = mixColumns (shiftRows (subBytes x)) ^^^ mixColumns (shiftRows (subBytes y)) := by
  unfold aesRound addRoundKey
  generalize mixColumns (shiftRows (subBytes x)) = p
  generalize mixColumns (shiftRows (subBytes y)) = q
  simp only [State.xor_def, Word.xor_def, xor_xor_cancel]

/-- **Two rounds**: a round's input difference and the next round's input difference have at least
`5 ×` (active columns entering `MixColumns`) nonzero bytes between them. -/
theorem two_rounds (k x y : State) :
    5 * (mcIn x y).ac ≤ (x ^^^ y).wt + (aesRound k x ^^^ aesRound k y).wt := by
  rw [← wt_mcIn, aesRound_xor]
  generalize hp : shiftRows (subBytes x) = p
  generalize hq : shiftRows (subBytes y) = q
  have hm : mcIn x y = p ^^^ q := by rw [mcIn, hp, hq]
  rw [hm]
  obtain ⟨p0, p1, p2, p3⟩ := p
  obtain ⟨q0, q1, q2, q3⟩ := q
  have := branch_col p0 q0; have := branch_col p1 q1; have := branch_col p2 q2; have := branch_col p3 q3
  simp only [State.ac, State.wt, mixColumns, State.mapCols, State.xor_def] at *
  omega

/-- The active columns after a round are the active columns entering its `MixColumns`. -/
theorem ac_aesRound_xor (k x y : State) : (aesRound k x ^^^ aesRound k y).ac = (mcIn x y).ac := by
  rw [aesRound_xor, mcIn]
  generalize shiftRows (subBytes x) = p
  generalize shiftRows (subBytes y) = q
  obtain ⟨p0, p1, p2, p3⟩ := p
  obtain ⟨q0, q1, q2, q3⟩ := q
  simp only [State.ac, mixColumns, State.mapCols, State.xor_def, nzw_mixColumn_xor]

/-- `ShiftRows` gathers each column from four different columns, so a column of `mcIn` has at most as
many nonzero bytes as the round's input difference has active columns. -/
theorem wt_mcIn_col_le (x y : State) :
    (mcIn x y).c0.wt ≤ (x ^^^ y).ac ∧ (mcIn x y).c1.wt ≤ (x ^^^ y).ac ∧
    (mcIn x y).c2.wt ≤ (x ^^^ y).ac ∧ (mcIn x y).c3.wt ≤ (x ^^^ y).ac := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := x
  obtain ⟨⟨e0, e1, e2, e3⟩, ⟨f0, f1, f2, f3⟩, ⟨g0, g1, g2, g3⟩, ⟨h0, h1, h2, h3⟩⟩ := y
  have := nz_le_nzw (a0 ^^^ e0) (a1 ^^^ e1) (a2 ^^^ e2) (a3 ^^^ e3)
  have := nz_le_nzw (b0 ^^^ f0) (b1 ^^^ f1) (b2 ^^^ f2) (b3 ^^^ f3)
  have := nz_le_nzw (c0 ^^^ g0) (c1 ^^^ g1) (c2 ^^^ g2) (c3 ^^^ g3)
  have := nz_le_nzw (d0 ^^^ h0) (d1 ^^^ h1) (d2 ^^^ h2) (d3 ^^^ h3)
  simp only [mcIn, State.ac, Word.wt, shiftRows, subBytes, State.mapCols, Word.map, State.xor_def,
    Word.xor_def, nz_sbox_xor] at *
  omega

/-- and, the other way, it sends the four bytes of any one column to four different columns. -/
theorem ac_mcIn_ge (x y : State) :
    (x ^^^ y).c0.wt ≤ (mcIn x y).ac ∧ (x ^^^ y).c1.wt ≤ (mcIn x y).ac ∧
    (x ^^^ y).c2.wt ≤ (mcIn x y).ac ∧ (x ^^^ y).c3.wt ≤ (mcIn x y).ac := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := x
  obtain ⟨⟨e0, e1, e2, e3⟩, ⟨f0, f1, f2, f3⟩, ⟨g0, g1, g2, g3⟩, ⟨h0, h1, h2, h3⟩⟩ := y
  simp only [mcIn, State.ac, Word.wt, shiftRows, subBytes, State.mapCols, Word.map, State.xor_def,
    Word.xor_def]
  have := nz_le_nzw (sbox a0 ^^^ sbox e0) (sbox b1 ^^^ sbox f1) (sbox c2 ^^^ sbox g2) (sbox d3 ^^^ sbox h3)
  have := nz_le_nzw (sbox b0 ^^^ sbox f0) (sbox c1 ^^^ sbox g1) (sbox d2 ^^^ sbox h2) (sbox a3 ^^^ sbox e3)
  have := nz_le_nzw (sbox c0 ^^^ sbox g0) (sbox d1 ^^^ sbox h1) (sbox a2 ^^^ sbox e2) (sbox b3 ^^^ sbox f3)
  have := nz_le_nzw (sbox d0 ^^^ sbox h0) (sbox a1 ^^^ sbox e1) (sbox b2 ^^^ sbox f2) (sbox c3 ^^^ sbox g3)
  simp only [nz_sbox_xor] at *
  omega

/-- The branch number, applied to column `j` of round 2's `MixColumns`. -/
theorem branch_round_cols (k x y : State) :
    5 * nzw (mcIn x y).c0 ≤ (mcIn x y).c0.wt + (aesRound k x ^^^ aesRound k y).c0.wt ∧
    5 * nzw (mcIn x y).c1 ≤ (mcIn x y).c1.wt + (aesRound k x ^^^ aesRound k y).c1.wt ∧
    5 * nzw (mcIn x y).c2 ≤ (mcIn x y).c2.wt + (aesRound k x ^^^ aesRound k y).c2.wt ∧
    5 * nzw (mcIn x y).c3 ≤ (mcIn x y).c3.wt + (aesRound k x ^^^ aesRound k y).c3.wt := by
  rw [aesRound_xor, mcIn]
  generalize shiftRows (subBytes x) = p
  generalize shiftRows (subBytes y) = q
  obtain ⟨p0, p1, p2, p3⟩ := p
  obtain ⟨q0, q1, q2, q3⟩ := q
  simp only [mixColumns, State.mapCols, State.xor_def]
  exact ⟨branch_col p0 q0, branch_col p1 q1, branch_col p2 q2, branch_col p3 q3⟩

theorem wt_le_four_nzw (w : Word) : w.wt ≤ 4 * nzw w := by
  have := nz_le w.b0; have := nz_le w.b1; have := nz_le w.b2; have := nz_le w.b3
  unfold nzw Word.wt at *; split <;> omega

theorem nzw_pos {w : Word} (h : 0 < w.wt) : nzw w = 1 := by unfold nzw; split <;> omega

theorem State.wt_le_four_ac (s : State) : s.wt ≤ 4 * s.ac := by
  have := wt_le_four_nzw s.c0; have := wt_le_four_nzw s.c1
  have := wt_le_four_nzw s.c2; have := wt_le_four_nzw s.c3
  unfold State.wt State.ac; omega

theorem State.ac_le_wt (s : State) : s.ac ≤ s.wt := by
  have := nzw_le_wt s.c0; have := nzw_le_wt s.c1; have := nzw_le_wt s.c2; have := nzw_le_wt s.c3
  unfold State.wt State.ac; omega

theorem State.col_pos {s : State} (h : 0 < s.wt) :
    0 < s.c0.wt ∨ 0 < s.c1.wt ∨ 0 < s.c2.wt ∨ 0 < s.c3.wt := by
  unfold State.wt at h; omega

/-! ## Four rounds -/

/-- The counting at the heart of the four-round bound, over abstract differences `Dᵢ` (round inputs) and
`Mᵢ` (what enters `MixColumns` in round `i + 1`). Kept apart from the cipher so that the arithmetic
never has to look inside a round. -/
theorem four_rounds_count (D0 D1 D2 D3 M0 M1 M2 : State)
    (h01 : 5 * M0.ac ≤ D0.wt + D1.wt) (h23 : 5 * M2.ac ≤ D2.wt + D3.wt)
    (hx : 0 < D0.wt) (hw0 : M0.wt = D0.wt) (hw1 : M1.wt = D1.wt) (hac1 : D1.ac = M0.ac)
    (hle : M1.c0.wt ≤ D1.ac ∧ M1.c1.wt ≤ D1.ac ∧ M1.c2.wt ≤ D1.ac ∧ M1.c3.wt ≤ D1.ac)
    (hbr : 5 * nzw M1.c0 ≤ M1.c0.wt + D2.c0.wt ∧ 5 * nzw M1.c1 ≤ M1.c1.wt + D2.c1.wt ∧
      5 * nzw M1.c2 ≤ M1.c2.wt + D2.c2.wt ∧ 5 * nzw M1.c3 ≤ M1.c3.wt + D2.c3.wt)
    (hge : D2.c0.wt ≤ M2.ac ∧ D2.c1.wt ≤ M2.ac ∧ D2.c2.wt ≤ M2.ac ∧ D2.c3.wt ≤ M2.ac) :
    25 ≤ D0.wt + D1.wt + D2.wt + D3.wt := by
  -- round 1 has an active column, and so round 2's `MixColumns` input is nonzero
  have a0 : 0 < M0.ac := by have := State.wt_le_four_ac M0; omega
  have m1 : 0 < M1.wt := by have := State.ac_le_wt D1; omega
  -- in round 2, an active column carries at most `M0.ac` bytes in and at least `5 - M0.ac` out
  have key : 5 ≤ M0.ac + M2.ac := by
    rw [← hac1] at *
    obtain ⟨l0, l1, l2, l3⟩ := hle
    obtain ⟨b0, b1, b2, b3⟩ := hbr
    obtain ⟨g0, g1, g2, g3⟩ := hge
    rcases State.col_pos m1 with p | p | p | p
    · rw [nzw_pos p] at b0; omega
    · rw [nzw_pos p] at b1; omega
    · rw [nzw_pos p] at b2; omega
    · rw [nzw_pos p] at b3; omega
  omega

theorem wt_pos_of_ne {x y : State} (h : x ≠ y) : 0 < (x ^^^ y).wt := by
  rcases Nat.eq_zero_or_pos (x ^^^ y).wt with h0 | h0
  · exfalso; apply h
    obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := x
    obtain ⟨⟨e0, e1, e2, e3⟩, ⟨f0, f1, f2, f3⟩, ⟨g0, g1, g2, g3⟩, ⟨h0', h1, h2, h3⟩⟩ := y
    simp only [State.wt, State.xor_def, Nat.add_eq_zero_iff, Word.wt_eq_zero, Word.xor_def,
      Word.zero_def, Word.mk.injEq, UInt8.xor_eq_zero_iff] at h0
    simp [h0]
  · exact h0

/-- **The wide-trail bound.** Two different blocks `x ≠ y` go through four rounds' worth of S-boxes:
the inputs of rounds 1 to 4 are `x`, `R₁ x`, `R₂ (R₁ x)`, `R₃ (R₂ (R₁ x))`, where `Rᵢ` is a full round
under any round key `kᵢ`. Across those four layers, at least 25 S-boxes see different inputs. -/
theorem four_rounds_active (k1 k2 k3 x y : State) (h : x ≠ y) :
    25 ≤ (x ^^^ y).wt + (aesRound k1 x ^^^ aesRound k1 y).wt +
      (aesRound k2 (aesRound k1 x) ^^^ aesRound k2 (aesRound k1 y)).wt +
      (aesRound k3 (aesRound k2 (aesRound k1 x)) ^^^ aesRound k3 (aesRound k2 (aesRound k1 y))).wt :=
  four_rounds_count _ _ _ _ (mcIn x y) (mcIn (aesRound k1 x) (aesRound k1 y))
    (mcIn (aesRound k2 (aesRound k1 x)) (aesRound k2 (aesRound k1 y)))
    (two_rounds k1 x y) (two_rounds k3 _ _) (wt_pos_of_ne h) (wt_mcIn x y) (wt_mcIn _ _)
    (ac_aesRound_xor k1 x y) (wt_mcIn_col_le _ _) (branch_round_cols k2 _ _) (ac_mcIn_ge _ _)

/-- The same, for any four consecutive rounds of AES-256 encryption under any key schedule. -/
theorem cipherRounds_four_active (rk : Nat → State) (r : Nat) (x y : State) (h : x ≠ y) :
    25 ≤ (x ^^^ y).wt + (cipherRounds rk 1 r x ^^^ cipherRounds rk 1 r y).wt +
      (cipherRounds rk 2 r x ^^^ cipherRounds rk 2 r y).wt +
      (cipherRounds rk 3 r x ^^^ cipherRounds rk 3 r y).wt :=
  four_rounds_active (rk r) (rk (r + 1)) (rk (r + 2)) x y h

end AES
