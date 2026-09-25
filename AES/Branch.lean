import AES.Linear

/-!
# The branch number of MixColumns is 5

The branch number of a column map `M` is the least value of `wt a + wt (M a)` over nonzero columns `a`,
where `wt` counts nonzero bytes (*The Design of Rijndael*, §9.3). For `MixColumns` it is 5, the most a
4×4 map can have: a change in one byte of a column changes all four bytes of the output, a change in two
changes at least three, and so on.

A search over all 2³² columns would settle it, and is what a SAT solver does. Here it is proved instead,
in the kernel, from the algebra of `GF.lean`:

* `M` commutes with scaling a column by a nonzero `λ`, which does not change which bytes are zero. So a
  column with nonzero bytes in two places can be scaled so that the first of them is `1`, and only the
  255 values of the second remain: 6 × 255 cases for weight 2, 4 cases for weight 1.
* For weight 3 and 4, look at the output instead. If it had weight at most 1, it would be `z` times a
  unit vector, and the input would be `z` times a column of `M⁻¹`, which has four nonzero bytes.
-/

namespace AES

set_option maxHeartbeats 0

/-- `1` if the byte is nonzero. -/
def nz (b : Byte) : Nat := if b = 0 then 0 else 1

/-- The number of nonzero bytes of a column. -/
def Word.wt (w : Word) : Nat := nz w.b0 + nz w.b1 + nz w.b2 + nz w.b3

@[simp] theorem nz_zero : nz 0 = 0 := rfl
theorem nz_of_ne {b : Byte} (h : b ≠ 0) : nz b = 1 := by simp [nz, h]
theorem nz_le (b : Byte) : nz b ≤ 1 := by unfold nz; split <;> omega

theorem Word.wt_eq_zero {w : Word} : w.wt = 0 ↔ w = 0 := by
  obtain ⟨a, b, c, d⟩ := w
  simp only [wt, nz, zero_def, mk.injEq]
  split <;> split <;> split <;> split <;> simp_all

/-- Multiply every byte by `λ`. -/
def Word.scale (l : Byte) (w : Word) : Word := w.map (mul l)

theorem dot_scale (r : Word) (l : Byte) (w : Word) : dot r (w.scale l) = mul l (dot r w) := by
  simp only [dot, Word.scale, Word.map, mul_xor, mul_left_comm l]

theorem Mat.apply_scale (m : Mat) (l : Byte) (w : Word) : m.apply (w.scale l) = (m.apply w).scale l := by
  simp only [Mat.apply, dot_scale]; rfl

theorem nz_mul {l : Byte} (hl : l ≠ 0) (b : Byte) : nz (mul l b) = nz b := by
  unfold nz
  by_cases hb : b = 0
  · simp [hb, mul_zero]
  · simp [hb, mul_ne_zero hl hb]

theorem Word.wt_scale {l : Byte} (hl : l ≠ 0) (w : Word) : (w.scale l).wt = w.wt := by
  simp only [wt, scale, map, nz_mul hl]

/-! ## Columns with one or two nonzero bytes -/

/-- Scaling a column whose byte `i` is `x ≠ 0` by `x⁻¹` makes that byte `1`; written out for the ten
shapes a column of weight one or two can have. -/
theorem scale_inv_mul {x : Byte} (hx : x ≠ 0) (y : Byte) : mul x (mul (inv x) y) = y := mul_inv_mul hx y

/-- A weight-one column is a multiple of a unit vector, so its image has the weight of a column of `m`. -/
theorem wt_apply_single (m : Mat) {x : Byte} (hx : x ≠ 0) (u : Word) (hu : u.scale x = v) :
    (m.apply v).wt = (m.apply u).wt := by
  rw [← hu, Mat.apply_scale, Word.wt_scale hx]

theorem single0 (x : Byte) : (⟨1, 0, 0, 0⟩ : Word).scale x = ⟨x, 0, 0, 0⟩ := by
  simp [Word.scale, Word.map, mul_one, mul_zero]
theorem single1 (x : Byte) : (⟨0, 1, 0, 0⟩ : Word).scale x = ⟨0, x, 0, 0⟩ := by
  simp [Word.scale, Word.map, mul_one, mul_zero]
theorem single2 (x : Byte) : (⟨0, 0, 1, 0⟩ : Word).scale x = ⟨0, 0, x, 0⟩ := by
  simp [Word.scale, Word.map, mul_one, mul_zero]
theorem single3 (x : Byte) : (⟨0, 0, 0, 1⟩ : Word).scale x = ⟨0, 0, 0, x⟩ := by
  simp [Word.scale, Word.map, mul_one, mul_zero]

/-- Every column of `MixColumns` and of `InvMixColumns` has four nonzero bytes. -/
theorem mix_units : (mixMat.apply ⟨1, 0, 0, 0⟩).wt = 4 ∧ (mixMat.apply ⟨0, 1, 0, 0⟩).wt = 4 ∧
    (mixMat.apply ⟨0, 0, 1, 0⟩).wt = 4 ∧ (mixMat.apply ⟨0, 0, 0, 1⟩).wt = 4 := by decide +kernel
theorem invMix_units : (invMixMat.apply ⟨1, 0, 0, 0⟩).wt = 4 ∧ (invMixMat.apply ⟨0, 1, 0, 0⟩).wt = 4 ∧
    (invMixMat.apply ⟨0, 0, 1, 0⟩).wt = 4 ∧ (invMixMat.apply ⟨0, 0, 0, 1⟩).wt = 4 := by decide +kernel

/-- The weight-two check: with the first nonzero byte scaled to `1`, every value of the second gives an
output with at least three nonzero bytes. Six positions, 256 values each. -/
theorem mix_pairs : allBytes (fun μ => μ == 0 || (
    3 ≤ (mixMat.apply ⟨1, μ, 0, 0⟩).wt && 3 ≤ (mixMat.apply ⟨1, 0, μ, 0⟩).wt &&
    3 ≤ (mixMat.apply ⟨1, 0, 0, μ⟩).wt && 3 ≤ (mixMat.apply ⟨0, 1, μ, 0⟩).wt &&
    3 ≤ (mixMat.apply ⟨0, 1, 0, μ⟩).wt && 3 ≤ (mixMat.apply ⟨0, 0, 1, μ⟩).wt)) = true := by
  decide +kernel

theorem mix_pair_spec {μ : Byte} (h : μ ≠ 0) :
    3 ≤ (mixMat.apply ⟨1, μ, 0, 0⟩).wt ∧ 3 ≤ (mixMat.apply ⟨1, 0, μ, 0⟩).wt ∧
    3 ≤ (mixMat.apply ⟨1, 0, 0, μ⟩).wt ∧ 3 ≤ (mixMat.apply ⟨0, 1, μ, 0⟩).wt ∧
    3 ≤ (mixMat.apply ⟨0, 1, 0, μ⟩).wt ∧ 3 ≤ (mixMat.apply ⟨0, 0, 1, μ⟩).wt := by
  simpa [h, and_assoc] using allBytes_spec mix_pairs μ

/-- A column with nonzero bytes `x` and `y` in two places is `x` times one with `1` and `x⁻¹ • y`. -/
theorem pair_scale {x : Byte} (hx : x ≠ 0) (y : Byte) :
    (⟨1, mul (inv x) y, 0, 0⟩ : Word).scale x = ⟨x, y, 0, 0⟩ ∧
    (⟨1, 0, mul (inv x) y, 0⟩ : Word).scale x = ⟨x, 0, y, 0⟩ ∧
    (⟨1, 0, 0, mul (inv x) y⟩ : Word).scale x = ⟨x, 0, 0, y⟩ ∧
    (⟨0, 1, mul (inv x) y, 0⟩ : Word).scale x = ⟨0, x, y, 0⟩ ∧
    (⟨0, 1, 0, mul (inv x) y⟩ : Word).scale x = ⟨0, x, 0, y⟩ ∧
    (⟨0, 0, 1, mul (inv x) y⟩ : Word).scale x = ⟨0, 0, x, y⟩ := by
  simp [Word.scale, Word.map, mul_one, mul_zero, mul_inv_mul hx]

theorem inv_mul_ne_zero {x y : Byte} (hx : x ≠ 0) (hy : y ≠ 0) : mul (inv x) y ≠ 0 :=
  mul_ne_zero (inv_ne_zero hx) hy

/-- Columns of weight one or two: the output makes up the rest of the 5. -/
theorem branch_low (a : Word) (ha : a ≠ 0) (hw : a.wt ≤ 2) : 5 ≤ a.wt + (mixMat.apply a).wt := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨m0, m1, m2, m3⟩ := mix_units
  by_cases h0 : a0 = 0 <;> by_cases h1 : a1 = 0 <;> by_cases h2 : a2 = 0 <;> by_cases h3 : a3 = 0 <;>
    (try simp only [h0, h1, h2, h3] at ha hw ⊢) <;>
    (try simp only [Word.wt, nz_zero, nz_of_ne, h0, h1, h2, h3, ne_eq, not_false_eq_true] at hw) <;>
    (try simp only [Word.wt, nz_zero, nz_of_ne, h0, h1, h2, h3, ne_eq, not_false_eq_true]) <;>
    first
    | omega
    | exact absurd rfl ha
    | (rw [← Word.wt, wt_apply_single mixMat h0 _ (single0 a0)]; omega)
    | (rw [← Word.wt, wt_apply_single mixMat h1 _ (single1 a1)]; omega)
    | (rw [← Word.wt, wt_apply_single mixMat h2 _ (single2 a2)]; omega)
    | (rw [← Word.wt, wt_apply_single mixMat h3 _ (single3 a3)]; omega)
    | (rw [← Word.wt, ← (pair_scale h0 a1).1, Mat.apply_scale, Word.wt_scale h0]
       have := (mix_pair_spec (inv_mul_ne_zero h0 h1)).1; omega)
    | (rw [← Word.wt, ← (pair_scale h0 a2).2.1, Mat.apply_scale, Word.wt_scale h0]
       have := (mix_pair_spec (inv_mul_ne_zero h0 h2)).2.1; omega)
    | (rw [← Word.wt, ← (pair_scale h0 a3).2.2.1, Mat.apply_scale, Word.wt_scale h0]
       have := (mix_pair_spec (inv_mul_ne_zero h0 h3)).2.2.1; omega)
    | (rw [← Word.wt, ← (pair_scale h1 a2).2.2.2.1, Mat.apply_scale, Word.wt_scale h1]
       have := (mix_pair_spec (inv_mul_ne_zero h1 h2)).2.2.2.1; omega)
    | (rw [← Word.wt, ← (pair_scale h1 a3).2.2.2.2.1, Mat.apply_scale, Word.wt_scale h1]
       have := (mix_pair_spec (inv_mul_ne_zero h1 h3)).2.2.2.2.1; omega)
    | (rw [← Word.wt, ← (pair_scale h2 a3).2.2.2.2.2, Mat.apply_scale, Word.wt_scale h2]
       have := (mix_pair_spec (inv_mul_ne_zero h2 h3)).2.2.2.2.2; omega)

/-- A column of weight one is sent by `m` to a multiple of one of `m`'s columns. -/
theorem wt_apply_of_wt_one (m : Mat)
    (hm : (m.apply ⟨1, 0, 0, 0⟩).wt = 4 ∧ (m.apply ⟨0, 1, 0, 0⟩).wt = 4 ∧
      (m.apply ⟨0, 0, 1, 0⟩).wt = 4 ∧ (m.apply ⟨0, 0, 0, 1⟩).wt = 4)
    (b : Word) (hb : b.wt = 1) : (m.apply b).wt = 4 := by
  obtain ⟨m0, m1, m2, m3⟩ := hm
  obtain ⟨a0, a1, a2, a3⟩ := b
  by_cases h0 : a0 = 0 <;> by_cases h1 : a1 = 0 <;> by_cases h2 : a2 = 0 <;> by_cases h3 : a3 = 0 <;>
    (try simp only [h0, h1, h2, h3] at hb ⊢) <;>
    (try simp only [Word.wt, nz_zero, nz_of_ne, h0, h1, h2, h3, ne_eq, not_false_eq_true] at hb) <;>
    first
    | omega
    | (rw [wt_apply_single m h0 _ (single0 a0)]; omega)
    | (rw [wt_apply_single m h1 _ (single1 a1)]; omega)
    | (rw [wt_apply_single m h2 _ (single2 a2)]; omega)
    | (rw [wt_apply_single m h3 _ (single3 a3)]; omega)

theorem invMixMat_apply_mixMat_apply (a : Word) : invMixMat.apply (mixMat.apply a) = a := by
  rw [Mat.apply_apply, invMixMat_mul_mixMat, Mat.one_apply]

theorem Mat.apply_zero (m : Mat) : m.apply 0 = 0 := by
  simp [Mat.apply, dot, mul_zero]

/-- Columns of weight three or four: if the output had weight at most one, the input would be a
multiple of a column of `InvMixColumns`, which has weight four. -/
theorem branch_high (a : Word) (hw : 3 ≤ a.wt) : 5 ≤ a.wt + (mixMat.apply a).wt := by
  have hle : a.wt ≤ 4 := by
    have := nz_le a.b0; have := nz_le a.b1; have := nz_le a.b2; have := nz_le a.b3
    unfold Word.wt; omega
  rcases Nat.lt_or_ge (mixMat.apply a).wt 2 with hb | hb
  · rcases Nat.lt_or_ge (mixMat.apply a).wt 1 with hb' | hb'
    · have h0 : mixMat.apply a = 0 := Word.wt_eq_zero.mp (by omega)
      have : a = 0 := by rw [← invMixMat_apply_mixMat_apply a, h0, Mat.apply_zero]
      subst this; simp [Word.wt] at hw
    · have := wt_apply_of_wt_one invMixMat invMix_units _ (by omega : (mixMat.apply a).wt = 1)
      rw [invMixMat_apply_mixMat_apply] at this
      omega
  · omega

/-! ## The branch number -/

/-- **The branch number of `MixColumns` is at least 5**: a nonzero column and its image have at least
five nonzero bytes between them. -/
theorem branch_mixColumn (a : Word) (ha : a ≠ 0) : 5 ≤ a.wt + (mixColumn a).wt := by
  rw [mixColumn_eq]
  rcases Nat.lt_or_ge a.wt 3 with h | h
  · exact branch_low a ha (by omega)
  · exact branch_high a h

/-- **and exactly 5**: one changed byte changes all four. -/
theorem branch_mixColumn_tight : ∃ a : Word, a ≠ 0 ∧ a.wt + (mixColumn a).wt = 5 :=
  ⟨⟨1, 0, 0, 0⟩, by decide, by decide +kernel⟩

/-- The same for differences: two different columns, and their images, differ in at least five bytes
between them. This is the form the wide-trail argument uses. -/
theorem branch_mixColumn_diff {a b : Word} (h : a ≠ b) :
    5 ≤ (a ^^^ b).wt + (mixColumn a ^^^ mixColumn b).wt := by
  rw [← mixColumn_xor]
  apply branch_mixColumn
  intro h'
  apply h
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp only [Word.xor_def, Word.zero_def, Word.mk.injEq, UInt8.xor_eq_zero_iff] at h'
  simp [h']

/-- `InvMixColumns` has branch number 5 too. -/
theorem branch_invMixColumn (a : Word) (ha : a ≠ 0) : 5 ≤ a.wt + (invMixColumn a).wt := by
  have hc : invMixColumn a ≠ 0 := by
    intro h; apply ha; rw [← mixColumn_invMixColumn a, h, mixColumn_eq, Mat.apply_zero]
  have := branch_mixColumn _ hc
  rw [mixColumn_invMixColumn] at this
  omega

end AES
