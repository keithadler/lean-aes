import AES.Spec

/-!
# Columns as vectors over GF(2⁸)

`MixColumns` and `InvMixColumns` multiply each column by a 4×4 matrix. Rather than expanding
`InvMixColumns ∘ MixColumns` into sixty-four products and regrouping them by hand, this proves once that
applying two matrices in turn is applying their product, and then lets the kernel multiply the two
matrices of FIPS-197 and see the identity.
-/

namespace AES

set_option maxHeartbeats 0

/-- A 4×4 matrix over GF(2⁸), by rows. -/
structure Mat where
  /-- Row 0. -/
  r0 : Word
  /-- Row 1. -/
  r1 : Word
  /-- Row 2. -/
  r2 : Word
  /-- Row 3. -/
  r3 : Word
  deriving DecidableEq, Repr

/-- `Σₖ rₖ • wₖ`. -/
def dot (r w : Word) : Byte := mul r.b0 w.b0 ^^^ mul r.b1 w.b1 ^^^ mul r.b2 w.b2 ^^^ mul r.b3 w.b3

namespace Mat

/-- The matrix times a column. -/
def apply (m : Mat) (w : Word) : Word := ⟨dot m.r0 w, dot m.r1 w, dot m.r2 w, dot m.r3 w⟩

/-- Column 0 of a matrix. -/
def col0 (m : Mat) : Word := ⟨m.r0.b0, m.r1.b0, m.r2.b0, m.r3.b0⟩
/-- Column 1 of a matrix. -/
def col1 (m : Mat) : Word := ⟨m.r0.b1, m.r1.b1, m.r2.b1, m.r3.b1⟩
/-- Column 2 of a matrix. -/
def col2 (m : Mat) : Word := ⟨m.r0.b2, m.r1.b2, m.r2.b2, m.r3.b2⟩
/-- Column 3 of a matrix. -/
def col3 (m : Mat) : Word := ⟨m.r0.b3, m.r1.b3, m.r2.b3, m.r3.b3⟩

/-- The row vector `a` times the matrix `b`. -/
def row (a : Word) (b : Mat) : Word := ⟨dot a b.col0, dot a b.col1, dot a b.col2, dot a b.col3⟩

/-- The matrix product. -/
def mul (a b : Mat) : Mat := ⟨row a.r0 b, row a.r1 b, row a.r2 b, row a.r3 b⟩

/-- The identity matrix. -/
def one : Mat := ⟨⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩⟩

theorem dot_apply (r : Word) (b : Mat) (w : Word) : dot r (b.apply w) = dot (row r b) w := by
  obtain ⟨r0, r1, r2, r3⟩ := r
  obtain ⟨⟨a00, a01, a02, a03⟩, ⟨a10, a11, a12, a13⟩, ⟨a20, a21, a22, a23⟩, ⟨a30, a31, a32, a33⟩⟩ := b
  obtain ⟨w0, w1, w2, w3⟩ := w
  simp only [dot, apply, row, col0, col1, col2, col3, mul_xor, xor_mul, mul_assoc]
  ac_rfl

/-- Applying `b` and then `a` is applying `a * b`. -/
theorem apply_apply (a b : Mat) (w : Word) : a.apply (b.apply w) = (a.mul b).apply w := by
  simp only [mul]
  rw [apply, dot_apply, dot_apply, dot_apply, dot_apply]
  rfl

theorem one_apply (w : Word) : one.apply w = w := by
  obtain ⟨w0, w1, w2, w3⟩ := w
  simp only [apply, one, dot, one_mul, zero_mul, UInt8.xor_zero, UInt8.zero_xor]

theorem apply_xor (m : Mat) (v w : Word) : m.apply (v ^^^ w) = m.apply v ^^^ m.apply w := by
  obtain ⟨v0, v1, v2, v3⟩ := v
  obtain ⟨w0, w1, w2, w3⟩ := w
  simp only [apply, dot, Word.xor_def, mul_xor]
  congr 1 <;> ac_rfl

end Mat

/-- The matrix of `MixColumns`, eq. (5.6). -/
def mixMat : Mat := ⟨⟨2, 3, 1, 1⟩, ⟨1, 2, 3, 1⟩, ⟨1, 1, 2, 3⟩, ⟨3, 1, 1, 2⟩⟩

/-- The matrix of `InvMixColumns`, eq. (5.17). -/
def invMixMat : Mat := ⟨⟨0x0e, 0x0b, 0x0d, 0x09⟩, ⟨0x09, 0x0e, 0x0b, 0x0d⟩, ⟨0x0d, 0x09, 0x0e, 0x0b⟩,
  ⟨0x0b, 0x0d, 0x09, 0x0e⟩⟩

theorem mixColumn_eq (w : Word) : mixColumn w = mixMat.apply w := by
  simp only [mixColumn, Mat.apply, mixMat, dot, one_mul]

theorem invMixColumn_eq (w : Word) : invMixColumn w = invMixMat.apply w := rfl

/-- The two matrices of FIPS-197 are inverse to each other. The kernel multiplies them out. -/
theorem invMixMat_mul_mixMat : invMixMat.mul mixMat = Mat.one := by decide +kernel
theorem mixMat_mul_invMixMat : mixMat.mul invMixMat = Mat.one := by decide +kernel

theorem invMixColumn_mixColumn (w : Word) : invMixColumn (mixColumn w) = w := by
  rw [mixColumn_eq, invMixColumn_eq, Mat.apply_apply, invMixMat_mul_mixMat, Mat.one_apply]

theorem mixColumn_invMixColumn (w : Word) : mixColumn (invMixColumn w) = w := by
  rw [mixColumn_eq, invMixColumn_eq, Mat.apply_apply, mixMat_mul_invMixMat, Mat.one_apply]

/-- `MixColumns` is additive, so it maps differences to differences. -/
theorem mixColumn_xor (v w : Word) : mixColumn (v ^^^ w) = mixColumn v ^^^ mixColumn w := by
  simp only [mixColumn_eq, Mat.apply_xor]

end AES
