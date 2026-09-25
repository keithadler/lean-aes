/-!
# Counting with big numbers

The S-box's difference and linear tables have 65,536 entries each, and each entry counts over 256
inputs, so tabulating them one entry at a time is 16.7 million evaluations: hours in the kernel. The
kernel does have one fast operation, though: arithmetic on natural-number literals, which it performs
with GMP. So a whole row of a table is kept as one number, one base-2¹⁶ digit per entry, and adding an
entire row of indicator values is one addition.

This file proves the bookkeeping that makes that sound: a sum of numbers written in digits is the
number whose digits are the sums, and when every digit is below the base, reading the digits back gives
exactly those sums. `digitsIn` is the reader the checks use.
-/

namespace AES.Digits

/-- The base: sixteen bits per digit, far more than a count out of 256 needs. -/
def B : Nat := 65536

/-- `f i + B * f (i+1) + B² * f (i+2) + …`, `n` digits. -/
def ofDigits (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, i => Nat.add (f i) (Nat.mul B (ofDigits f n (Nat.succ i)))

/-- `g 0 + g 1 + … + g (n-1)`. -/
def sum (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.add (g n) (sum g n)

/-- Every one of the `n` lowest digits of `h` lies in `[lo, hi]`. -/
def digitsIn (lo hi : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, h => (Nat.ble lo (Nat.mod h B) && Nat.ble (Nat.mod h B) hi) && digitsIn lo hi n (Nat.div h B)

theorem ofDigits_congr {f g : Nat → Nat} {n i : Nat} (h : ∀ k, i ≤ k → k < i + n → f k = g k) :
    ofDigits f n i = ofDigits g n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [ofDigits]
    rw [h i (Nat.le_refl _) (by omega), ih (fun k hk hk' => h k (by omega) (by omega))]

theorem ofDigits_zero (n i : Nat) : ofDigits (fun _ => 0) n i = 0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [ofDigits, ih]; rfl

theorem ofDigits_add (f g : Nat → Nat) (n i : Nat) :
    ofDigits (fun k => f k + g k) n i = ofDigits f n i + ofDigits g n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [ofDigits, Nat.add_eq, Nat.mul_eq, ih, Nat.succ_eq_add_one, Nat.mul_add]
    omega

/-- A single `1` in digit `d` is `B ^ d`. -/
theorem ofDigits_single (n i d : Nat) (h : d < n) :
    ofDigits (fun k => if k = i + d then 1 else 0) n i = B ^ d := by
  induction n generalizing i d with
  | zero => omega
  | succ n ih =>
    simp only [ofDigits, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one]
    cases d with
    | zero =>
      rw [ofDigits_congr (g := fun _ => 0) (fun k hk _ => by simp; omega), ofDigits_zero]
      simp
    | succ d =>
      rw [ofDigits_congr (g := fun k => if k = (i + 1) + d then 1 else 0) (fun k _ _ => by
        congr 1; apply propext; omega), ih (i + 1) d (by omega)]
      simp [Nat.pow_succ, Nat.mul_comm]

/-- Summing numbers written in digits sums the digits. -/
theorem sum_ofDigits (g : Nat → Nat → Nat) (m n i : Nat) :
    sum (fun x => ofDigits (g x) n i) m = ofDigits (fun k => sum (fun x => g x k) m) n i := by
  induction m with
  | zero => simp only [sum]; exact (ofDigits_zero n i).symm
  | succ m ih =>
    simp only [sum, Nat.add_eq, ih]
    exact (ofDigits_add (g m) (fun k => sum (fun x => g x k) m) n i).symm

/-- Reading the digits back: if every digit is below `B`, `digitsIn` checks each of them. -/
theorem digitsIn_ofDigits {lo hi : Nat} {f : Nat → Nat} {n i : Nat} (hf : ∀ k, f k < B)
    (h : digitsIn lo hi n (ofDigits f n i) = true) : ∀ k, i ≤ k → k < i + n → lo ≤ f k ∧ f k ≤ hi := by
  induction n generalizing i with
  | zero => intro k _ _; omega
  | succ n ih =>
    have hmod : Nat.mod (ofDigits f (n + 1) i) B = f i := by
      show (f i + B * ofDigits f n (i + 1)) % B = f i
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf i)]
    have hdiv : Nat.div (ofDigits f (n + 1) i) B = ofDigits f n (i + 1) := by
      show (f i + B * ofDigits f n (i + 1)) / B = _
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < B), Nat.div_eq_of_lt (hf i), Nat.zero_add]
    simp only [digitsIn, hmod, hdiv, Bool.and_eq_true, Nat.ble_eq] at h
    intro k hk hk'
    rcases Nat.eq_or_lt_of_le hk with rfl | hk
    · exact h.1
    · exact ih h.2 k hk (by omega)

theorem sum_congr {g g' : Nat → Nat} {m : Nat} (h : ∀ x < m, g x = g' x) : sum g m = sum g' m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [sum, h m (by omega), ih (fun x hx => h x (by omega))]

/-- A sum of `0`/`1` values is at most the number of terms. -/
theorem sum_le (g : Nat → Nat) (hg : ∀ x, g x ≤ 1) (m : Nat) : sum g m ≤ m := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih => have := hg m; simp only [sum, Nat.add_eq]; omega

/-- `List.countP` over `0, …, m-1` is a `sum` of indicators. -/
theorem countP_range (p : Nat → Bool) (m : Nat) :
    (List.range m).countP p = sum (fun x => if p x then 1 else 0) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [sum, Nat.add_eq, List.countP_cons, List.countP_nil]
    omega

end AES.Digits
