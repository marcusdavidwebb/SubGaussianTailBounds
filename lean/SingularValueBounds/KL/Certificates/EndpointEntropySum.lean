import Mathlib.Algebra.BigOperators.Intervals

/-! A tail-recursive integer evaluator for the finite entropy sums. -/
namespace SingularValueBounds.KL.Certificates
open scoped BigOperators

def intRangeFold (start : ℕ) : ℕ → (ℕ → ℤ) → ℤ → ℤ
  | 0, _, acc => acc
  | len + 1, f, acc => intRangeFold (start + 1) len f (acc + f start)

theorem intRangeFold_eq_sum (start len : ℕ) (f : ℕ → ℤ) (acc : ℤ) :
    intRangeFold start len f acc = acc + ∑ j ∈ Finset.Ico start (start + len), f j := by
  induction len generalizing start acc with
  | zero => simp [intRangeFold]
  | succ len ih =>
    rw [intRangeFold, ih]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : start < start + (len + 1))]
    have h : start + 1 + len = start + (len + 1) := by omega
    rw [h]
    simp only [add_assoc, add_comm (f start), add_left_comm]

theorem intRangeFold_zero_eq_sum (start stop : ℕ) (h : start ≤ stop) (f : ℕ → ℤ) :
    intRangeFold start (stop - start) f 0 = ∑ j ∈ Finset.Ico start stop, f j := by
  rw [intRangeFold_eq_sum, Nat.add_sub_of_le h, zero_add]

end SingularValueBounds.KL.Certificates
