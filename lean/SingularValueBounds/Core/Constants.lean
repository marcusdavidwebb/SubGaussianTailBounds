import Mathlib

/-!
# The logarithmic and fourth-moment constants

The paper uses `L = log(eK)`, written as `1 + log K` here. The fourth-moment
constant is `3` at `K = 1` and `5 K² L` otherwise.
-/

namespace SingularValueBounds
noncomputable section

def logParameter (K : ℝ) : ℝ := 1 + Real.log K

def fourthMomentConstant (K : ℝ) : ℝ :=
  if K = 1 then 3 else 5 * K ^ 2 * logParameter K

theorem logParameter_one : logParameter 1 = 1 := by
  simp [logParameter]

theorem one_le_logParameter {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ logParameter K := by
  have := Real.log_nonneg hK
  dsimp [logParameter]
  linarith

theorem logParameter_eq_log_exp_mul {K : ℝ} (hK : 0 < K) :
    logParameter K = Real.log (Real.exp 1 * K) := by
  rw [Real.log_mul (Real.exp_ne_zero 1) hK.ne', Real.log_exp]
  rfl

theorem fourthMomentConstant_pos {K : ℝ} (hK : 1 ≤ K) :
    0 < fourthMomentConstant K := by
  have hL := one_le_logParameter hK
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  unfold fourthMomentConstant
  split_ifs with h
  · norm_num
  · positivity

end
end SingularValueBounds
