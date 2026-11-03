import SingularValueBounds.KL.Upper.RoundedAlgorithmSoundness

/-!
Uniform rational rounding inequalities and nonnegative Taylor terms.
The retained exponential algorithms instantiate the generic transcript lemmas
at the order and precision needed by their mathematical bounds.
-/

open scoped BigOperators
namespace SingularValueBounds.KL.Certificates

lemma roundingScale_pos : 0 < roundingScale := by norm_num [roundingScale]

lemma roundDownQ_le (x : ℚ) : roundDownQ x ≤ x := by
  rw [roundDownQ, div_le_iff₀ roundingScale_pos]
  exact Int.floor_le _

lemma le_roundUpQ (x : ℚ) : x ≤ roundUpQ x := by
  rw [roundUpQ, le_div_iff₀ roundingScale_pos]
  have h := Int.floor_le (-(x*roundingScale))
  linarith

lemma roundDownQ_nonneg {x : ℚ} (hx : 0 ≤ x) : 0 ≤ roundDownQ x := by
  unfold roundDownQ
  apply div_nonneg _ roundingScale_pos.le
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hx roundingScale_pos.le)

lemma roundUpQ_nonpos {x : ℚ} (hx : x ≤ 0) : roundUpQ x ≤ 0 := by
  unfold roundUpQ
  apply div_nonpos_of_nonpos_of_nonneg _ roundingScale_pos.le
  have h : (0:ℚ) ≤ (⌊-(x*roundingScale)⌋ : ℤ) := by
    exact_mod_cast Int.floor_nonneg.mpr (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hx roundingScale_pos.le))
  linarith

lemma expTermLowerQ_nonneg {x : ℚ} (hx : 0 ≤ x) (j : ℕ) : 0 ≤ expTermLowerQ x j := by
  induction j with
  | zero => change (0 : ℚ) ≤ 1; norm_num
  | succ j ih =>
    exact roundDownQ_nonneg (div_nonneg (mul_nonneg ih hx) (by positivity))

end SingularValueBounds.KL.Certificates
