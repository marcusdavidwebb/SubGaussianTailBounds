import SingularValueBounds.KL.Upper.GeneralSecondCertificates

/-! Uniform geometry and exponential signs for the upper second-moment cells. -/
namespace SingularValueBounds.KL.UpperSecond
open Certificates Certificates.NumericalCertificateConditions

theorem secondExp_nonneg {x : ℚ} (hx : -50 < x ∧ x < 50) :
    0 ≤ secondExpLowerQ x ∧ 0 ≤ secondExpUpperQ x := by
  constructor
  · unfold secondExpLowerQ
    split_ifs with hx0
    · have ht : 0 ≤ expTaylorQ 48 x := by
        unfold expTaylorQ
        exact Finset.sum_nonneg (fun _ _ => by positivity)
      unfold secondDownQ
      positivity
    · have hn : (0 : ℝ) ≤ -(x : ℝ) := by
        have h : (0 : ℚ) ≤ -x := by linarith
        exact_mod_cast h
      have hd : -(x : ℝ) < (48 : ℝ) + 2 := by
        have h : (-50 : ℝ) < x := by exact_mod_cast hx.1
        linarith
      have h := (Real.exp_pos (-(x : ℝ))).trans_le (exp_le_expTaylorUpper 48 hn hd)
      have hq : (0 : ℚ) < expTaylorUpperQ 48 (-x) := by
        have hc : (0 : ℝ) < (expTaylorUpperQ 48 (-x) : ℝ) := by
          simpa only [cast_expTaylorUpperQ, Rat.cast_neg] using h
        exact_mod_cast hc
      unfold secondDownQ
      positivity
  · have h := (Real.exp_pos (x : ℝ)).trans_le (second_exp_enclosure hx).2
    exact_mod_cast h.le

theorem secondCell_basicConditions (j : Fin 334) :
    0 ≤ secondCellDLo j ∧ secondCellDLo j ≤ secondCellDHi j ∧ secondCellDHi j < 1 ∧
    2 * secondCellDHi j < 50 ∧ 0 ≤ secondExpUpperQ (-2 * secondCellDLo j) ∧
    0 ≤ secondExpLowerQ (-2 * secondCellDHi j) := by
  have hj : (j.val : ℚ) ≤ 333 := by exact_mod_cast (show j.val ≤ 333 by omega)
  have hlo : 0 ≤ secondCellLo j := by unfold secondCellLo; positivity
  have hhi : 0 ≤ secondCellHi j := by unfold secondCellHi; positivity
  have horder : secondCellLo j ≤ secondCellHi j := by
    unfold secondCellLo secondCellHi
    linarith
  have hhi1 : secondCellHi j < 1 := by unfold secondCellHi; linarith
  have hdlo : 0 ≤ secondCellDLo j := by unfold secondCellDLo; positivity
  have hdhi : 0 ≤ secondCellDHi j := by unfold secondCellDHi; positivity
  have hdorder : secondCellDLo j ≤ secondCellDHi j := pow_le_pow_left₀ hlo horder 4
  have hdhi1 : secondCellDHi j < 1 := pow_lt_one₀ hhi hhi1 (by norm_num : 4 ≠ 0)
  exact ⟨hdlo, hdorder, hdhi1, by linarith,
    (secondExp_nonneg (x := -2 * secondCellDLo j) ⟨by linarith, by linarith⟩).2,
    (secondExp_nonneg (x := -2 * secondCellDHi j) ⟨by linarith, by linarith⟩).1⟩

end SingularValueBounds.KL.UpperSecond
