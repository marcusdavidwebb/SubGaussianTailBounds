import SingularValueBounds.Core.ScalarTail

open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 800000

/-- The exponential resolvent integral used in the entropy calculation. -/
def exponentialResolvent (x : ℝ) : ℝ := ∫ u in Ioi 0, Real.exp (-u) / (x + u)

private theorem exp_power_integrable (j : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ j * Real.exp (-u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (j : ℝ)) (p := 1) (b := 1)
    (by have := Nat.cast_nonneg (α := ℝ) j; linarith) (by norm_num) (by norm_num)
  simpa using h

/-- Factorial moments of the mean-one exponential density. -/
theorem exponential_factorial_moment (j : ℕ) :
    (∫ u in Ioi 0, u ^ j * Real.exp (-u)) = (j.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (j : ℝ) + 1) (by positivity) (by norm_num : (0 : ℝ) < 1)
  simpa [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using h

/-- Finiteness of the resolvent integral at every positive argument. -/
theorem exponentialResolvent_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / (x + u)) (Ioi 0) := by
  apply ((exp_power_integrable 0).const_mul (1 / x)).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (Real.continuous_exp.comp continuous_neg).continuousOn.div
      (continuous_const.add continuous_id).continuousOn
      (fun u hu => ne_of_gt (add_pos hx hu))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-u) / (x + u))]
    simp only [pow_zero, one_mul]
    simpa [one_div, div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_left (Real.exp_nonneg (-u)) hx (by linarith : x ≤ x + u)

private def lowerCoeff (x : ℝ) (j : ℕ) : ℝ :=
  match j with
  | 0 => -216 - 432*x - 336*x^2 - 117*x^3 - 18*x^4 - x^5
  | 1 => 432 + 336*x + 117*x^2 + 18*x^3 + x^4
  | 2 => -336 - 117*x - 18*x^2 - x^3
  | 3 => 117 + 18*x + x^2
  | 4 => -18 - x
  | _ => 1

private def upperCoeff (x : ℝ) (j : ℕ) : ℝ :=
  match j with
  | 0 => 576 + 1728*x + 1872*x^2 + 912*x^3 + 216*x^4 + 24*x^5 + x^6
  | 1 => -1728 - 1872*x - 912*x^2 - 216*x^3 - 24*x^4 - x^5
  | 2 => 1872 + 912*x + 216*x^2 + 24*x^3 + x^4
  | 3 => -912 - 216*x - 24*x^2 - x^3
  | 4 => 216 + 24*x + x^2
  | 5 => -24 - x
  | _ => 1

private theorem polynomial_integrable (c : ℕ → ℝ) (n : ℕ) :
    IntegrableOn (fun u : ℝ => ∑ j ∈ Finset.range n, c j * (u ^ j * Real.exp (-u)))
      (Ioi 0) := by
  exact integrable_finset_sum _ (fun j hj => (exp_power_integrable j).const_mul (c j))

private theorem polynomial_integral (c : ℕ → ℝ) (n : ℕ) :
    (∫ u in Ioi 0, ∑ j ∈ Finset.range n, c j * (u ^ j * Real.exp (-u))) =
      ∑ j ∈ Finset.range n, c j * (j.factorial : ℝ) := by
  rw [integral_finset_sum _ (fun j hj => (exp_power_integrable j).const_mul (c j))]
  simp_rw [integral_const_mul, exponential_factorial_moment]

/-- The first printed positive-square remainder identity. -/
theorem exponentialResolvent_lower_remainder {x : ℝ} (hx : 0 < x) :
    let D := x^3 + 9*x^2 + 18*x + 6
    exponentialResolvent x - (x^2 + 8*x + 11) / D =
      (∫ u in Ioi 0, Real.exp (-u) * (u^3 - 9*u^2 + 18*u - 6)^2 / (x + u)) / D^2 := by
  dsimp only
  let D := x^3 + 9*x^2 + 18*x + 6
  have hD : D ≠ 0 := ne_of_gt (by dsimp [D]; positivity)
  have hp : ∀ u ∈ Ioi (0 : ℝ),
      Real.exp (-u) * (u^3 - 9*u^2 + 18*u - 6)^2 / (x + u) =
      D^2 * (Real.exp (-u) / (x + u)) +
        ∑ j ∈ Finset.range 6, lowerCoeff x j * (u^j * Real.exp (-u)) := by
    intro u hu
    have hu0 : 0 < u := hu
    have hxu : x + u ≠ 0 := ne_of_gt (by linarith : 0 < x + u)
    norm_num [Finset.sum_range_succ, lowerCoeff]
    dsimp [D]
    field_simp
    <;> ring
  have hi := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hp
  rw [hi, integral_add ((exponentialResolvent_integrable hx).const_mul (D^2))
    (polynomial_integrable (lowerCoeff x) 6), integral_const_mul, polynomial_integral]
  change exponentialResolvent x - (x^2 + 8*x + 11) / D = _
  norm_num [Finset.sum_range_succ, lowerCoeff]
  dsimp [exponentialResolvent, D]
  field_simp [hx.ne', hD]
  <;> ring

/-- The second printed positive-square remainder identity. -/
theorem exponentialResolvent_upper_remainder {x : ℝ} (hx : 0 < x) :
    let D := x^3 + 12*x^2 + 36*x + 24
    (x^3 + 11*x^2 + 26*x + 6) / (x*D) - exponentialResolvent x =
      (∫ u in Ioi 0, Real.exp (-u) * u * (u^3 - 12*u^2 + 36*u - 24)^2 / (x + u)) /
        (x*D^2) := by
  dsimp only
  let D := x^3 + 12*x^2 + 36*x + 24
  have hD : D ≠ 0 := ne_of_gt (by dsimp [D]; positivity)
  have hp : ∀ u ∈ Ioi (0 : ℝ),
      Real.exp (-u) * u * (u^3 - 12*u^2 + 36*u - 24)^2 / (x + u) =
      -(x*D^2) * (Real.exp (-u) / (x + u)) +
        ∑ j ∈ Finset.range 7, upperCoeff x j * (u^j * Real.exp (-u)) := by
    intro u hu
    have hu0 : 0 < u := hu
    have hxu : x + u ≠ 0 := ne_of_gt (by linarith : 0 < x + u)
    norm_num [Finset.sum_range_succ, upperCoeff]
    dsimp [D]
    field_simp
    <;> ring
  have hi := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hp
  rw [hi, integral_add ((exponentialResolvent_integrable hx).const_mul (-(x*D^2)))
    (polynomial_integrable (upperCoeff x) 7), integral_const_mul, polynomial_integral]
  change (x^3 + 11*x^2 + 26*x + 6) / (x*D) - exponentialResolvent x = _
  norm_num [Finset.sum_range_succ, upperCoeff]
  dsimp [exponentialResolvent, D]
  field_simp [hx.ne', hD]
  <;> ring

/-- Both rational bounds, with no external arithmetic hypotheses. -/
theorem exponentialResolvent_rational_bounds {x : ℝ} (hx : 0 < x) :
    (x^2 + 8*x + 11) / (x^3 + 9*x^2 + 18*x + 6) ≤ exponentialResolvent x ∧
    exponentialResolvent x ≤
      (x^3 + 11*x^2 + 26*x + 6) / (x*(x^3 + 12*x^2 + 36*x + 24)) := by
  constructor
  · have h := exponentialResolvent_lower_remainder hx
    dsimp only at h
    have hn : 0 ≤ (∫ u in Ioi 0,
        Real.exp (-u) * (u^3 - 9*u^2 + 18*u - 6)^2 / (x+u)) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      positivity
    have := div_nonneg hn (sq_nonneg (x^3 + 9*x^2 + 18*x + 6))
    linarith
  · have h := exponentialResolvent_upper_remainder hx
    dsimp only at h
    have hn : 0 ≤ (∫ u in Ioi 0,
        Real.exp (-u) * u * (u^3 - 12*u^2 + 36*u - 24)^2 / (x+u)) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 ≤ u := hu.le
      positivity
    have := div_nonneg hn (show 0 ≤ x*(x^3+12*x^2+36*x+24)^2 by positivity)
    linarith
end
end SingularValueBounds.KL
