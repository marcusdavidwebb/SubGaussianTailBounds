import SingularValueBounds.Shifts.LowerMoments

/-!
# Sharp one-row lower Laplace estimate (supplementary S1.3)

This module proves `eq:app-lower-moment-laplace` from its comparison
`T ≤ (1 + Q) Δ`. Constructing the exact matrix shift and proving that
comparison are separate tasks. All integrability conditions here are explicit.
-/

open MeasureTheory Set

namespace SingularValueBounds.KL

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The elementary rational lower bound for the negative exponential that
retains the half-unit improvement in the second-moment coefficient. -/
theorem exp_neg_pade_lower {x : ℝ} (hx : 0 ≤ x) :
    (2 - x) / (2 + x) ≤ Real.exp (-x) := by
  let f : ℝ → ℝ := fun y => (2 + y) * Real.exp (-y) - (2 - y)
  have hd (y : ℝ) : HasDerivAt f (1 - (1 + y) * Real.exp (-y)) y := by
    convert (((hasDerivAt_const y 2).add (hasDerivAt_id y)).mul
      ((hasDerivAt_id y).neg.exp)).sub
        ((hasDerivAt_const y 2).sub (hasDerivAt_id y)) using 1 <;>
      dsimp [f] <;> ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (by dsimp [f]; fun_prop)
      (fun y _ => (hd y).hasDerivWithinAt)
    intro y hy
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp y)
      (Real.exp_nonneg (-y))
    have he : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add]; simp
    rw [he] at h
    linarith
  have h := hmono (by simp) hx hx
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at h
  apply (div_le_iff₀ (by linarith : 0 < 2 + x)).2
  dsimp [f] at h
  nlinarith

/-- The sharp scalar rational-to-exponential step, valid for every positive
Laplace parameter, without a small-parameter restriction. -/
theorem lower_laplace_rational_bound {m2 ℓ : ℝ} (hm2 : 1 ≤ m2) (hℓ : 0 ≤ ℓ) :
    1 - ℓ / (1 + m2 * ℓ) ≤
      Real.exp (-ℓ / (1 + (m2 - 1 / 2) * ℓ)) := by
  let d := 1 + (m2 - 1 / 2) * ℓ
  have hd : 0 < d := by
    have hm : 0 ≤ m2 - 1 / 2 := by linarith
    dsimp [d]; positivity
  have hD : 0 < 1 + m2 * ℓ := by positivity
  have hp := exp_neg_pade_lower (div_nonneg hℓ hd.le)
  have hid : (2 - ℓ / d) / (2 + ℓ / d) = 1 - ℓ / (1 + m2 * ℓ) := by
    have h2 : 2 + ℓ / d ≠ 0 := ne_of_gt (by positivity)
    field_simp [hd.ne', hD.ne', h2]
    dsimp [d]
    ring
  rw [hid] at hp
  simpa only [neg_div] using hp

/-- Unit first moment forces the usual lower bound on the second moment. -/
theorem lower_one_le_second [IsProbabilityMeasure μ] {T : Ω → ℝ}
    (hT : Integrable T μ) (hT2 : Integrable (fun ω => T ω ^ 2) μ)
    (hmean : (∫ ω, T ω ∂μ) = 1) : 1 ≤ ∫ ω, T ω ^ 2 ∂μ := by
  have hmem : MemLp T 2 μ :=
    (memLp_two_iff_integrable_sq hT.aestronglyMeasurable).2 hT2
  have hc := integral_mul_sq_le hmem (memLp_const (1 : ℝ))
  simpa [hmean] using hc

/-- Weighted Cauchy--Schwarz proves the first, rational bound in
`eq:app-lower-moment-laplace`. Measurability of `Δ` suffices for its
exponential integrability because `Δ` is nonnegative. -/
theorem lower_laplace_rational [IsProbabilityMeasure μ]
    {T Q Δ : Ω → ℝ} {b m2 ℓ : ℝ}
    (hT : Integrable T μ) (hT2 : Integrable (fun ω => T ω ^ 2) μ)
    (hTQ : Integrable (fun ω => T ω * Q ω) μ)
    (hQ : AEMeasurable Q μ) (hΔ : AEMeasurable Δ μ)
    (hT0 : ∀ ω, 0 ≤ T ω) (hQ0 : ∀ ω, 0 ≤ Q ω)
    (hΔ0 : ∀ ω, 0 ≤ Δ ω)
    (hmean : (∫ ω, T ω ∂μ) = 1)
    (hsecond : (∫ ω, T ω ^ 2 ∂μ) ≤ m2)
    (hcost : (∫ ω, T ω * Q ω ∂μ) ≤ b)
    (hcomparison : ∀ ω, T ω ≤ (1 + Q ω) * Δ ω)
    (hℓ : 0 ≤ ℓ) :
    Integrable (fun ω => Real.exp (-ℓ * (1 + b) * Δ ω)) μ ∧
      (∫ ω, Real.exp (-ℓ * (1 + b) * Δ ω) ∂μ) ≤
        1 - ℓ / (1 + m2 * ℓ) := by
  have hb : 0 ≤ b := (integral_nonneg (fun ω => mul_nonneg (hT0 ω) (hQ0 ω))).trans hcost
  have hm2 : 1 ≤ m2 := (lower_one_le_second hT hT2 hmean).trans hsecond
  let s := ℓ * (1 + b)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  let D : Ω → ℝ := fun ω => 1 + Q ω + s * T ω
  have hD : ∀ ω, 0 < D ω := fun ω => by
    dsimp [D]; have := hQ0 ω; have := hT0 ω; positivity
  have hdiv : Integrable (fun ω => T ω / D ω) μ := by
    apply hT.mono' ((hT.aemeasurable.div
      ((aemeasurable_const.add hQ).add (hT.aemeasurable.const_mul s))).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hT0 ω) (hD ω).le)]
    apply div_le_self (hT0 ω)
    dsimp [D]; have := hQ0 ω; have := mul_nonneg hs (hT0 ω); linarith
  have hratio := current_shift_mean_lower hT hT2 hTQ hQ hT0 hQ0
    (by norm_num : (0 : ℝ) < 1) hs (by linarith : 0 ≤ m2) hb hmean hsecond hcost
  change 1 / (1 + b + s * m2) ≤ ∫ ω, T ω / D ω ∂μ at hratio
  have hexp : Integrable (fun ω => Real.exp (-s * Δ ω)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.continuous_exp.comp_aestronglyMeasurable
        (hΔ.aestronglyMeasurable.const_mul (-s)))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (hΔ0 ω)
  have hp (ω : Ω) : Real.exp (-s * Δ ω) ≤ 1 - s * (T ω / D ω) := by
    have hq : 0 < 1 + Q ω := by have := hQ0 ω; linarith
    have hrecip : Real.exp (-s * Δ ω) ≤ 1 / (1 + s * Δ ω) := by
      have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (s * Δ ω))
        (Real.exp_nonneg (-s * Δ ω))
      have hid : Real.exp (s * Δ ω) * Real.exp (-s * Δ ω) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      rw [hid] at he
      apply (le_div_iff₀ (by have := hΔ0 ω; positivity : 0 < 1 + s * Δ ω)).2
      nlinarith
    apply hrecip.trans
    apply (div_le_iff₀ (by have := hΔ0 ω; positivity : 0 < 1 + s * Δ ω)).2
    apply (le_of_sub_nonneg ?_)
    have hc := mul_nonneg hs (sub_nonneg.mpr (hcomparison ω))
    have hid : (1 - s * (T ω / D ω)) * (1 + s * Δ ω) - 1 =
        s * ((1 + Q ω) * Δ ω - T ω) / D ω := by
      field_simp [(hD ω).ne']; dsimp [D]; ring
    rw [hid]
    exact div_nonneg hc (hD ω).le
  have hi := integral_mono hexp ((integrable_const 1).sub (hdiv.const_mul s)) hp
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_const 1) (hdiv.const_mul s), integral_const_mul] at hi
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi
  have hr := mul_le_mul_of_nonneg_left hratio hs
  have hid : s * (1 / (1 + b + s * m2)) = ℓ / (1 + m2 * ℓ) := by
    have hb1 : 1 + b ≠ 0 := by positivity
    have hden : 1 + m2 * ℓ ≠ 0 := by positivity
    have hden2 : 1 + b + s * m2 ≠ 0 := by positivity
    field_simp [hden, hden2]
    dsimp [s]; ring
  rw [hid] at hr
  constructor
  · simpa [s, neg_mul] using hexp
  · simpa [s, neg_mul] using hi.trans (sub_le_sub_left hr 1)

/-- The complete one-row estimate `eq:app-lower-moment-laplace`.
The matrix comparison is an input, and no independence is assumed. -/
theorem lower_laplace [IsProbabilityMeasure μ]
    {T Q Δ : Ω → ℝ} {b m2 ℓ : ℝ}
    (hT : Integrable T μ) (hT2 : Integrable (fun ω => T ω ^ 2) μ)
    (hTQ : Integrable (fun ω => T ω * Q ω) μ)
    (hQ : AEMeasurable Q μ) (hΔ : AEMeasurable Δ μ)
    (hT0 : ∀ ω, 0 ≤ T ω) (hQ0 : ∀ ω, 0 ≤ Q ω)
    (hΔ0 : ∀ ω, 0 ≤ Δ ω)
    (hmean : (∫ ω, T ω ∂μ) = 1)
    (hsecond : (∫ ω, T ω ^ 2 ∂μ) ≤ m2)
    (hcost : (∫ ω, T ω * Q ω ∂μ) ≤ b)
    (hcomparison : ∀ ω, T ω ≤ (1 + Q ω) * Δ ω)
    (hℓ : 0 ≤ ℓ) :
    Integrable (fun ω => Real.exp (-ℓ * (1 + b) * Δ ω)) μ ∧
      (∫ ω, Real.exp (-ℓ * (1 + b) * Δ ω) ∂μ) ≤
        Real.exp (-ℓ / (1 + (m2 - 1 / 2) * ℓ)) := by
  have h := lower_laplace_rational hT hT2 hTQ hQ hΔ hT0 hQ0 hΔ0
    hmean hsecond hcost hcomparison hℓ
  exact ⟨h.1, h.2.trans (lower_laplace_rational_bound
    ((lower_one_le_second hT hT2 hmean).trans hsecond) hℓ)⟩

/-- The rounded general fluctuation constant dominates the sharp coefficient. -/
theorem lower_beta_general_rounding : (499 / 100 : ℝ) < 2 * (79 / 50 : ℝ) ^ 2 := by
  norm_num

/-- The rounded unit-sub-Gaussian fluctuation constant dominates `5/2`. -/
theorem lower_beta_one_rounding : (5 / 2 : ℝ) < 2 * (28 / 25 : ℝ) ^ 2 := by
  norm_num

end
end SingularValueBounds.KL
