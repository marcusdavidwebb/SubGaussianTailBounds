import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Weighted entropy: finite-integrability version of Lemma S1.4

This file formalises supplementary Lemma `app:weighted-entropy`, equation
`eq:app-entropy-variational`. The proof uses the scalar exponential tangent
inequality and normalises by the exponential moment. It needs no independence
assumption and no external arithmetic certificate.

`weighted_entropy` treats integrable weighted products. For the nonnegative
quadratic applications, `weighted_entropy_of_nonneg` derives the weighted-product
integrability from finite entropy and a finite exponential moment. The convention
`0 * log 0 = 0` is built into real multiplication and Mathlib's real logarithm.
-/

open MeasureTheory

namespace SingularValueBounds.KL

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Scalar entropy--exponential inequality, including the case of zero weight. -/
theorem mul_le_mul_log_sub_add_exp {w z : ℝ} (hw : 0 ≤ w) :
    w * z ≤ w * Real.log w - w + Real.exp z := by
  by_cases hw0 : w = 0
  · subst w
    simpa using (Real.exp_pos z).le
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (z - Real.log w)) hw
    rw [Real.exp_sub, Real.exp_log hwpos] at h
    have hcancel : w * (Real.exp z / w) = Real.exp z := by
      field_simp
    rw [hcancel] at h
    nlinarith

/-- The exponential moment used in the entropy normalisation is strictly positive. -/
theorem exp_moment_pos [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hExp : Integrable (fun ω => Real.exp (Z ω)) μ) :
    0 < ∫ ω, Real.exp (Z ω) ∂μ :=
  integral_exp_pos hExp

/-- Normalisation of an exponential by its positive, finite expectation. -/
theorem normalized_exp_integral [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hExp : Integrable (fun ω => Real.exp (Z ω)) μ) :
    (∫ ω, Real.exp (Z ω) / (∫ x, Real.exp (Z x) ∂μ) ∂μ) = 1 := by
  rw [integral_div, div_self (exp_moment_pos hExp).ne']

/-- Supplementary Lemma S1.4 (`eq:app-entropy-variational`), with explicit
finite-integrability hypotheses. The weight is nonnegative almost everywhere and
has mean one. The entropy and weighted product are ordinary real Bochner
integrals; the result imposes no independence assumptions. -/
theorem weighted_entropy [IsProbabilityMeasure μ] {W Z : Ω → ℝ}
    (hW0 : ∀ᵐ ω ∂μ, 0 ≤ W ω)
    (hW : Integrable W μ)
    (hMean : (∫ ω, W ω ∂μ) = 1)
    (hEntropy : Integrable (fun ω => W ω * Real.log (W ω)) μ)
    (hWZ : Integrable (fun ω => W ω * Z ω) μ)
    (hExp : Integrable (fun ω => Real.exp (Z ω)) μ) :
    (∫ ω, W ω * Z ω ∂μ) ≤
      (∫ ω, W ω * Real.log (W ω) ∂μ) +
        Real.log (∫ ω, Real.exp (Z ω) ∂μ) := by
  let M := ∫ ω, Real.exp (Z ω) ∂μ
  have hM : 0 < M := exp_moment_pos hExp
  have hpoint : ∀ᵐ ω ∂μ,
      W ω * Z ω - W ω * Real.log M ≤
        W ω * Real.log (W ω) - W ω + Real.exp (Z ω) / M := by
    filter_upwards [hW0] with ω hw
    have h := mul_le_mul_log_sub_add_exp (z := Z ω - Real.log M) hw
    rw [Real.exp_sub, Real.exp_log hM] at h
    nlinarith
  have hIntegral := integral_mono_ae
    (hWZ.sub (hW.mul_const (Real.log M)))
    ((hEntropy.sub hW).add (hExp.div_const M)) hpoint
  change (∫ ω, W ω * Z ω - W ω * Real.log M ∂μ) ≤
    (∫ ω, W ω * Real.log (W ω) - W ω + Real.exp (Z ω) / M ∂μ) at hIntegral
  rw [integral_sub hWZ (hW.mul_const (Real.log M)), integral_mul_const,
    integral_add (f := fun ω => W ω * Real.log (W ω) - W ω)
      (hEntropy.sub hW) (hExp.div_const M),
    integral_sub hEntropy hW, integral_div, hMean] at hIntegral
  have hMoment : (∫ ω, Real.exp (Z ω) ∂μ) / M = 1 := div_self hM.ne'
  rw [hMoment, one_mul] at hIntegral
  linarith

/-- Finite entropy and an exponential moment imply integrability of `W * Z`
when `W` and `Z` are nonnegative. Thus the entropy interface for nonnegative
quadratic forms does not require a separate weighted-product assumption. -/
theorem integrable_weighted_of_nonneg {W Z : Ω → ℝ}
    (hW0 : ∀ᵐ ω ∂μ, 0 ≤ W ω)
    (hZ0 : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hW : Integrable W μ)
    (hEntropy : Integrable (fun ω => W ω * Real.log (W ω)) μ)
    (hExp : Integrable (fun ω => Real.exp (Z ω)) μ) :
    Integrable (fun ω => W ω * Z ω) μ := by
  have hZm : AEMeasurable Z μ := by
    simpa only [Real.log_exp] using hExp.aemeasurable.log
  apply ((hEntropy.sub hW).add hExp).mono'
    (hW.aestronglyMeasurable.mul hZm.aestronglyMeasurable)
  filter_upwards [hW0, hZ0] with ω hw hz
  change ‖W ω * Z ω‖ ≤ W ω * Real.log (W ω) - W ω + Real.exp (Z ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hz)]
  exact mul_le_mul_log_sub_add_exp hw

/-- Weighted entropy for nonnegative `Z`, deriving integrability of the
weighted product from the entropy and exponential-moment assumptions. -/
theorem weighted_entropy_of_nonneg [IsProbabilityMeasure μ] {W Z : Ω → ℝ}
    (hW0 : ∀ᵐ ω ∂μ, 0 ≤ W ω)
    (hZ0 : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hW : Integrable W μ)
    (hMean : (∫ ω, W ω ∂μ) = 1)
    (hEntropy : Integrable (fun ω => W ω * Real.log (W ω)) μ)
    (hExp : Integrable (fun ω => Real.exp (Z ω)) μ) :
    (∫ ω, W ω * Z ω ∂μ) ≤
      (∫ ω, W ω * Real.log (W ω) ∂μ) +
        Real.log (∫ ω, Real.exp (Z ω) ∂μ) :=
  weighted_entropy hW0 hW hMean hEntropy
    (integrable_weighted_of_nonneg hW0 hZ0 hW hEntropy hExp) hExp

end SingularValueBounds.KL
