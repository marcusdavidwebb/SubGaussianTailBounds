import Mathlib

/-!
# Exact Chernoff optimization for the spectral exponential bounds

Both signs use the same parameter `(s - √m) / (v s)`. In particular, the
rational Laplace estimate is applied directly at the square threshold.
-/

open MeasureTheory ProbabilityTheory

namespace SingularValueBounds

noncomputable section

/-- The common cancellation for either spectral edge. -/
theorem spectral_chernoff_exponent {m v s : ℝ}
    (hm : 0 < m) (hv : 0 < v) (hs : 0 < s) :
    let θ := (s - Real.sqrt m) / (v * s);
    -θ * s ^ 2 + m * θ / (1 - v * θ) =
      -(s - Real.sqrt m) ^ 2 / v := by
  have hr : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hr2 := Real.sq_sqrt hm.le
  dsimp only
  have hd : 1 - v * ((s - Real.sqrt m) / (v * s)) = Real.sqrt m / s := by
    field_simp
    ring
  rw [hd]
  generalize ha : Real.sqrt m = a at *
  rw [← hr2]
  field_simp
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Lower Chernoff estimate for the direct spectral exponential bound. -/
theorem spectral_lower_tail_of_mgf [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) {m v s : ℝ} (hm : 0 < m) (hv : 0 < v)
    (hs : 0 < s) (hsroot : s < Real.sqrt m)
    (hint : ∀ θ : ℝ, θ < 0 → Integrable (fun ω => Real.exp (θ * Y ω)) μ)
    (hmgf : ∀ θ : ℝ, θ < 0 →
      (∫ ω, Real.exp (θ * Y ω) ∂μ) ≤
        Real.exp (m * θ / (1 - v * θ))) :
    μ.real {ω | Y ω ≤ s ^ 2} ≤ Real.exp (-(s - Real.sqrt m) ^ 2 / v) := by
  let θ := (s - Real.sqrt m) / (v * s)
  have hθ : θ < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hsroot) (mul_pos hv hs)
  have hmarkov := measure_le_le_exp_mul_mgf (μ := μ) (X := Y)
    (s ^ 2) hθ.le (hint θ hθ)
  calc
    μ.real {ω | Y ω ≤ s ^ 2} ≤
        Real.exp (-θ * (s ^ 2)) * (∫ ω, Real.exp (θ * Y ω) ∂μ) := hmarkov
    _ ≤ Real.exp (-θ * (s ^ 2)) *
        Real.exp (m * θ / (1 - v * θ)) :=
      mul_le_mul_of_nonneg_left (hmgf θ hθ) (Real.exp_nonneg _)
    _ = Real.exp (-(s - Real.sqrt m) ^ 2 / v) := by
      rw [← Real.exp_add, spectral_chernoff_exponent hm hv hs]

/-- Upper Chernoff estimate for the same rational Laplace bound. -/
theorem spectral_upper_tail_of_mgf [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) {m v s : ℝ} (hm : 0 < m) (hv : 0 < v)
    (hs : 0 < s) (hsroot : Real.sqrt m < s)
    (hint : ∀ θ : ℝ, 0 < θ → θ < 1 / v →
      Integrable (fun ω => Real.exp (θ * Y ω)) μ)
    (hmgf : ∀ θ : ℝ, 0 < θ → θ < 1 / v →
      (∫ ω, Real.exp (θ * Y ω) ∂μ) ≤
        Real.exp (m * θ / (1 - v * θ))) :
    μ.real {ω | s ^ 2 ≤ Y ω} ≤ Real.exp (-(s - Real.sqrt m) ^ 2 / v) := by
  let θ := (s - Real.sqrt m) / (v * s)
  have hθ : 0 < θ := div_pos (sub_pos.mpr hsroot) (mul_pos hv hs)
  have hθv : θ < 1 / v := by
    apply (div_lt_div_iff₀ (mul_pos hv hs) hv).2
    have hr := Real.sqrt_pos.2 hm
    nlinarith [mul_pos hv hr]
  have hmarkov := measure_ge_le_exp_mul_mgf (μ := μ) (X := Y)
    (s ^ 2) hθ.le (hint θ hθ hθv)
  calc
    μ.real {ω | s ^ 2 ≤ Y ω} ≤
        Real.exp (-θ * (s ^ 2)) * (∫ ω, Real.exp (θ * Y ω) ∂μ) := hmarkov
    _ ≤ Real.exp (-θ * (s ^ 2)) *
        Real.exp (m * θ / (1 - v * θ)) :=
      mul_le_mul_of_nonneg_left (hmgf θ hθ hθv) (Real.exp_nonneg _)
    _ = Real.exp (-(s - Real.sqrt m) ^ 2 / v) := by
      rw [← Real.exp_add, spectral_chernoff_exponent hm hv hs]

/-- The paper's lower square-root confidence threshold, with `s > 0`.
The zero final singular-value target is handled later using `d > D`. -/
theorem spectral_lower_sqrt_tail [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) {m b : ℝ} (hm : 0 < m) (hb : 0 < b)
    (hint : ∀ θ : ℝ, θ < 0 → Integrable (fun ω => Real.exp (θ * Y ω)) μ)
    (hmgf : ∀ θ : ℝ, θ < 0 →
      (∫ ω, Real.exp (θ * Y ω) ∂μ) ≤
        Real.exp (m * θ / (1 - (2 * b ^ 2) * θ)))
    {t : ℝ} (ht : 0 < t) (hs : 0 < Real.sqrt m - b * t) :
    μ.real {ω | Y ω ≤ (Real.sqrt m - b * t) ^ 2} ≤
      Real.exp (-t ^ 2 / 2) := by
  have hsr : Real.sqrt m - b * t < Real.sqrt m := by nlinarith
  have h := spectral_lower_tail_of_mgf Y hm (by positivity : 0 < 2 * b ^ 2)
    hs hsr hint hmgf
  have he : -(Real.sqrt m - b * t - Real.sqrt m) ^ 2 / (2 * b ^ 2) = -t ^ 2 / 2 := by
    field_simp
    ring
  simpa only [he] using h

/-- The upper square-root confidence threshold. -/
theorem spectral_upper_sqrt_tail [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) {m b : ℝ} (hm : 0 < m) (hb : 0 < b)
    (hint : ∀ θ : ℝ, 0 < θ → θ < 1 / (2 * b ^ 2) →
      Integrable (fun ω => Real.exp (θ * Y ω)) μ)
    (hmgf : ∀ θ : ℝ, 0 < θ → θ < 1 / (2 * b ^ 2) →
      (∫ ω, Real.exp (θ * Y ω) ∂μ) ≤
        Real.exp (m * θ / (1 - (2 * b ^ 2) * θ)))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (Real.sqrt m + b * t) ^ 2 ≤ Y ω} ≤
      Real.exp (-t ^ 2 / 2) := by
  have hr := Real.sqrt_pos.2 hm
  have hs : 0 < Real.sqrt m + b * t := by positivity
  have hsr : Real.sqrt m < Real.sqrt m + b * t := by nlinarith
  have h := spectral_upper_tail_of_mgf Y hm (by positivity : 0 < 2 * b ^ 2)
    hs hsr hint hmgf
  have he : -(Real.sqrt m + b * t - Real.sqrt m) ^ 2 / (2 * b ^ 2) = -t ^ 2 / 2 := by
    field_simp
    ring
  simpa only [he] using h

end
end SingularValueBounds
