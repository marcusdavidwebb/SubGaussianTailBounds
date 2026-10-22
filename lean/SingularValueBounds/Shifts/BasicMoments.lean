import Mathlib

/-! # Elementary bounds and integrability for the lower shift -/

open MeasureTheory

namespace SingularValueBounds

theorem shift_nonneg (q e a η : ℝ) (hq : 0 ≤ q) (he : 0 ≤ e)
    (ha : 0 < a) (hη : 0 ≤ η) : 0 ≤ q / (a + e + η * q) := by positivity

theorem shift_le_div (q e a η : ℝ) (hq : 0 ≤ q) (he : 0 ≤ e)
    (ha : 0 < a) (hη : 0 ≤ η) : q / (a + e + η * q) ≤ q / a := by
  apply div_le_div_of_nonneg_left hq ha
  have := mul_nonneg hη hq
  linarith

theorem shift_sq_le (q e a η : ℝ) (hq : 0 ≤ q) (he : 0 ≤ e)
    (ha : 0 < a) (hη : 0 ≤ η) :
    (q / (a + e + η * q)) ^ 2 ≤ q ^ 2 / (a + η * q) ^ 2 := by
  have hbase : 0 < a + η * q := by positivity
  have hden : a + η * q ≤ a + e + η * q := by linarith
  have hle := div_le_div_of_nonneg_left hq hbase hden
  have hn := shift_nonneg q e a η hq he ha hη
  simpa only [div_pow] using pow_le_pow_left₀ hn hle 2

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Integrability of the shift and its square follows from that of `q` and
`q²`.  No boundedness assumption on the excess is required. -/
theorem shift_integrable {q e : Ω → ℝ} {a η : ℝ}
    (hq : Integrable q μ) (hq2 : Integrable (fun x => q x ^ 2) μ)
    (he : AEMeasurable e μ) (hq0 : ∀ x, 0 ≤ q x) (he0 : ∀ x, 0 ≤ e x)
    (ha : 0 < a) (hη : 0 ≤ η) :
    Integrable (fun x => q x / (a + e x + η * q x)) μ ∧
    Integrable (fun x => (q x / (a + e x + η * q x)) ^ 2) μ := by
  have hm : AEMeasurable (fun x => q x / (a + e x + η * q x)) μ :=
    hq.aemeasurable.div ((aemeasurable_const.add he).add
      (aemeasurable_const.mul hq.aemeasurable))
  constructor
  · apply (hq.div_const a).mono' hm.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (shift_nonneg _ _ _ _ (hq0 x) (he0 x) ha hη)]
    exact shift_le_div _ _ _ _ (hq0 x) (he0 x) ha hη
  · apply (hq2.div_const (a ^ 2)).mono' (hm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hle := shift_le_div _ _ _ _ (hq0 x) (he0 x) ha hη
    have hn := shift_nonneg _ _ _ _ (hq0 x) (he0 x) ha hη
    simpa only [div_pow] using pow_le_pow_left₀ hn hle 2

end Integral
end SingularValueBounds
