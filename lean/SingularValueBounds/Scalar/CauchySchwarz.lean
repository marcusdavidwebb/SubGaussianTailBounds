import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cauchy--Schwarz and the endpoint lower-shift excess

The scalar estimates below supply the moment calculations in the current
exponential shift proofs.
-/

open MeasureTheory
open scoped ENNReal

namespace SingularValueBounds

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cauchy--Schwarz for real square-integrable functions, in squared form. -/
theorem integral_mul_sq_le {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hinner : ∀ {u v : Ω → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ),
      inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂μ := by
    intro u v hu hv
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [hinner hf hg, hinner hf hf, hinner hg hg] at h
  simpa only [pow_two] using h

/-- The endpoint excess is bounded by the positive part of a
centred quadratic form `W`; the covariance term exploits isotropy. -/
theorem weighted_excess_unit [IsProbabilityMeasure μ]
    {q W e : Ω → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hq : MemLp q 2 μ) (hW : MemLp W 2 μ) (he : MemLp e 2 μ)
    (hq0 : ∀ x, 0 ≤ q x) (heW : ∀ x, e x ≤ max (W x) 0)
    (hqmean : ∫ x, q x ∂μ = 1) (hWmean : ∫ x, W x ∂μ = 0)
    (hqsecond : ∫ x, q x ^ 2 ∂μ ≤ 3)
    (hWsecond : ∫ x, W x ^ 2 ∂μ ≤ 2 * η ^ 2) :
    ∫ x, q x * e x ∂μ ≤ (7 / 3 : ℝ) * η := by
  have hqint : Integrable q μ := hq.integrable (by norm_num)
  have hWint : Integrable W μ := hW.integrable (by norm_num)
  have hqc : MemLp (fun x => q x - 1) 2 μ := hq.sub (memLp_const 1)
  have hqcsecond : ∫ x, (q x - 1) ^ 2 ∂μ ≤ 2 := by
    have hi : (∫ x, (q x - 1) ^ 2 ∂μ) = (∫ x, q x ^ 2 ∂μ) - 2 * (∫ x, q x ∂μ) + 1 := by
      calc
        (∫ x, (q x - 1) ^ 2 ∂μ) = ∫ x, q x ^ 2 - 2 * q x + 1 ∂μ := by
          congr 1
          funext x
          ring
        _ = _ := by
          rw [integral_add (show Integrable (fun x => q x ^ 2 - 2 * q x) μ from hq.integrable_sq.sub (hqint.const_mul 2)) (integrable_const 1),
            integral_sub hq.integrable_sq (hqint.const_mul 2)]
          simp [integral_const_mul]
    rw [hi, hqmean]
    linarith
  have hqa : MemLp (fun x => |W x|) 2 μ := by simpa only [Real.norm_eq_abs] using hW.norm
  have habssecond : (∫ x, |W x| ^ 2 ∂μ) = ∫ x, W x ^ 2 ∂μ := by simp
  have hfirst : (∫ x, q x * |W x| ∂μ) ≤ Real.sqrt 6 * η := by
    have hc := integral_mul_sq_le hq hqa
    rw [habssecond] at hc
    have hw0 : 0 ≤ ∫ x, W x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    have hm := mul_le_mul hqsecond hWsecond hw0 (by norm_num : (0 : ℝ) ≤ 3)
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    have hs0 := Real.sqrt_nonneg (6 : ℝ)
    have ht : 0 ≤ Real.sqrt 6 * η := mul_nonneg hs0 hη
    have ht2 : (Real.sqrt 6 * η) ^ 2 = 6 * η ^ 2 := by rw [mul_pow, hs]
    nlinarith
  have hsecond : (∫ x, (q x - 1) * W x ∂μ) ≤ 2 * η := by
    have hc := integral_mul_sq_le hqc hW
    have hw0 : 0 ≤ ∫ x, W x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    have hm := mul_le_mul hqcsecond hWsecond hw0 (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hi : (∫ x, q x * e x ∂μ) ≤
      ((∫ x, q x * |W x| ∂μ) + (∫ x, (q x - 1) * W x ∂μ)) / 2 := by
    have hmajor : Integrable (fun x => (q x * |W x| + (q x - 1) * W x + W x) / 2) μ :=
      (((hq.integrable_mul hqa).add (hqc.integrable_mul hW)).add hWint).div_const 2
    have hi := integral_mono (hq.integrable_mul he) hmajor (fun x => by
      have h := mul_le_mul_of_nonneg_left (heW x) (hq0 x)
      have hmax : max (W x) 0 = (|W x| + W x) / 2 := by
        by_cases hw : 0 ≤ W x
        · rw [max_eq_left hw, abs_of_nonneg hw]; ring
        · rw [max_eq_right (le_of_not_ge hw), abs_of_nonpos (le_of_not_ge hw)]; ring
      rw [hmax] at h
      dsimp only [Pi.mul_apply]
      nlinarith only [h])
    rw [integral_div, integral_add (show Integrable (fun x => q x * |W x| + (q x - 1) * W x) μ from (hq.integrable_mul hqa).add (hqc.integrable_mul hW)) hWint,
      integral_add (show Integrable (fun x => q x * |W x|) μ from hq.integrable_mul hqa) (show Integrable (fun x => (q x - 1) * W x) μ from hqc.integrable_mul hW), hWmean, add_zero] at hi
    exact hi
  have hnumeric : (Real.sqrt 6 + 2) / 2 ≤ (7 / 3 : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    have hn := Real.sqrt_nonneg (6 : ℝ)
    nlinarith
  have hn := mul_le_mul_of_nonneg_right hnumeric hη
  nlinarith

end SingularValueBounds
