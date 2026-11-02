import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum.NatFactorial
import SingularValueBounds.Core.ScalarTail
import SingularValueBounds.Core.Constants

/-! # The mean-sensitive tail second moment in Lemma 4.1(2) -/
open MeasureTheory Set
namespace SingularValueBounds
noncomputable section

theorem scalar_tail_coefficient {K : ℝ} (hK : 1 ≤ K) :
    Real.sqrt 3 * Real.exp (-((1 / (3 * K ^ 2)) *
        (8 * K ^ 2 * logParameter K))) / (1 / (3 * K ^ 2)) ≤ 3 / 7 := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL := one_le_logParameter hK
  have hs : Real.sqrt 3 ≤ (7 / 4 : ℝ) := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have heq : K ^ 2 * Real.exp (-((8 / 3 : ℝ) * logParameter K)) =
      Real.exp (-2 - (2 / 3 : ℝ) * logParameter K) := by
    conv_lhs => lhs; rw [← Real.exp_log hK0]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp [logParameter]
    ring
  have he11 : (13 : ℝ) ≤ Real.exp (8 / 3 : ℝ) := by
    have hh := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 8 / 3 by norm_num) 6
    norm_num [Finset.sum_range_succ] at hh
    linarith
  have hneg : Real.exp (-(8 / 3 : ℝ)) ≤ (1 / 13 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right he11 (Real.exp_nonneg (-(8 / 3 : ℝ)))
    have hi : Real.exp (8 / 3 : ℝ) * Real.exp (-(8 / 3 : ℝ)) = 1 := by
      rw [← Real.exp_add]; norm_num
    rw [hi] at hh
    linarith
  have he : K ^ 2 * Real.exp (-((8 / 3 : ℝ) * logParameter K)) ≤ (1 / 13 : ℝ) := by
    rw [heq]
    exact (Real.exp_le_exp.mpr (by linarith)).trans hneg
  have hcancel : (1 / (3 * K ^ 2)) * (8 * K ^ 2 * logParameter K) =
      (8 / 3 : ℝ) * logParameter K := by field_simp [hK0.ne']
  rw [hcancel]
  have hi : Real.sqrt 3 * Real.exp (-((8 / 3 : ℝ) * logParameter K)) / (1 / (3 * K ^ 2)) =
      3 * Real.sqrt 3 * (K ^ 2 * Real.exp (-((8 / 3 : ℝ) * logParameter K))) := by
    field_simp
  rw [hi]
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 3 * Real.sqrt 3 by positivity)
  nlinarith


theorem scalar_second_truncation {y a : ℝ} (hy : 0 ≤ y) :
    y ^ 2 ≤ a * y + a * max (y - a) 0 + max (y - a) 0 ^ 2 := by
  by_cases h : a ≤ y
  · rw [max_eq_left (sub_nonneg.mpr h)]
    nlinarith
  · rw [max_eq_right (by linarith : y - a ≤ 0)]
    nlinarith [mul_nonneg hy (show 0 ≤ a - y by linarith)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Truncation converts an exponential tail into a mean-sensitive second
moment estimate. -/
theorem exponential_tail_second_le {Y : Ω → ℝ} {C r a : ℝ}
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hC : 0 ≤ C) (hr : 0 < r) (ha : 0 ≤ a)
    (htail : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < Y ω} ≤ C * Real.exp (-(r * x))) :
    Integrable (fun ω => Y ω ^ 2) μ ∧
      (∫ ω, Y ω ^ 2 ∂μ) ≤ a * (∫ ω, Y ω ∂μ) +
        (C * Real.exp (-(r * a))) * (a / r + 2 / r ^ 2) := by
  have hy := exponential_tail_moment hY hY0 hC hr htail 0
  have hy2 := exponential_tail_moment hY hY0 hC hr htail 1
  have h1 := exponential_tail_positive_part_moment hY hC hr ha htail 0
  have h2 := exponential_tail_positive_part_moment hY hC hr ha htail 1
  norm_num at hy hy2 h1 h2
  refine ⟨hy2.1, ?_⟩
  have hay := hy.1.const_mul a
  have hau := h1.1.const_mul a
  have hB : Integrable (fun ω => a * Y ω + a * max (Y ω - a) 0) μ := hay.add hau
  have hi := integral_mono hy2.1 (hB.add h2.1)
    (fun ω => scalar_second_truncation (hY0 ω))
  simp only [Pi.add_apply] at hi
  rw [integral_add hB h2.1, integral_add hay hau] at hi
  simp only [integral_const_mul] at hi
  have hb1 := mul_le_mul_of_nonneg_left h1.2 ha
  calc
    (∫ ω, Y ω ^ 2 ∂μ) ≤ a * (∫ ω, Y ω ∂μ) +
        a * ((C * Real.exp (-(r * a))) / r) +
        ((C * Real.exp (-(r * a))) * 2 / r ^ 2) := by linarith [h2.2]
    _ = _ := by ring

/-- The paper's second-moment bound, retaining the additive `3v/4`. -/
theorem scalar_tail_second_moment {Y : Ω → ℝ} {K : ℝ}
    (hK : 1 ≤ K) (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < Y ω} ≤
      Real.sqrt 3 * Real.exp (-(x / (3 * K ^ 2)))) :
    Integrable (fun ω => Y ω ^ 2) μ ∧
      (∫ ω, Y ω ^ 2 ∂μ) ≤
        (8 * K ^ 2 * logParameter K) * (∫ ω, Y ω ∂μ) + 6 * K ^ 2 * logParameter K := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL := one_le_logParameter hK
  have ht : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < Y ω} ≤
      Real.sqrt 3 * Real.exp (-((1 / (3 * K ^ 2)) * x)) := by
    intro x hx
    convert! htail x hx using 1
    congr 2
    ring
  have h := exponential_tail_second_le hY hY0 (Real.sqrt_nonneg 3)
    (show 0 < 1 / (3 * K ^ 2) by positivity)
    (show 0 ≤ 8 * K ^ 2 * logParameter K by positivity) ht
  refine ⟨h.1, ?_⟩
  have hc := scalar_tail_coefficient hK
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 8 * K ^ 2 * logParameter K + 6 * K ^ 2 by positivity)
  have heq : (Real.sqrt 3 * Real.exp (-((1 / (3 * K ^ 2)) *
        (8 * K ^ 2 * logParameter K)))) *
        ((8 * K ^ 2 * logParameter K) / (1 / (3 * K ^ 2)) +
          2 / (1 / (3 * K ^ 2)) ^ 2) =
      (Real.sqrt 3 * Real.exp (-((1 / (3 * K ^ 2)) *
        (8 * K ^ 2 * logParameter K))) / (1 / (3 * K ^ 2))) *
        (8 * K ^ 2 * logParameter K + 6 * K ^ 2) := by
    field_simp [hK0.ne']; ring
  rw [heq] at h
  have hKL := mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hL)
  nlinarith [h.2]

/-- The tail hypothesis supplies the square integrability used in the shift proof. -/
theorem scalar_tail_memLp_two {Y : Ω → ℝ} {K : ℝ}
    (hK : 1 ≤ K) (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < Y ω} ≤
      Real.sqrt 3 * Real.exp (-(x / (3 * K ^ 2)))) : MemLp Y 2 μ :=
  (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).2
    (scalar_tail_second_moment hK hY hY0 htail).1

end
end SingularValueBounds
