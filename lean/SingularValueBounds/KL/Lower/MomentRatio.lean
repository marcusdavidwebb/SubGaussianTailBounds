import SingularValueBounds.KL.Lower.RealMoments
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The scalar real-moment/exponential comparison in S1.4, including its
continuous exponent range. The finite Taylor initial condition is separate. -/
open Set MeasureTheory
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1000000

theorem exponential_secant {c y : ℝ} (hc : 0 < c) (hy : y ∈ Icc (0:ℝ) c) :
    Real.exp (-y) ≤ 1-(1-Real.exp (-c))*y/c := by
  have h := convexOn_exp.2 (mem_univ (0:ℝ)) (mem_univ (-c))
    (sub_nonneg.mpr ((div_le_one hc).2 hy.2)) (div_nonneg hy.1 hc.le)
    (show 1-y/c+y/c = (1:ℝ) by ring)
  have he : (1-y/c)*(0:ℝ)+(y/c)*(-c) = -y := by field_simp <;> ring
  simp only [smul_eq_mul,he,Real.exp_zero,mul_one] at h
  convert! h using 1 <;> ring

theorem real_power_exponential_ratio_bound {p c : ℝ} (hp : 1 < p)
    (hc : 0 < c) (hroot : c ≤ p*(1-Real.exp (-c))) {y : ℝ} (hy : 0 ≤ y) :
    y^p/(Real.exp y-1) ≤ (p^p*Real.exp (-p))/(1-Real.exp (-c)) := by
  let f : ℝ → ℝ := fun x => x^p/(Real.exp x-1)
  have hden : 0 < 1-Real.exp (-c) := by
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
    linarith
  have hlarge (x : ℝ) (hx : c ≤ x) : f x ≤ (p^p*Real.exp (-p))/(1-Real.exp (-c)) := by
    have hx0 : 0 < x := hc.trans_le hx
    have hd : 0 < 1-Real.exp (-x) := by
      have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx0)
      linarith
    have he : f x = x^p*Real.exp (-x)/(1-Real.exp (-x)) := by
      dsimp [f]
      rw [Real.exp_neg]
      field_simp
    rw [he]
    exact div_le_div₀ (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ p) _) (Real.exp_pos _).le)
      (rpow_mul_exp_neg_le (by linarith) hx0.le) hden
      (by nlinarith [Real.exp_le_exp.mpr (neg_le_neg hx)])
  by_cases hy0 : y = 0
  · subst y
    simp only [Real.zero_rpow (by linarith : p ≠ 0),zero_div]
    positivity
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  by_cases hcy : c ≤ y
  · exact hlarge y hcy
  have hyc : y ≤ c := (lt_of_not_ge hcy).le
  have hderiv (x : ℝ) (hx : x ∈ Ioo (0:ℝ) c) :
      HasDerivAt f ((p*x^(p-1)*(Real.exp x-1)-x^p*Real.exp x)/(Real.exp x-1)^2) x := by
    exact ((Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')).div
      ((Real.hasDerivAt_exp x).sub_const 1)
      (ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx.1))))
  have hmono : MonotoneOn f (Ioc (0:ℝ) c) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc _ _) ?_ ?_ ?_
    · intro x hx
      exact ((Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')).continuousAt.div
        ((Real.continuous_exp.continuousAt).sub continuousAt_const)
        (ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx.1)))).continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hderiv x hx).deriv]
      apply div_nonneg _ (sq_nonneg _)
      have hs := exponential_secant hc ⟨hx.1.le,hx.2.le⟩
      have hh : 0 ≤ p*(1-Real.exp (-x))-x := by
        have hm := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ p)
        have hr := mul_le_mul_of_nonneg_right hroot (div_nonneg hx.1.le hc.le)
        have hcanc : c*(x/c) = x := by field_simp
        rw [hcanc] at hr
        have hid : p*((1-Real.exp (-c))*x/c) = p*(1-Real.exp (-c))*(x/c) := by ring
        calc
          0 ≤ p*((1-Real.exp (-c))*x/c)-x := by rw [hid]; linarith
          _ ≤ p*(1-Real.exp (-x))-x := by nlinarith
      have hm := mul_nonneg hh (Real.exp_pos x).le
      have he : Real.exp (-x)*Real.exp x = 1 := by
        rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_ne_zero x)]
      have hm' : 0 ≤ p*(Real.exp x-1)-x*Real.exp x := by nlinarith [hm]
      have hrpow : x^p = x^(p-1)*x := by
        rw [Real.rpow_sub_one hx.1.ne']
        exact (div_mul_cancel₀ _ hx.1.ne').symm
      rw [hrpow]
      nlinarith [mul_nonneg (Real.rpow_nonneg hx.1.le (p-1)) hm']
  exact (hmono ⟨hypos,hyc⟩ ⟨hc,le_rfl⟩ hyc).trans (hlarge c le_rfl)

theorem moment_threshold_exponential {p : ℝ} (hp : (19:ℝ)/4 ≤ p) :
    20*p < Real.exp (p-1/20) := by
  have hbase : (95:ℝ) < Real.exp (47/10) := by
    have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 47/10) 8
    have hn : (95:ℝ) < ∑ i ∈ Finset.range 8,(47/10:ℝ)^i/(Nat.factorial i:ℝ) := by
      norm_num [Finset.sum_range_succ,Nat.factorial]
    exact hn.trans_le hs
  have ht : 0 ≤ p-19/4 := by linarith
  have he := Real.add_one_le_exp (p-19/4)
  have hid : p-1/20 = (47/10:ℝ)+(p-19/4) := by ring
  rw [hid,Real.exp_add]
  have hmul := mul_le_mul_of_nonneg_left he (Real.exp_pos (47/10)).le
  nlinarith [mul_nonneg (by linarith : 0 ≤ Real.exp (47/10)-20) ht]

theorem real_power_exponential_bound {p y : ℝ} (hp : (19:ℝ)/4 ≤ p) (hy : 0 ≤ y) :
    y^p/(Real.exp y-1) ≤
      (p^p*Real.exp (-p))/(1-Real.exp (-(p-1/20))) := by
  apply real_power_exponential_ratio_bound (by linarith) (by linarith) _ hy
  have h := moment_threshold_exponential hp
  have he : Real.exp (-(p-1/20))*Real.exp (p-1/20) = 1 := by
    rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_ne_zero _)]
  have ht : p*Real.exp (-(p-1/20)) < 1/20 := by
    have hh := mul_lt_mul_of_pos_right h (Real.exp_pos (-(p-1/20)))
    nlinarith
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem real_moment_of_exponential {T : Ω → ℝ} {p scale M : ℝ}
    (hm : Measurable T) (hT0 : ∀ ω,0 ≤ T ω) (hp : (19:ℝ)/4 ≤ p)
    (hs : 0 < scale) (hExp : Integrable (fun ω => Real.exp (T ω/scale)) μ)
    (hM : (∫ ω,Real.exp (T ω/scale) ∂μ) ≤ M) :
    Integrable (fun ω => T ω^p) μ ∧
    (∫ ω,T ω^p ∂μ) ≤ scale^p*((p^p*Real.exp (-p))/(1-Real.exp (-(p-1/20))))*(M-1) := by
  let C := scale^p*((p^p*Real.exp (-p))/(1-Real.exp (-(p-1/20))))
  have hden : 0 < 1-Real.exp (-(p-1/20)) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -(p-1/20) < 0)
    linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (ω : Ω) : T ω^p ≤ C*(Real.exp (T ω/scale)-1) := by
    by_cases hz : T ω = 0
    · simp [hz,Real.zero_rpow (by linarith : p ≠ 0)]
    have ht : 0 < T ω := lt_of_le_of_ne (hT0 ω) (Ne.symm hz)
    have h := real_power_exponential_bound hp (div_nonneg (hT0 ω) hs.le)
    have hd : 0 < Real.exp (T ω/scale)-1 := sub_pos.mpr
      (Real.one_lt_exp_iff.mpr (div_pos ht hs))
    have hh := (div_le_iff₀ hd).1 h
    have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hs.le p)
    rw [Real.div_rpow (hT0 ω) hs.le] at hm
    have hsc : scale^p*(T ω^p/scale^p) = T ω^p := by
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hs p)]
    rw [hsc] at hm
    dsimp [C]
    nlinarith
  have hdom : Integrable (fun ω => C*(Real.exp (T ω/scale)-1)) μ :=
    (hExp.sub (integrable_const 1)).const_mul C
  have hint : Integrable (fun ω => T ω^p) μ := hdom.mono' ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).measurable.comp hm).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hT0 ω) _)]
      exact hpoint ω))
  refine ⟨hint,?_⟩
  have hi := integral_mono hint hdom hpoint
  rw [integral_const_mul,integral_sub hExp (integrable_const 1),integral_const] at hi
  simp only [probReal_univ,one_smul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hM 1) hC)

end
end SingularValueBounds.KL
