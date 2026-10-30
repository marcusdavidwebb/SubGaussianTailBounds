import SingularValueBounds.KL.Lower.Moments
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Sharpened cosh interpolation and the finite fourth-moment exclusion
principle in supplementary S1.6.4. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem scalar_cosh_fourth_lower_sharp {Y : Ω → ℝ}
    (hi : ∀ n : ℕ, Integrable (fun ω => Y ω^n) μ)
    (he : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    (hmean : (∫ ω,Y ω^2 ∂μ)=1) (t : ℝ) :
    Real.cosh (t*Real.sqrt (∫ ω,Y ω^4 ∂μ))-1 ≤
      (∫ ω,Y ω^4 ∂μ)*((∫ ω,Real.cosh (t*Y ω) ∂μ)-1) := by
  let m := ∫ ω,Y ω^4 ∂μ
  have hm1 : 1 ≤ m := scalar_one_le_fourth_moment (hi 2) (hi 4) hmean
  have hm : 0 ≤ m := by linarith
  have hmom (n : ℕ) : m^(n+1) ≤ m*(∫ ω,Y ω^(2*(n+1)) ∂μ) := by
    have h := mul_le_mul_of_nonneg_left (scalar_even_moment_lower hi hmean n) hm
    change m*m^n ≤ _ at h
    simpa only [← pow_succ'] using h
  have hseries (z : ℝ) : HasSum (fun n : ℕ => z^(2*(n+1))/(Nat.factorial (2*(n+1)):ℝ))
      (Real.cosh z-1) := by
    have h := (hasSum_nat_add_iff' 1).2 (Real.hasSum_cosh z)
    simpa using h
  have hiterm (n : ℕ) : Integrable
      (fun ω => (t*Y ω)^(2*(n+1))/(Nat.factorial (2*(n+1)):ℝ)) μ := by
    simpa only [mul_pow] using ((hi (2*(n+1))).const_mul (t^(2*(n+1)))).div_const _
  have hnonneg (z : ℝ) (n : ℕ) : 0 ≤ z^(2*(n+1))/(Nat.factorial (2*(n+1)):ℝ) := by
    rw [pow_mul]
    positivity
  rw [← (hseries (t*Real.sqrt m)).tsum_eq]
  apply (hseries (t*Real.sqrt m)).summable.tsum_le_of_sum_range_le
  intro N
  calc
    (∑ n ∈ Finset.range N,(t*Real.sqrt m)^(2*(n+1))/(Nat.factorial (2*(n+1)):ℝ)) ≤
        m*∑ n ∈ Finset.range N,(∫ ω,(t*Y ω)^(2*(n+1))/(Nat.factorial (2*(n+1)):ℝ) ∂μ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      rw [mul_pow,pow_mul (Real.sqrt m),Real.sq_sqrt hm]
      simp_rw [mul_pow]
      rw [integral_div,integral_const_mul]
      have h := mul_le_mul_of_nonneg_left (hmom n) (hnonneg t n)
      convert! h using 1 <;> ring
    _ = m*(∫ ω,∑ n ∈ Finset.range N,(t*Y ω)^(2*(n+1))/(Nat.factorial (2*(n+1)):ℝ) ∂μ) := by
      rw [integral_finsetSum _ (fun n _ => hiterm n)]
    _ ≤ m*(∫ ω,Real.cosh (t*Y ω)-1 ∂μ) := by
      apply mul_le_mul_of_nonneg_left _ hm
      apply integral_mono (integrable_finsetSum _ (fun n _ => hiterm n))
        ((scalar_cosh_integrable he t).sub (integrable_const 1))
      intro ω
      change (∑ n ∈ Finset.range N,_) ≤ Real.cosh (t*Y ω)-1
      rw [← (hseries (t*Y ω)).tsum_eq]
      exact (hseries (t*Y ω)).summable.sum_le_tsum (Finset.range N) (fun n _ => hnonneg _ n)
    _ = _ := by
      rw [integral_sub (scalar_cosh_integrable he t) (integrable_const 1)]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
      rfl

theorem scalar_cosh_fourth_implicit_sharp {Y : Ω → ℝ} {K : ℝ}
    (h : HasSubgaussianMGF Y ⟨K^2,sq_nonneg K⟩ μ)
    (hmean : (∫ ω,Y ω^2 ∂μ)=1) (x : ℝ) :
    (∫ ω,Y ω^4 ∂μ)*Real.log (1+(Real.cosh x-1)/(∫ ω,Y ω^4 ∂μ)) ≤ K^2*x^2/2 := by
  let m := ∫ ω,Y ω^4 ∂μ
  have hi : ∀ n : ℕ, Integrable (fun ω => Y ω^n) μ := fun n =>
    integrable_pow_of_integrable_exp_mul (by norm_num : (1:ℝ)≠0)
      (h.integrable_exp_mul 1) (h.integrable_exp_mul (-1)) n
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one (scalar_one_le_fourth_moment (hi 2) (hi 4) hmean)
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  let t := x/Real.sqrt m
  have ht : t*Real.sqrt m = x := div_mul_cancel₀ _ hs.ne'
  have hc := scalar_cosh_fourth_lower_sharp hi h.integrable_exp_mul hmean t
  rw [ht] at hc
  have hu := scalar_cosh_upper h t
  have hcosh : 0 ≤ Real.cosh x-1 := sub_nonneg.mpr (Real.one_le_cosh x)
  have hpos : 0 < 1+(Real.cosh x-1)/m := by positivity
  have hbound : 1+(Real.cosh x-1)/m ≤ Real.exp (K^2*t^2/2) := by
    change Real.cosh x-1 ≤ m*((∫ ω,Real.cosh (t*Y ω) ∂μ)-1) at hc
    have hd : (Real.cosh x-1)/m ≤ (∫ ω,Real.cosh (t*Y ω) ∂μ)-1 :=
      (div_le_iff₀ hm).2 (by nlinarith)
    nlinarith
  have hl := Real.log_le_log hpos hbound
  rw [Real.log_exp] at hl
  have hmul := mul_le_mul_of_nonneg_left hl hm.le
  have heq : m*(K^2*t^2/2) = K^2*x^2/2 := by
    dsimp [t]
    rw [div_pow,Real.sq_sqrt hm.le]
    field_simp
    <;> ring
  rw [heq] at hmul
  exact hmul

theorem mul_log_one_add_div_mono {A m0 m : ℝ} (hA : 0 ≤ A)
    (hm0 : 0 < m0) (hmm : m0 ≤ m) :
    m0*Real.log (1+A/m0) ≤ m*Real.log (1+A/m) := by
  have hm := hm0.trans_le hmm
  have ht0 : 0 ≤ m0/m := div_nonneg hm0.le hm.le
  have ht1 : 0 ≤ 1-m0/m := sub_nonneg.mpr ((div_le_one hm).2 hmm)
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show 0 < 1+A/m0 by positivity) (by norm_num : (0:ℝ)<1)
    ht0 ht1 (show m0/m+(1-m0/m)=(1:ℝ) by ring)
  have hid : (m0/m)*(1+A/m0)+(1-m0/m)*1 = 1+A/m := by
    field_simp
    <;> ring
  simp only [smul_eq_mul,Real.log_one,mul_zero,add_zero,hid] at h
  have hh := mul_le_mul_of_nonneg_left h hm.le
  have hc : m*((m0/m)*Real.log (1+A/m0)) = m0*Real.log (1+A/m0) := by
    field_simp
  rwa [hc] at hh

theorem scalar_fourth_exclusion {Y : Ω → ℝ} {K m0 E x : ℝ}
    (h : HasSubgaussianMGF Y ⟨K^2,sq_nonneg K⟩ μ)
    (hmean : (∫ ω,Y ω^2 ∂μ)=1) (hm0 : 0 < m0) (hE : K^2 ≤ E)
    (hexclude : E*x^2/2 < m0*Real.log (1+(Real.cosh x-1)/m0)) :
    (∫ ω,Y ω^4 ∂μ) < m0 := by
  by_contra hn
  have hmm : m0 ≤ ∫ ω,Y ω^4 ∂μ := le_of_not_gt hn
  have hm := mul_log_one_add_div_mono (sub_nonneg.mpr (Real.one_le_cosh x)) hm0 hmm
  have hi := scalar_cosh_fourth_implicit_sharp h hmean x
  have he := mul_le_mul_of_nonneg_right hE (sq_nonneg x)
  linarith

end
end SingularValueBounds.KL
