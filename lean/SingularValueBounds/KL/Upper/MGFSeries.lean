import SingularValueBounds.KL.Upper.TailMoments
import SingularValueBounds.KL.Upper.RareEvents

/-! # From explicit majorant coefficients to the upper MGF (S1.6.4)

The coefficient comparison is applied only after an actual moment bound or
an explicit Gaussian majorant has been constructed.
-/
open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

def bernsteinMajorantTerm (v t : ℝ) (p : ℕ) : ℝ :=
  if p=0 then 1 else if p=1 then t else
    (v^(p-1)+(if p=2 then 1/2 else 0))*t^p

theorem bernsteinMajorant_hasSum {v t : ℝ} (hv : 0≤v) (ht : 0≤t) (hvt : v*t<1) :
    HasSum (bernsteinMajorantTerm v t) (1+t/(1-v*t)+t^2/2) := by
  have hg := (hasSum_geometric_of_lt_one (mul_nonneg hv ht) hvt).mul_left (v*t^2)
  have hsingle : HasSum (fun n : ℕ => if n=0 then t^2/2 else 0) (t^2/2) :=
    hasSum_ite_eq 0 _
  have hsum := hg.add hsingle
  have htail : HasSum (fun n => bernsteinMajorantTerm v t (n+2))
      (v*t^2/(1-v*t)+t^2/2) := by
    convert hsum using 1
    · ext n
      dsimp [bernsteinMajorantTerm]
      rw [pow_succ,pow_add,mul_pow]
      by_cases hn : n=0
      · subst n
        norm_num
        ring
      · simp only [show n+2≠2 by omega,hn,if_false,add_zero]
        ring
  apply (hasSum_nat_add_iff' 2).1
  convert htail using 1
  norm_num [bernsteinMajorantTerm,Finset.sum_range_succ]
  field_simp [show 1-v*t≠0 by linarith]
  <;> ring

theorem bernsteinMajorant_le_exp {v t : ℝ} (hv : 0≤v) (ht : 0≤t) (hvt : v*t<1) :
    1+t/(1-v*t)+t^2/2 ≤ Real.exp (t/(1-v*t)) := by
  have hd : 0<1-v*t := by linarith
  have hz : 0≤t/(1-v*t) := div_nonneg ht hd.le
  have htz : t≤t/(1-v*t) := (le_div_iff₀ hd).2 (by nlinarith [mul_nonneg hv (sq_nonneg t)])
  have hh := Certificates.expTaylor_le_exp 2 hz
  norm_num [Certificates.expTaylor,Finset.sum_range_succ] at hh
  have hs : t^2≤(t/(1-v*t))^2 := pow_le_pow_left₀ ht htz 2
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The positive remainder has exactly the series starting at order two,
on any finite measure, including a restriction to a rare event. -/
theorem exponentialRemainder_integral_eq_tsum [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {t : ℝ} (hY : AEMeasurable Y μ) (hY0 : ∀ω,0≤Y ω) (ht : 0≤t)
    (hMom : ∀p : ℕ,Integrable (fun ω => Y ω^p) μ)
    (hTailSum : Summable (fun p : ℕ =>
      ((∫ω,Y ω^(p+2) ∂μ)/((p+2).factorial : ℝ))*t^(p+2))) :
    Integrable (fun ω => Real.exp (t*Y ω)) μ ∧
      (∫ω,exponentialRemainder t (Y ω) ∂μ)=
        ∑'p : ℕ,((∫ω,Y ω^(p+2) ∂μ)/((p+2).factorial : ℝ))*t^(p+2) := by
  have hsum : Summable (fun p : ℕ => ((∫ω,Y ω^p ∂μ)/(p.factorial : ℝ))*t^p) :=
    (summable_nat_add_iff 2).1 hTailSum
  have he := exp_integrable_and_eq_tsum_of_moments hY hY0 ht hMom hsum
  refine ⟨he.1, ?_⟩
  have hYi : Integrable Y μ := by simpa using hMom 1
  have hR : (∫ω,exponentialRemainder t (Y ω) ∂μ)=
      (∫ω,Real.exp (t*Y ω) ∂μ)-μ.real univ-t*(∫ω,Y ω ∂μ) := by
    change (∫ω,(((fun ω : Ω => Real.exp (t*Y ω))-(fun _ : Ω => (1 : ℝ)))-
      (fun ω : Ω => t*Y ω)) ω ∂μ)=_
    rw [integral_sub' (he.1.sub (integrable_const 1)) (hYi.const_mul t),
      integral_sub' he.1 (integrable_const 1),integral_const_mul,integral_const,smul_eq_mul,mul_one]
  rw [hR,he.2]
  have hs := hsum.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at hs
  nlinarith

/-- Moment bounds imply actual exponential integrability and the printed
upper Bernstein MGF. The first moment is used separately from the second.
The generic `v` covers the endpoint `4` and the general `9 K²L/2`. -/
theorem mgf_of_bernstein_moments {Y : Ω → ℝ} {v t : ℝ}
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0≤Y ω)
    (hv : 0≤v) (ht : 0≤t) (hvt : v*t<1)
    (hMom : ∀ p : ℕ, Integrable (fun ω => Y ω^p) μ)
    (hMean : (∫ ω, Y ω ∂μ)≤1)
    (hSecond : (∫ ω, Y ω^2 ∂μ)/2≤v+1/2)
    (hHigher : ∀ p : ℕ, 3≤p → (∫ ω, Y ω^p ∂μ)/(p.factorial : ℝ)≤v^(p-1)) :
    Integrable (fun ω => Real.exp (t*Y ω)) μ ∧
      (∫ ω, Real.exp (t*Y ω) ∂μ)≤Real.exp (t/(1-v*t)) := by
  let a : ℕ → ℝ := fun p => ((∫ ω, Y ω^p ∂μ)/(p.factorial : ℝ))*t^p
  have ha : ∀ p, 0≤a p := fun p => by
    have hI : 0≤∫ ω, Y ω^p ∂μ := integral_nonneg (fun ω => pow_nonneg (hY0 ω) p)
    dsimp [a]
    positivity
  have hb (p : ℕ) : a p≤bernsteinMajorantTerm v t p := by
    by_cases h0 : p=0
    · subst p
      simp [a,bernsteinMajorantTerm]
    by_cases h1 : p=1
    · subst p
      simp only [a,pow_one,Nat.factorial_one,Nat.cast_one,div_one,
        bernsteinMajorantTerm,show (1 : ℕ)≠0 by omega,if_false,if_true]
      simpa using mul_le_mul_of_nonneg_right hMean ht
    by_cases h2 : p=2
    · subst p
      norm_num only [a,bernsteinMajorantTerm,Nat.factorial_succ,Nat.factorial_zero,
        Nat.cast_ofNat,show (2 : ℕ)≠0 by omega,show (2 : ℕ)≠1 by omega,if_false,if_true,
        Nat.sub_self,Nat.reduceSub,pow_one]
      exact mul_le_mul_of_nonneg_right hSecond (sq_nonneg t)
    have hp3 : 3≤p := by omega
    simp only [bernsteinMajorantTerm,h0,h1,h2,if_false,add_zero]
    exact mul_le_mul_of_nonneg_right (hHigher p hp3) (pow_nonneg ht p)
  have hsum := bernsteinMajorant_hasSum hv ht hvt
  have haSum : Summable a := Summable.of_nonneg_of_le ha hb hsum.summable
  have he := exp_integrable_and_eq_tsum_of_moments hY hY0 ht hMom haSum
  refine ⟨he.1, ?_⟩
  rw [he.2]
  have hh := tsum_le_tsum hb haSum hsum.summable
  rw [hsum.tsum_eq] at hh
  exact hh.trans (bernsteinMajorant_le_exp hv ht hvt)

end
end SingularValueBounds.KL
