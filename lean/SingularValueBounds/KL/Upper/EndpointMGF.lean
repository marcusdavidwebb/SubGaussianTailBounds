import SingularValueBounds.KL.Upper.EndpointCoefficients
import SingularValueBounds.KL.Upper.MGFSeries
import SingularValueBounds.KL.Upper.RareEvents
import SingularValueBounds.KL.Upper.CappedWeights

/-! # Endpoint upper exponential moment (supplementary S1.6.4)

Analytic pieces of Lemma `app:one-upper-mgf`, including the low-shape
first-moment cutoff and the concentrated-spectrum remainder comparison.
-/
open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

theorem endpoint_cutoff_epsilon :
    (46/15 : ℝ)/(1/2)*Real.exp (-((1/2 : ℝ)*(13/2)))≤5/21 := by
  have he := Certificates.expTaylor_le_exp 24 (x := (13/4 : ℝ)) (by norm_num)
  have hnum : (644/25 : ℝ)≤Real.exp (13/4) := by
    norm_num [Certificates.expTaylor,Finset.sum_range_succ] at he
    linarith
  have hInv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<644/25) hnum
  simp only [one_div] at hInv
  norm_num at hInv
  rw [Real.exp_neg]
  norm_num only [show (1/2 : ℝ)*(13/2)=13/4 by norm_num]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Complete low-shape scalar branch of Lemma S1.12. The tail is the
capped-weight determinant estimate; all cutoff moments and the infinite
series passage are proved here. -/
theorem endpoint_mgf_of_low_tail {Y : Ω → ℝ} {t : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω,0≤Y ω)
    (hMean : (∫ ω,Y ω ∂μ)≤1)
    (htail : ∀ u,0≤u → μ.real {ω | u<Y ω}≤(46/15 : ℝ)*Real.exp (-((1/2 : ℝ)*u)))
    (ht : 0≤t) (ht4 : 4*t<1) :
    Integrable (fun ω => Real.exp (t*Y ω)) μ ∧
      (∫ ω,Real.exp (t*Y ω) ∂μ)≤Real.exp (t/(1-4*t)) := by
  have hm (p : ℕ) : Integrable (fun ω => Y ω^p) μ := by
    cases p with
    | zero => simpa using integrable_const (1 : ℝ)
    | succ p => exact (exponential_tail_moment hY.aemeasurable hY0
        (by norm_num : (0 : ℝ)≤46/15) (by norm_num : (0 : ℝ)<1/2) htail p).1
  have hc (n : ℕ) : (∫ ω,Y ω^(n+1) ∂μ)/((n+1).factorial : ℝ)≤
      endpointLowCoefficient (n+1) := by
    have h := first_moment_cutoff hY hY0 (by norm_num : (0 : ℝ)≤46/15)
      (by norm_num : (0 : ℝ)<1/2) (by norm_num : (0 : ℝ)≤13/2) htail hMean n
    let e : ℝ := (92/15 : ℝ)*Real.exp (-(13/4 : ℝ))
    have he0 : 0≤e := by dsimp [e]; positivity
    have he : e≤5/21 := by
      have hh := endpoint_cutoff_epsilon
      norm_num at hh
      exact hh
    have hT := tailMomentSeries_ge_leading n (A := (13/2 : ℝ)) (s := 2)
      (by norm_num) (by norm_num)
    dsimp [endpointLowCoefficient]
    norm_num only [show (1 : ℝ)/(1/2)=2 by norm_num] at h
    change (∫ ω,Y ω^(n+1) ∂μ)/((n+1).factorial : ℝ)≤
      (1-e)*(13/2 : ℝ)^n/((n+1).factorial : ℝ)+e*tailMomentSeries (n+1) (13/2) 2 at h
    let a : ℝ := (13/2 : ℝ)^n/((n+1).factorial : ℝ)
    let S : ℝ := tailMomentSeries (n+1) (13/2) 2
    have hTa : a≤S := hT
    have hprod := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hTa)
    have hh : (∫ ω,Y ω^(n+1) ∂μ)/((n+1).factorial : ℝ)≤(1-e)*a+e*S := by
      convert! h using 1 <;> dsimp [a,S] <;> ring
    have hg : (∫ ω,Y ω^(n+1) ∂μ)/((n+1).factorial : ℝ)≤(16/21 : ℝ)*a+(5/21 : ℝ)*S := by
      nlinarith
    convert! hg using 1 <;> dsimp [a,S] <;> ring
  apply mgf_of_bernstein_moments hY.aemeasurable hY0 (by norm_num : (0 : ℝ)≤4)
    ht ht4 hm hMean
  · have h := hc 1
    rw [endpointLowCoefficient_second] at h
    norm_num at h ⊢
    exact h
  · intro p hp
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
    exact (hc n).trans (endpointLowCoefficient_higher hp)

/-- Concentrated-spectrum scalar assembly. The comparison of `T` and the
auxiliary Gaussian `G` is a whole-MGF comparison. All coefficient estimates
below concern `G` and the restriction of `Y` to `E`.

The matrix proof supplies the displayed event bound, the good-event
comparison, and Gaussian comparison; none is a numerical certificate. -/
theorem endpoint_mgf_of_rare_gaussian
    {Γ : Type*} [MeasurableSpace Γ] {ν : Measure Γ} [IsProbabilityMeasure ν]
    {Y T : Ω → ℝ} {G : Γ → ℝ} {E : Set Ω} {t : ℝ} (i : Fin 3)
    (hY : Measurable Y) (hY0 : ∀ω,0≤Y ω) (hT0 : ∀ω,0≤T ω)
    (hG : AEMeasurable G ν) (hG0 : ∀ω,0≤G ω)
    (hE : MeasurableSet E) (ht : 0≤t) (ht4 : 4*t<1)
    (hMeanY : (∫ω,Y ω ∂μ)≤1) (hTi : Integrable T μ)
    (hMeanT : (∫ω,T ω ∂μ)=1) (hMeanG : (∫ω,G ω ∂ν)=1)
    (hGMom : ∀p : ℕ,Integrable (fun ω => G ω^p) ν)
    (hTE : Integrable (fun ω => Real.exp (t*T ω)) μ)
    (hCompare : (∫ω,Real.exp (t*T ω) ∂μ)≤∫ω,Real.exp (t*G ω) ∂ν)
    (hGood : ∀ω,ω∉E → Y ω≤T ω)
    (hProb : μ.real E≤(endpointRareRow i).probability)
    (hTail : ∀u,0≤u → μ.real {ω | u<Y ω}≤
      (177/50 : ℝ)*Real.exp (-((23/50 : ℝ)*u)))
    (hCut : (177/50 : ℝ)*Real.exp (-((23/50 : ℝ)*(endpointRareRow i).cutoff))≤
      (endpointRareRow i).probability)
    (hGSecond : (∫ω,G ω^2 ∂ν)/2≤1/2+(endpointRareRow i).zeta)
    (hGHigher : ∀p : ℕ,3≤p → (∫ω,G ω^p ∂ν)/(p.factorial : ℝ)≤gaussianSquareCoefficient p) :
    Integrable (fun ω => Real.exp (t*Y ω)) μ ∧
      (∫ω,Real.exp (t*Y ω) ∂μ)≤Real.exp (t/(1-4*t)) := by
  have htR : t<(23/50 : ℝ) := by linarith
  have hYi : Integrable Y μ := by
    simpa using (exponential_tail_moment hY.aemeasurable hY0
      (by norm_num : (0 : ℝ)≤177/50) (by norm_num : (0 : ℝ)<23/50) hTail 0).1
  have hRem := exponential_tail_remainder hY.aemeasurable hY0
    (by norm_num : (0 : ℝ)≤177/50) (by norm_num : (0 : ℝ)<23/50)
    ht htR (by norm_num : (0 : ℝ)≤1) (b := 0) (by positivity) hTail
  have hYE : Integrable (fun ω => Real.exp (t*Y ω)) μ := by
    have h := hRem.1.add (integrable_const (1 : ℝ))
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.add_apply,one_mul,zero_mul,sub_zero,sub_add_cancel])
  have hr0 : 0≤(endpointRareRow i).probability := by fin_cases i <;> norm_num [endpointRareRow]
  have hA0 : 0≤(endpointRareRow i).cutoff := by fin_cases i <;> norm_num [endpointRareRow]
  have hRare (p : ℕ) := rare_event_moment hY hY0 hE hr0
    (by norm_num : (0 : ℝ)≤177/50) (by norm_num : (0 : ℝ)<23/50)
    hA0 hProb hTail hCut p
  let g : ℕ → ℝ := fun n => ((∫ω,G ω^(n+2) ∂ν)/((n+2).factorial : ℝ))*t^(n+2)
  let r : ℕ → ℝ := fun n => ((∫ω in E,Y ω^(n+2) ∂μ)/((n+2).factorial : ℝ))*t^(n+2)
  have hg0 (n : ℕ) : 0≤g n := by
    have h : 0 ≤ ∫ ω, G ω ^ (n+2) ∂ν :=
      integral_nonneg (fun ω => pow_nonneg (hG0 ω) (n+2))
    dsimp [g]
    positivity
  have hr0' (n : ℕ) : 0≤r n := by
    have h : 0 ≤ ∫ ω in E, Y ω ^ (n+2) ∂μ :=
      integral_nonneg (fun ω => pow_nonneg (hY0 ω) (n+2))
    dsimp [r]
    positivity
  have hbound (n : ℕ) : g n+r n≤bernsteinMajorantTerm 4 t (n+2) := by
    have hRareN := (hRare (n+2)).2
    norm_num only [show (1 : ℝ)/(23/50)=50/23 by norm_num] at hRareN
    have hGN : (∫ω,G ω^(n+2) ∂ν)/((n+2).factorial : ℝ)≤
        if n=0 then 1/2+(endpointRareRow i).zeta else gaussianSquareCoefficient (n+2) := by
      by_cases hn : n=0
      · subst n
        simpa using hGSecond
      · simpa only [hn,if_false] using hGHigher (n+2) (by omega)
    have hTotal : (∫ω,G ω^(n+2) ∂ν)/((n+2).factorial : ℝ)+
        (∫ω in E,Y ω^(n+2) ∂μ)/((n+2).factorial : ℝ)≤endpointRareCoefficient i (n+2) := by
      simpa only [endpointRareCoefficient,shiftedExponentialCoefficient,
        show n+2=2 ↔ n=0 by omega] using add_le_add hGN hRareN
    have hCoeff : endpointRareCoefficient i (n+2)≤
        (4 : ℝ)^(n+2-1)+(if n+2=2 then 1/2 else 0) := by
      by_cases hn : n=0
      · subst n
        norm_num
        exact (endpointRareCoefficient_second i).le
      · simpa only [show n+2≠2 by omega,if_false,add_zero] using
          endpointRareCoefficient_higher i (by omega : 3≤n+2)
    have hh := mul_le_mul_of_nonneg_right (hTotal.trans hCoeff) (pow_nonneg ht (n+2))
    dsimp [g,r,bernsteinMajorantTerm]
    convert! hh using 1 <;> ring
  have hMajor := bernsteinMajorant_hasSum (by norm_num : (0 : ℝ)≤4) ht ht4
  have hMajorTail : Summable (fun n => bernsteinMajorantTerm 4 t (n+2)) :=
    (summable_nat_add_iff 2).2 hMajor.summable
  have hBoth : Summable (fun n => g n+r n) := Summable.of_nonneg_of_le
    (fun n => add_nonneg (hg0 n) (hr0' n)) hbound hMajorTail
  have hgSum : Summable g := Summable.of_nonneg_of_le hg0
    (fun n => le_add_of_nonneg_right (hr0' n)) hBoth
  have hrSum : Summable r := Summable.of_nonneg_of_le hr0'
    (fun n => le_add_of_nonneg_left (hg0 n)) hBoth
  have hGE := exponentialRemainder_integral_eq_tsum hG hG0 ht hGMom hgSum
  have hRE := exponentialRemainder_integral_eq_tsum hY.aemeasurable hY0 ht
    (fun p => (hRare p).1) hrSum
  have hGInt : Integrable G ν := by simpa using hGMom 1
  have hRT : (∫ω,exponentialRemainder t (T ω) ∂μ)≤
      ∫ω,exponentialRemainder t (G ω) ∂ν := by
    have heT : Integrable (fun ω => exponentialRemainder t (T ω)) μ :=
      (hTE.sub (integrable_const 1)).sub (hTi.const_mul t)
    have heG : Integrable (fun ω => exponentialRemainder t (G ω)) ν :=
      (hGE.1.sub (integrable_const 1)).sub (hGInt.const_mul t)
    rw [integral_exponentialRemainder hTi hTE,
      integral_exponentialRemainder hGInt hGE.1,hMeanT,hMeanG]
    simpa using hCompare
  have hSplit := mgf_rare_event_split hE ht hY0 hT0 hYi hTi hYE hTE hMeanY hGood
  have hSums := hBoth.tsum_le_tsum hbound hMajorTail
  rw [Summable.tsum_add hgSum hrSum] at hSums
  have hFinal := hMajor.summable.sum_add_tsum_nat_add 2
  rw [hMajor.tsum_eq] at hFinal
  have hFinite : (∑ p∈Finset.range 2,bernsteinMajorantTerm 4 t p)=1+t := by
    norm_num [bernsteinMajorantTerm,Finset.sum_range_succ]
  rw [hFinite] at hFinal
  rw [hRE.2] at hSplit
  rw [hGE.2] at hRT
  refine ⟨hYE, ?_⟩
  apply le_trans _ (bernsteinMajorant_le_exp (by norm_num : (0 : ℝ)≤4) ht ht4)
  nlinarith

end
end SingularValueBounds.KL
