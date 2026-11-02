import SingularValueBounds.KL.Upper.TailMoments
import SingularValueBounds.Scalar.UpperExponentialTools

/-! # Restricted-measure rare-event integration (supplementary S1.6.4)

The event and upper shift need not be independent. All tail and moment
estimates are carried out on the restricted finite measure.
-/
open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def exponentialRemainder (t x : ℝ) : ℝ := Real.exp (t*x)-1-t*x

theorem exponentialRemainder_nonneg (t x : ℝ) : 0≤exponentialRemainder t x := by
  dsimp [exponentialRemainder]
  linarith [Real.add_one_le_exp (t*x)]

theorem integral_exponentialRemainder [IsFiniteMeasure μ] {Y : Ω → ℝ} {t : ℝ}
    (hYi : Integrable Y μ) (hExp : Integrable (fun ω => Real.exp (t*Y ω)) μ) :
    (∫ω,exponentialRemainder t (Y ω) ∂μ)=
      (∫ω,Real.exp (t*Y ω) ∂μ)-μ.real univ-t*(∫ω,Y ω ∂μ) := by
  change (∫ω,(((fun ω : Ω => Real.exp (t*Y ω))-(fun _ : Ω => (1 : ℝ)))-
    (fun ω : Ω => t*Y ω)) ω ∂μ)=_
  rw [integral_sub' (hExp.sub (integrable_const 1)) (hYi.const_mul t),
    integral_sub' hExp (integrable_const 1),integral_const_mul,integral_const,smul_eq_mul,mul_one]

theorem exponentialRemainder_mono {t x y : ℝ} (ht : 0≤t) (hx : 0≤x) (hxy : x≤y) :
    exponentialRemainder t x ≤ exponentialRemainder t y := by
  have he : 1≤Real.exp (t*x) := Real.one_le_exp_iff.mpr (mul_nonneg ht hx)
  have hδ : 0≤t*(y-x) := mul_nonneg ht (sub_nonneg.mpr hxy)
  have hmul := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t*(y-x))) (Real.exp_nonneg (t*x))
  have hid : Real.exp (t*x)*Real.exp (t*(y-x))=Real.exp (t*y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid] at hmul
  dsimp [exponentialRemainder]
  nlinarith [mul_nonneg (sub_nonneg.mpr he) hδ]

/-- Gaussian comparison is used on the *whole* remainder MGF of `T`.
This deterministic rare-event split does not claim moment domination of
the original sub-Gaussian quadratic form. -/
theorem mgf_rare_event_split [IsProbabilityMeasure μ] {Y T : Ω → ℝ}
    {E : Set Ω} {t : ℝ} (hE : MeasurableSet E) (ht : 0≤t)
    (hY0 : ∀ ω, 0≤Y ω)
    (hYi : Integrable Y μ) (hTi : Integrable T μ)
    (hYE : Integrable (fun ω => Real.exp (t*Y ω)) μ)
    (hTE : Integrable (fun ω => Real.exp (t*T ω)) μ)
    (hMean : (∫ ω, Y ω ∂μ)≤1)
    (hGood : ∀ ω, ω∉E → Y ω≤T ω) :
    (∫ ω, Real.exp (t*Y ω) ∂μ) ≤ 1+t+
      (∫ ω, exponentialRemainder t (T ω) ∂μ)+
      ∫ ω in E, exponentialRemainder t (Y ω) ∂μ := by
  have hRY : Integrable (fun ω => exponentialRemainder t (Y ω)) μ :=
    (hYE.sub (integrable_const 1)).sub (hYi.const_mul t)
  have hRT : Integrable (fun ω => exponentialRemainder t (T ω)) μ :=
    (hTE.sub (integrable_const 1)).sub (hTi.const_mul t)
  have hpoint (ω : Ω) : exponentialRemainder t (Y ω) ≤
      exponentialRemainder t (T ω)+E.indicator (fun ω => exponentialRemainder t (Y ω)) ω := by
    by_cases hω : ω∈E
    · simp only [Set.indicator_of_mem hω]
      linarith [exponentialRemainder_nonneg t (T ω)]
    · simp only [Set.indicator_of_notMem hω,add_zero]
      exact exponentialRemainder_mono ht (hY0 ω) (hGood ω hω)
  have hi := integral_mono hRY (hRT.add (hRY.indicator hE)) hpoint
  change (∫ ω, exponentialRemainder t (Y ω) ∂μ)≤
    ∫ ω, exponentialRemainder t (T ω)+E.indicator (fun ω => exponentialRemainder t (Y ω)) ω ∂μ at hi
  rw [integral_add hRT (hRY.indicator hE),integral_indicator hE] at hi
  change (∫ ω, (((fun ω : Ω => Real.exp (t*Y ω))-(fun _ : Ω => (1 : ℝ)))-
    (fun ω : Ω => t*Y ω)) ω ∂μ)≤_ at hi
  rw [integral_sub' (hYE.sub (integrable_const 1)) (hYi.const_mul t),
    integral_sub' hYE (integrable_const 1),integral_const_mul] at hi
  simp only [integral_const,probReal_univ,one_smul] at hi
  nlinarith

/-- Combining an event bound and an unrestricted exponential tail. -/
theorem restricted_tail_bounds [IsFiniteMeasure μ] {Y : Ω → ℝ} {E : Set Ω}
    {p C r : ℝ} (hE : MeasurableSet E)
    (hp : μ.real E ≤ p)
    (htail : ∀ u, 0 ≤ u → μ.real {ω | u < Y ω} ≤ C*Real.exp (-(r*u)))
    {u : ℝ} (hu : 0 ≤ u) :
    (μ.restrict E).real {ω | u < Y ω} ≤ p ∧
      (μ.restrict E).real {ω | u < Y ω} ≤ C*Real.exp (-(r*u)) := by
  rw [measureReal_restrict_apply' hE]
  constructor
  · exact (measureReal_mono inter_subset_right (measure_ne_top μ _)).trans hp
  · exact (measureReal_mono inter_subset_left (measure_ne_top μ _)).trans (htail u hu)

/-- Exact shifted-exponential moment domination on an arbitrary finite
measure. The mass bound and cutoff-tail comparison supply both pieces of
the dominating survival function. -/
theorem finite_measure_cutoff_moment [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {p C r A : ℝ}
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hC : 0 ≤ C) (hr : 0 < r) (hA : 0 ≤ A)
    (hmass : μ.real univ ≤ p)
    (htail : ∀ u, 0 ≤ u → μ.real {ω | u < Y ω} ≤ C*Real.exp (-(r*u)))
    (hcut : C*Real.exp (-(r*A)) ≤ p) (n : ℕ) :
    Integrable (fun ω => Y ω^n) μ ∧
      (∫ ω, Y ω^n ∂μ)/(n.factorial : ℝ) ≤ p*tailMomentSeries (n+1) A (1/r) := by
  let U : Ω → ℝ := fun ω => max (Y ω-A) 0
  have hU0 : ∀ ω, 0 ≤ U ω := fun ω => le_max_right _ _
  have hUi (j : ℕ) : Integrable (fun ω => U ω^j) μ := by
    cases j with
    | zero => simpa using integrable_const (1 : ℝ)
    | succ j => exact (exponential_tail_positive_part_moment hY hC hr hA htail j).1
  have hUm (j : ℕ) : (∫ ω, U ω^j ∂μ) ≤ p*(j.factorial : ℝ)/r^j := by
    cases j with
    | zero => simpa [U] using hmass
    | succ j =>
      have h := (exponential_tail_positive_part_moment hY hC hr hA htail j).2
      exact h.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcut (by positivity)) (by positivity))
  have hYi : Integrable (fun ω => Y ω^n) μ := by
    cases n with
    | zero => simpa using integrable_const (1 : ℝ)
    | succ n => exact (exponential_tail_moment hY hY0 hC hr htail n).1
  refine ⟨hYi, ?_⟩
  have hsum : ∀ ω, (A+U ω)^n =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*A^j*U ω^(n-j) := by
    intro ω
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcoeff (j : ℕ) : Integrable (fun ω => (n.choose j : ℝ)*A^j*U ω^(n-j)) μ :=
    (hUi (n-j)).const_mul _
  have hSumInt : Integrable (fun ω => (A+U ω)^n) μ := by
    simp_rw [hsum]
    exact integrable_finsetSum _ (fun j hj => hcoeff j)
  have hpoint : ∀ ω, Y ω^n ≤ (A+U ω)^n := by
    intro ω
    apply pow_le_pow_left₀ (hY0 ω)
    have h := le_max_left (Y ω-A) 0
    dsimp [U]
    linarith
  have hbound := integral_mono hYi hSumInt hpoint
  simp_rw [hsum] at hbound
  rw [integral_finsetSum _ (fun j hj => hcoeff j)] at hbound
  simp_rw [integral_const_mul] at hbound
  have hterms : (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*A^j*(∫ ω, U ω^(n-j) ∂μ)) ≤
      (n.factorial : ℝ)*(p*tailMomentSeries (n+1) A (1/r)) := by
    unfold tailMomentSeries
    simp only [Nat.add_sub_cancel]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    have hf : (n.choose j : ℝ)*(j.factorial : ℝ)*((n-j).factorial : ℝ) = (n.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
    calc
      _ ≤ (n.choose j : ℝ)*A^j*(p*((n-j).factorial : ℝ)/r^(n-j)) :=
        mul_le_mul_of_nonneg_left (hUm (n-j)) (by positivity)
      _ = _ := by
        rw [hf.symm,div_pow]
        field_simp
        <;> ring
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<n.factorial)).2
  simpa only [mul_comm] using hbound.trans hterms

/-- Rare-event form of the preceding theorem. Its hypotheses contain no
independence statement about `E` and `Y`. -/
theorem rare_event_moment [IsFiniteMeasure μ] {Y : Ω → ℝ} {E : Set Ω}
    {p C r A : ℝ} (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hE : MeasurableSet E) (hC : 0 ≤ C)
    (hr : 0 < r) (hA : 0 ≤ A) (hprob : μ.real E ≤ p)
    (htail : ∀ u, 0 ≤ u → μ.real {ω | u < Y ω} ≤ C*Real.exp (-(r*u)))
    (hcut : C*Real.exp (-(r*A)) ≤ p) (n : ℕ) :
    IntegrableOn (fun ω => Y ω^n) E μ ∧
      (∫ ω in E, Y ω^n ∂μ)/(n.factorial : ℝ) ≤ p*tailMomentSeries (n+1) A (1/r) := by
  apply finite_measure_cutoff_moment hY.aemeasurable hY0 hC hr hA
    (by simpa using hprob) _ hcut n
  intro u hu
  exact (restricted_tail_bounds hE hprob htail hu).2

end
end SingularValueBounds.KL
