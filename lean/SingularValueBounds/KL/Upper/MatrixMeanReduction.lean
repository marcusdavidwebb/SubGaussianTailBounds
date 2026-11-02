import SingularValueBounds.KL.Weighted.EntropyIntegration
import SingularValueBounds.KL.Upper.ComparisonLogdet
import SingularValueBounds.KL.Upper.EndpointMatrix

open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1800000
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Common exact-matrix mean reduction used by both upper entropy packages. -/
theorem upperShift_mean_of_entropy_cost
    {X : Ω → ι → ℝ} {K L w b : ℝ} (hiso : CentredIsotropic μ X)
    (hsg : SubGaussianMGF μ X K) (hK : 0<K) (hL : 0≤L) (hw : 0≤w)
    {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hcap : K^2*Matrix.trace R+w*K^2*L*frobenius R≤b) (hb : b<1)
    (hCost : ∀ W : Ω → ℝ, Measurable W → Integrable W μ →
      (∀ω,0≤W ω) → (∫ω,W ω ∂μ)=1 →
      (∀ω,W ω≤(1-b)*upperShift R hR (X ω)) →
      Integrable (fun ω => W ω*Real.log (W ω)) μ →
      (∫ω,W ω*Real.log (W ω) ∂μ)+upperComparisonMatrixLogdet R/2≤w*L) :
    Integrable (fun ω => (1-b)*upperShift R hR (X ω)) μ ∧
      (∫ω,(1-b)*upperShift R hR (X ω) ∂μ)≤1 := by
  let Y := fun ω => (1-b)*upperShift R hR (X ω)
  let Q := quadraticForm (upperFixedComparison R) X
  let a := K^2*frobenius R
  let H := Matrix.trace R/frobenius R+upperComparisonMatrixLogdet R/2
  have hη : 0<frobenius R := frobenius_pos hR
  have ha : 0<a := by dsimp [a]; positivity
  have hY : Measurable Y := by
    have hp : Measurable (fun ω =>
        ((⟨R,hR⟩ : {R : Matrix ι ι ℝ // R.PosDef}),X ω)) :=
      measurable_const.prodMk hiso.measurable
    exact measurable_const.mul (by
      simpa only [Function.comp_def] using (measurable_upperShift (ι := ι)).comp hp)
  have hY0 : ∀ω,0≤Y ω := fun ω =>
    mul_nonneg (sub_pos.mpr hb).le (upperShift_nonneg hR (X ω))
  have htrace : K^2*Matrix.trace R≤b := by
    have hn : 0≤w*K^2*L*frobenius R := by positivity
    linarith
  have hTail : ∀u,0≤u → μ.real {ω | u<Y ω}≤
      (Real.sqrt (1-(1/2 : ℝ)))⁻¹*Real.exp (-((1/(4*K^2))*u)) := by
    intro u hu
    have ht := upperShift_tail_family hsg hiso.measurable hK hR htrace hb
      (by norm_num : (0 : ℝ)<1/2) (by norm_num : (1/2 : ℝ)<1) hu
    convert! ht using 1 <;> congr 2 <;> ring
  have hr : 0<1/(4*K^2) := by positivity
  have hC : 0≤(Real.sqrt (1-(1/2 : ℝ)))⁻¹ := by positivity
  have hYi : Integrable Y μ := by
    simpa using (exponential_tail_moment hY.aemeasurable hY0 hC hr hTail 0).1
  refine ⟨hYi,?_⟩
  by_cases hMean : (∫ω,Y ω ∂μ)<1
  · exact hMean.le
  have hm1 : 1≤∫ω,Y ω ∂μ := le_of_not_gt hMean
  let m := (∫ ω, Y ω ∂μ)
  let W := fun ω => Y ω/m
  have hm : 0 < m := by dsimp [m]; linarith
  have hn := normalized_weight_properties hYi hY0 hm1
  change Integrable W μ ∧ _ at hn
  have hW : Measurable W := hY.div_const m
  have hW0 : ∀ω,0≤W ω := fun ω => (hn.2.2.1 ω).1
  have hWY : ∀ω,W ω≤Y ω := fun ω => (hn.2.2.1 ω).2
  have hWE : Integrable (fun ω => W ω*Real.log (W ω)) μ :=
    entropy_integrable_of_exponential_tail hW.aemeasurable hW0 hC hr
      (fun u hu => (hn.2.2.2 u).trans (hTail u hu))
  have hB := upperFixedComparison_posSemidef hR
  have hgap : (1-(2*K^2*(1/a)) • upperFixedComparison R).PosDef := by
    have hid : 2*K^2*(1/a)=2/frobenius R := by
      dsimp [a]
      field_simp
    rw [hid]
    exact upperComparisonNormalizedGap_posDef hR
  have he := quadratic_exponential_det_bound hsg hiso.measurable _ hB (1/a)
    (by positivity) hgap
  have hg := quadratic_log_mgf_le_logdet hsg hiso.measurable _ hB (1/a)
    (by positivity) hgap
  have hExp : Integrable (fun ω => Real.exp (Q ω/a)) μ := by
    simpa only [one_div,mul_comm,div_eq_mul_inv,Q,one_mul] using he.1
  have hGaussian : Real.log (∫ω,Real.exp (Q ω/a) ∂μ)≤H := by
    have hid : (1-(2*K^2*(1/a)) • upperFixedComparison R)=upperComparisonNormalizedGap R := by
      unfold upperComparisonNormalizedGap
      congr 2
      dsimp [a]
      field_simp
    rw [hid] at hg
    have hg' : Real.log (∫ω,Real.exp (Q ω/a) ∂μ) ≤
        -Real.log (Matrix.det (upperComparisonNormalizedGap R))/2 := by
      simpa only [Q,one_div,div_eq_mul_inv,mul_comm,one_mul] using hg
    dsimp [H,upperComparisonMatrixLogdet]
    linarith
  have hQ0 : ∀ω,0≤Q ω := quadraticForm_nonneg hB X
  have hZ0 : ∀ᵐω∂μ,0≤Q ω/a := Filter.Eventually.of_forall fun ω => div_nonneg (hQ0 ω) ha.le
  have hWeighted := weighted_entropy_of_nonneg (Filter.Eventually.of_forall hW0)
    hZ0 hn.1 hn.2.1 hWE hExp
  have hWZi := integrable_weighted_of_nonneg (Filter.Eventually.of_forall hW0)
    hZ0 hn.1 hWE hExp
  have hWQi : Integrable (fun ω => W ω*Q ω) μ := by
    convert! hWZi.mul_const a using 1
    ext ω
    try dsimp
    field_simp
  have hCost' := hCost W hW hn.1 hW0 hn.2.1 hWY hWE
  have hWQ : (∫ω,W ω*Q ω ∂μ)≤b := by
    have hid : (∫ω,W ω*(Q ω/a) ∂μ)=(∫ω,W ω*Q ω ∂μ)/a := by
      simp_rw [← mul_div_assoc]
      rw [integral_div]
    rw [hid] at hWeighted
    have hwq := (div_le_iff₀ ha).1 hWeighted
    have hsum : a*((∫ω,W ω*Real.log (W ω) ∂μ)+H)≤b := by
      have hh := mul_le_mul_of_nonneg_left hCost' ha.le
      dsimp [a,H] at *
      have hid : K^2*frobenius R*(Matrix.trace R/frobenius R)=K^2*Matrix.trace R := by
        field_simp
      nlinarith
    apply hwq.trans
    calc
      _ ≤ ((∫ω,W ω*Real.log (W ω) ∂μ)+H)*a :=
        mul_le_mul_of_nonneg_right (add_le_add_right hGaussian _) ha.le
      _ = a*((∫ω,W ω*Real.log (W ω) ∂μ)+H) := by ring
      _ ≤ b := hsum
  have hYQi : Integrable (fun ω => Y ω*Q ω) μ := by
    convert! hWQi.const_mul m using 1
    ext ω
    dsimp [W]
    field_simp
  have hpoint : ∀ω,Y ω≤(1-b)*quadraticForm (upperSquareWeight R) X ω+Y ω*Q ω := by
    intro ω
    have hh := mul_le_mul_of_nonneg_left (upperShift_fixed_comparison hR (X ω))
      (sub_pos.mpr hb).le
    dsimp [Y,Q,quadraticForm] at *
    nlinarith
  have hFixed := integral_mono hYi
    (((hiso.quadratic_integrable _).const_mul (1-b)).add hYQi) hpoint
  change (∫ω,Y ω ∂μ) ≤ (∫ω,(1-b)*quadraticForm (upperSquareWeight R) X ω+Y ω*Q ω ∂μ) at hFixed
  have hT1 : (∫ω,(1-b)*quadraticForm (upperSquareWeight R) X ω ∂μ)=1-b := by
    rw [integral_const_mul,hiso.quadratic_mean,upperSquareWeight_trace hR,mul_one]
  rw [integral_add ((hiso.quadratic_integrable _).const_mul (1-b)) hYQi,hT1] at hFixed
  have hid : (∫ω,Y ω*Q ω ∂μ)=m*(∫ω,W ω*Q ω ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by dsimp [W]; field_simp
  rw [hid] at hFixed
  change m≤1
  change m≤1-b+m*(∫ω,W ω*Q ω ∂μ) at hFixed
  nlinarith [mul_le_mul_of_nonneg_left hWQ hm.le]

end
end SingularValueBounds.KL
