import SingularValueBounds.KL.Upper.EndpointNumerics
import SingularValueBounds.KL.Upper.EndpointMGF

/-! # Matrix boundary for the endpoint upper MGF (supplementary S1.6.4)

All auxiliary random variables below are the actual quadratic forms in the
printed proof, or the explicitly constructed standard Gaussian majorant.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1800000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem upperWeight_eq_normalized_square {R : Matrix ι ι ℝ} (hR : R.PosDef) (j : ι) :
    upperWeight hR.isHermitian.eigenvalues j=(upperNormalizedSpectrum R hR j)^2 := by
  have hf := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian] at hf
  unfold upperWeight upperNormalizedSpectrum
  rw [← real_spectral_trace_square hR.isHermitian,← hf]
  field_simp [(frobenius_pos hR).ne']

theorem upperSquareWeight_trace {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix.trace (upperSquareWeight R)=1 := by
  unfold upperSquareWeight
  rw [Matrix.trace_smul]
  simp only [smul_eq_mul]
  exact inv_mul_cancel₀ (trace_square_pos hR).ne'

theorem upperWeightedMean_normalized {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    upperWeightedMean hR.isHermitian.eigenvalues=frobenius R*upperComparisonShapeMean R hR := by
  unfold upperWeightedMean upperComparisonShapeMean normalizedUpperMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [upperWeight_eq_normalized_square hR]
  unfold upperNormalizedSpectrum
  field_simp [(frobenius_pos hR).ne']
  <;> ring

theorem product_inv_sqrt_eq_exp_log {d : ι → ℝ} (hd : ∀j,0<d j) :
    (∏j,(Real.sqrt (d j))⁻¹)=Real.exp (-(∑j,Real.log (d j))/2) := by
  have he (j : ι) : (Real.sqrt (d j))⁻¹=Real.exp (-Real.log (d j)/2) := by
    rw [← Real.exp_log (inv_pos.mpr (Real.sqrt_pos.mpr (hd j))),Real.log_inv,
      Real.log_sqrt (hd j).le]
    congr 1
    ring
  simp_rw [he]
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div,Finset.sum_neg_distrib]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual comparison-quadratic MGF in each concentrated spectral row. -/
theorem upperComparison_endpoint_log_mgf (hcert : EndpointLogratioCertificateConditions)
    {X : Ω → ι → ℝ} (hsg : SubGaussianMGF μ X 1) (hm : Measurable X)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (i : Fin 3) (top : ι)
    (hκ : upperNormalizedSpectrum R hR top∈Icc
      (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    Integrable (fun ω => Real.exp (((6/5 : ℝ)/frobenius R)*
      quadraticForm (upperFixedComparison R) X ω)) μ ∧
      Real.log (∫ω,Real.exp (((6/5 : ℝ)/frobenius R)*
        quadraticForm (upperFixedComparison R) X ω) ∂μ)≤
        ((6/5 : ℝ)/frobenius R)*Matrix.trace (upperFixedComparison R)+endpointLogMGFCost i := by
  let η := frobenius R
  let x := upperNormalizedSpectrum R hR
  let c := normalizedUpperEigenvalue x
  let d := upperFixedEigenvalue hR.isHermitian.eigenvalues
  let U := hR.isHermitian.eigenvectorUnitary
  have hη : 0<η := frobenius_pos hR
  have hx : ∀j,0<x j := fun j => div_pos (hR.eigenvalues_pos j) hη
  have h2 := (upperNormalizedSpectrum_properties hR).2
  obtain ⟨hgap,hsum⟩ := endpoint_spectral_logdet hcert i hx h2 top hκ
  have hc0 : ∀j,0≤c j := fun j => normalized_upper_eigenvalue_nonneg (fun k => (hx k).le) j
  have hd (j : ι) : d j=η*c j := upperFixedEigenvalue_normalized hR j
  have hgapd : ∀j,0<1-2*(1 : ℝ)^2*((6/5 : ℝ)/η)*d j := by
    intro j
    rw [hd]
    convert hgap j using 1
    field_simp [hη.ne']
    <;> ring
  have hb := unitary_quadratic_exponential_bound hsg hm U d
    (fun j => by rw [hd]; exact mul_nonneg hη.le (hc0 j)) ((6/5 : ℝ)/η) (by positivity) hgapd
  rw [← upperFixedComparison_spectral hR] at hb
  refine ⟨hb.1, ?_⟩
  have hprod : (∏j,(Real.sqrt (1-2*(1 : ℝ)^2*((6/5 : ℝ)/η)*d j))⁻¹)=
      Real.exp (-(∑j,Real.log (1-(12/5 : ℝ)*c j))/2) := by
    have hid (j : ι) : 1-2*(1 : ℝ)^2*((6/5 : ℝ)/η)*d j=1-(12/5 : ℝ)*c j := by
      rw [hd]
      field_simp [hη.ne']
      <;> ring
    simp_rw [hid]
    exact product_inv_sqrt_eq_exp_log hgap
  rw [hprod] at hb
  have hlog := Real.log_le_log (integral_exp_pos hb.1) hb.2
  rw [Real.log_exp] at hlog
  have htrace : Matrix.trace (upperFixedComparison R)=η*∑j,c j := by
    rw [upperFixedComparison_normalized_spectral hR,Matrix.trace_smul,
      unitary_conjugate_trace,Matrix.trace_diagonal]
    rfl
  have hn := endpoint_row_log_bounds i
  have hidentity : (∑j,endpointLogExcess ((12/5 : ℝ)*c j))=
      -(∑j,Real.log (1-(12/5 : ℝ)*c j))-(12/5 : ℝ)*∑j,c j := by
    simp only [endpointLogExcess,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
      ← Finset.mul_sum]
  rw [hidentity] at hsum
  rw [htrace]
  dsimp [endpointLogMGFCost,endpointLogExcess] at hsum ⊢
  have hscale : ((6/5 : ℝ)/η)*(η*∑j,c j)=(6/5 : ℝ)*∑j,c j := by field_simp [hη.ne'] <;> ring
  rw [hscale]
  linarith [hn.1,hn.2]

/-- The three event probabilities for the actual comparison quadratic form. -/
theorem upperComparison_endpoint_rare_probability
    (hcert : EndpointLogratioCertificateConditions)
    {X : Ω → ι → ℝ} (hsg : SubGaussianMGF μ X 1) (hm : Measurable X)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (i : Fin 3) (top : ι)
    {b w : ℝ} (hw : (23/10 : ℝ)≤w)
    (hcap : Matrix.trace R+w*frobenius R≤b)
    (hκ : upperNormalizedSpectrum R hR top∈Icc
      (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    μ.real {ω | b<quadraticForm (upperFixedComparison R) X ω}≤
      (endpointRareRow i).probability := by
  let η := frobenius R
  let Q := quadraticForm (upperFixedComparison R) X
  let lam := (6/5 : ℝ)/η
  have hη : 0<η := frobenius_pos hR
  have hlam : 0<lam := by dsimp [lam]; positivity
  obtain ⟨hi,hl⟩ := upperComparison_endpoint_log_mgf hcert hsg hm hR i top hκ
  have hp := measure_ge_le_exp_mul_mgf (μ := μ) (X := Q) b hlam.le hi
  have hmgf : (∫ω,Real.exp (lam*Q ω) ∂μ)≤
      Real.exp (lam*Matrix.trace (upperFixedComparison R)+endpointLogMGFCost i) := by
    have hh := Real.exp_le_exp.mpr hl
    rw [Real.exp_log (integral_exp_pos hi)] at hh
    exact hh
  have hrow := endpoint_spectral_row_bounds i
    (fun j => (upperNormalizedSpectrum_properties hR).1 j)
    (upperNormalizedSpectrum_properties hR).2 top hκ
  have hgap : (endpointSpectralRow i).gap*η≤b-Matrix.trace (upperFixedComparison R) := by
    rw [upperFixedComparison_trace hR,upperSquareWeight_mean hR,upperWeightedMean_normalized hR]
    have hd := hrow.2.2.2.2.2.2
    have hh := mul_le_mul_of_nonneg_right hd hη.le
    change (endpointSpectralRow i).gap*η≤_ at hh
    dsimp [upperComparisonShapeMean] at ⊢
    nlinarith [mul_le_mul_of_nonneg_right hw hη.le]
  have hlamgap : (6/5 : ℝ)*(endpointSpectralRow i).gap≤
      lam*(b-Matrix.trace (upperFixedComparison R)) := by
    have hh := mul_le_mul_of_nonneg_left hgap hlam.le
    have hid : lam*((endpointSpectralRow i).gap*η)=(6/5 : ℝ)*(endpointSpectralRow i).gap := by
      dsimp [lam]
      field_simp [hη.ne']
      <;> ring
    rwa [hid] at hh
  calc
    _ ≤ μ.real {ω | b≤Q ω} := by
      apply measureReal_mono _ (measure_ne_top μ _)
      intro ω hω
      change b<Q ω at hω
      exact hω.le
    _ ≤ Real.exp (-lam*b)*(∫ω,Real.exp (lam*Q ω) ∂μ) := by simpa only [mgf] using hp
    _ ≤ Real.exp (-lam*b)*Real.exp (lam*Matrix.trace (upperFixedComparison R)+endpointLogMGFCost i) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (endpointLogMGFCost i-lam*(b-Matrix.trace (upperFixedComparison R))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (endpointLogMGFCost i-(6/5 : ℝ)*(endpointSpectralRow i).gap) :=
      Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := endpoint_row_probability_exponential i

end
end SingularValueBounds.KL
