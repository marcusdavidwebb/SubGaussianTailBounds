import SingularValueBounds.KL.Upper.EndpointApplication
import SingularValueBounds.KL.Upper.GeneralFourth

/-! Analytic general-K second-moment refinements: exact-shift tails,
rare-event splitting, and Gaussian fourth-moment averaging. -/
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1400000
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upperShift_general_low_tail {X : Ω → ι → ℝ} {K : ℝ} {R : Matrix ι ι ℝ}
    (hsg : SubGaussianMGF μ X K) (hK : 0 < K) (hm : Measurable X) (hR : R.PosDef)
    {b η u : ℝ} (hcap : K^2*Matrix.trace R≤b) (hb : b<1)
    (hη : 0<η) (hnorm : η^2=∑i,hR.isHermitian.eigenvalues i^2)
    (hmax : ∀i,hR.isHermitian.eigenvalues i≤(15/16 : ℝ)*η) (hu : 0≤u) :
    μ.real {ω | u<(1-b)*upperShift R hR (X ω)}≤
      (46/15 : ℝ)*Real.exp (-u/(2*K^2)) := by
  have hb0 : 0<1-b := by linarith
  by_cases hu0 : u=0
  · subst u
    norm_num
    exact (measureReal_le_one (μ := μ)).trans (by norm_num)
  have huPos : 0<u := lt_of_le_of_ne hu (Ne.symm hu0)
  let h := u/(1-b)
  have hh : 0<h := div_pos huPos hb0
  obtain ⟨hgap,hlog⟩ := endpoint_capped_spectral_cost hR.eigenvalues_pos hh.le hη hnorm hmax
  rw [← real_spectral_trace hR.isHermitian] at hlog
  have ht := upperShift_tail_of_spectral_logdet hsg hm hK
    hR hh (q := 1) (by norm_num) (by simpa using hgap) (by simpa using hlog)
  have hevent : {ω | u<(1-b)*upperShift R hR (X ω)}={ω | h<upperShift R hR (X ω)} := by
    ext ω
    change u<(1-b)*upperShift R hR (X ω) ↔ u/(1-b)<upperShift R hR (X ω)
    rw [div_lt_iff₀ hb0,mul_comm]
  rw [hevent]
  norm_num only [one_pow,one_mul,mul_one] at ht
  have hscaled : u≤h*(1-K^2*Matrix.trace R) := by
    have he : h*(1-b)=u := by dsimp [h]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hcap hh.le]
  calc
    _ ≤ Real.exp (2*Real.log (46/15 : ℝ)/2-h*(1-K^2*Matrix.trace R)/(2*K^2)) := ht
    _ ≤ Real.exp (Real.log (46/15 : ℝ)-u/(2*K^2)) := Real.exp_le_exp.mpr (by
      have hh := div_le_div_of_nonneg_right hscaled (show 0 ≤ 2*K^2 by positivity)
      linarith)
    _ = _ := by rw [Real.exp_sub,Real.exp_log (by norm_num : (0 : ℝ)<46/15),
        div_eq_mul_inv,← Real.exp_neg]; congr 2; ring


theorem upperComparison_general_log_mgf (hcert : EndpointLogratioCertificateConditions)
    {X : Ω → ι → ℝ} {K : ℝ} (hsg : SubGaussianMGF μ X K) (hK : 0 < K) (hm : Measurable X)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (i : Fin 3) (top : ι)
    (hκ : upperNormalizedSpectrum R hR top∈Icc
      (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    Integrable (fun ω => Real.exp (((6/5 : ℝ)/(K^2*frobenius R))*
      quadraticForm (upperFixedComparison R) X ω)) μ ∧
      Real.log (∫ω,Real.exp (((6/5 : ℝ)/(K^2*frobenius R))*
        quadraticForm (upperFixedComparison R) X ω) ∂μ)≤
        ((6/5 : ℝ)/(K^2*frobenius R))*K^2*Matrix.trace (upperFixedComparison R)+endpointLogMGFCost i := by
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
  have hgapd : ∀j,0<1-2*K^2*((6/5 : ℝ)/(K^2*η))*d j := by
    intro j
    rw [hd]
    convert! hgap j using 1
    field_simp [hη.ne',hK.ne']
    <;> ring
  have hb := unitary_quadratic_exponential_bound hsg hm U d
    (fun j => by rw [hd]; exact mul_nonneg hη.le (hc0 j)) ((6/5 : ℝ)/(K^2*η)) (by positivity) hgapd
  rw [← upperFixedComparison_spectral hR] at hb
  refine ⟨hb.1, ?_⟩
  have hprod : (∏j,(Real.sqrt (1-2*K^2*((6/5 : ℝ)/(K^2*η))*d j))⁻¹)=
      Real.exp (-(∑j,Real.log (1-(12/5 : ℝ)*c j))/2) := by
    have hid (j : ι) : 1-2*K^2*((6/5 : ℝ)/(K^2*η))*d j=1-(12/5 : ℝ)*c j := by
      rw [hd]
      field_simp [hη.ne',hK.ne']
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
  have hscale : ((6/5 : ℝ)/(K^2*η))*K^2*(η*∑j,c j)=(6/5 : ℝ)*∑j,c j := by field_simp [hη.ne',hK.ne'] <;> ring
  rw [hscale]
  linarith [hn.1,hn.2]



theorem upperComparison_general_rare_probability
    (hcert : EndpointLogratioCertificateConditions)
    {X : Ω → ι → ℝ} {K d : ℝ} (hsg : SubGaussianMGF μ X K) (hK : 0 < K) (hd : 0 ≤ d) (hm : Measurable X)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (i : Fin 3) (top : ι)
    {b w : ℝ} (hw : (23/10 : ℝ)≤w)
    (hcap : K^2*Matrix.trace R+w*K^2*(1+d)*frobenius R≤b)
    (hκ : upperNormalizedSpectrum R hR top∈Icc
      (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    μ.real {ω | b<quadraticForm (upperFixedComparison R) X ω}≤
      (endpointRareRow i).probability*Real.exp (-((69/25:ℝ)*d)) := by
  let η := frobenius R
  let Q := quadraticForm (upperFixedComparison R) X
  let lam := (6/5 : ℝ)/(K^2*η)
  have hη : 0<η := frobenius_pos hR
  have hlam : 0<lam := by dsimp [lam]; positivity
  obtain ⟨hi,hl⟩ := upperComparison_general_log_mgf hcert hsg hK hm hR i top hκ
  have hp := measure_ge_le_exp_mul_mgf (μ := μ) (X := Q) b hlam.le hi
  have hmgf : (∫ω,Real.exp (lam*Q ω) ∂μ)≤
      Real.exp (lam*K^2*Matrix.trace (upperFixedComparison R)+endpointLogMGFCost i) := by
    have hh := Real.exp_le_exp.mpr hl
    rw [Real.exp_log (integral_exp_pos hi)] at hh
    exact hh
  have hrow := endpoint_spectral_row_bounds i
    (fun j => (upperNormalizedSpectrum_properties hR).1 j)
    (upperNormalizedSpectrum_properties hR).2 top hκ
  have hgap : K^2*η*((endpointSpectralRow i).gap+(23/10:ℝ)*d) ≤
      b-K^2*Matrix.trace (upperFixedComparison R) := by
    rw [upperFixedComparison_trace hR,upperSquareWeight_mean hR,upperWeightedMean_normalized hR]
    have hrowgap := hrow.2.2.2.2.2.2
    have hh := mul_le_mul_of_nonneg_left hrowgap (mul_nonneg (sq_nonneg K) hη.le)
    have hw' := mul_le_mul_of_nonneg_right hw (show 0 ≤ K^2*(1+d)*η by positivity)
    dsimp [upperComparisonShapeMean] at ⊢
    nlinarith
  have hlamgap : (6/5:ℝ)*(endpointSpectralRow i).gap+(69/25:ℝ)*d ≤
      lam*(b-K^2*Matrix.trace (upperFixedComparison R)) := by
    have hh := mul_le_mul_of_nonneg_left hgap hlam.le
    have hid : lam*(K^2*η*((endpointSpectralRow i).gap+(23/10:ℝ)*d)) =
        (6/5:ℝ)*(endpointSpectralRow i).gap+(69/25:ℝ)*d := by
      dsimp [lam]
      field_simp [hη.ne',hK.ne']
      <;> ring
    rwa [hid] at hh
  calc
    _ ≤ μ.real {ω | b≤Q ω} := by
      apply measureReal_mono _ (measure_ne_top μ _)
      intro ω hω
      change b<Q ω at hω
      exact hω.le
    _ ≤ Real.exp (-lam*b)*(∫ω,Real.exp (lam*Q ω) ∂μ) := by simpa only [mgf] using hp
    _ ≤ Real.exp (-lam*b)*Real.exp (lam*K^2*Matrix.trace (upperFixedComparison R)+endpointLogMGFCost i) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (endpointLogMGFCost i-lam*(b-K^2*Matrix.trace (upperFixedComparison R))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (endpointLogMGFCost i-(6/5 : ℝ)*(endpointSpectralRow i).gap-(69/25:ℝ)*d) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (endpointLogMGFCost i-(6/5:ℝ)*(endpointSpectralRow i).gap)*
        Real.exp (-((69/25:ℝ)*d)) := by rw [Real.exp_sub,Real.exp_neg,div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_right (endpoint_row_probability_exponential i) (Real.exp_nonneg _)


end
end SingularValueBounds.KL
