import SingularValueBounds.KL.Upper.EndpointGaussian

/-! # Endpoint upper MGF for the exact shift (supplementary S1.6.4)

Only the finite rational Bernstein certificate is external. All probability,
spectral, Gaussian-series and infinite-series arguments are proved in Lean.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1800000
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upperShift_endpoint_high_mgf
    (hcert : EndpointLogratioCertificateConditions)
    {X : Ω → ι → ℝ} (hiso : CentredIsotropic μ X)
    (hsg : SubGaussianMGF μ X 1) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (i : Fin 3) (top : ι)
    (hκ : upperNormalizedSpectrum R hR top∈Icc
      (endpointSpectralRow i).lo (endpointSpectralRow i).hi)
    {b w t : ℝ} (hw : (23/10 : ℝ)≤w)
    (hcap : Matrix.trace R+w*frobenius R≤b) (hb : b<1)
    (hMean : (∫ω,(1-b)*upperShift R hR (X ω) ∂μ)≤1)
    (ht : 0≤t) (ht4 : 4*t<1) :
    Integrable (fun ω => Real.exp (t*((1-b)*upperShift R hR (X ω)))) μ ∧
      (∫ω,Real.exp (t*((1-b)*upperShift R hR (X ω))) ∂μ)≤
        Real.exp (t/(1-4*t)) := by
  let Y := fun ω => (1-b)*upperShift R hR (X ω)
  let T := quadraticForm (upperSquareWeight R) X
  let Q := quadraticForm (upperFixedComparison R) X
  let E := {ω | b<Q ω}
  let x := upperNormalizedSpectrum R hR
  let G := endpointGaussian x
  have hY : Measurable Y := by
    have hp : Measurable (fun ω =>
        ((⟨R,hR⟩ : {R : Matrix ι ι ℝ // R.PosDef}),X ω)) :=
      measurable_const.prodMk hiso.measurable
    exact measurable_const.mul (by
      simpa only [Function.comp_def] using (measurable_upperShift (ι := ι)).comp hp)
  have hY0 : ∀ω,0≤Y ω := fun ω =>
    mul_nonneg (sub_pos.mpr hb).le (upperShift_nonneg hR (X ω))
  have hG0 : ∀g,0≤G g := by
    intro g
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hG : Measurable G := by unfold G endpointGaussian; fun_prop
  have hE : MeasurableSet E := by
    have hm := hiso.measurable
    have hQ : Measurable Q := by
      change Measurable (fun ω => quadraticForm (upperFixedComparison R) X ω)
      simp_rw [quadraticForm_eq_sum]
      fun_prop
    exact measurableSet_lt measurable_const hQ
  have hx := upperNormalizedSpectrum_properties hR
  have hGMom (p : ℕ) := standardGaussian_quadratic_moment_le
    (fun j => sq_nonneg (x j)) hx.2 p
  have hComp := upperSquareWeight_gaussian_mgf hsg hiso.measurable hR ht ht4
  have htrace : Matrix.trace R≤b := by
    have hη := (frobenius_pos hR).le
    nlinarith
  have hTail : ∀u,0≤u → μ.real {ω | u<Y ω}≤
      (177/50 : ℝ)*Real.exp (-((23/50 : ℝ)*u)) := by
    intro u hu
    have h := upperShift_tail_family hsg hiso.measurable (by norm_num : (0 : ℝ)<1)
      hR (by simpa using htrace) hb (by norm_num : (0 : ℝ)<23/25)
      (by norm_num : (23/25 : ℝ)<1) hu
    have hs0 : 0<Real.sqrt (1-(23/25 : ℝ)) := Real.sqrt_pos.mpr (by norm_num)
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ)≤1-(23/25 : ℝ))
    have hs : (Real.sqrt (1-(23/25 : ℝ)))⁻¹≤(177/50 : ℝ) := by
      rw [← one_div]
      apply (div_le_iff₀ hs0).2
      nlinarith
    have he : -(23/25*u/(2*(1 : ℝ)^2))=-(23/50*u) := by ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _))
  apply endpoint_mgf_of_rare_gaussian (ν := standardGaussian ι) (Y := Y) (T := T)
    (G := G) (E := E) i hY hY0 hG.aemeasurable hG0 hE ht ht4 hMean
    (hiso.quadratic_integrable _) ((hiso.quadratic_mean _).trans (upperSquareWeight_trace hR))
    (endpointGaussian_mean hx.2) (fun p => (hGMom p).1) hComp.1 hComp.2
  · intro ω hω
    have hQ : Q ω≤b := le_of_not_gt hω
    have hh := upperShift_fixed_comparison hR (X ω)
    have hmul := mul_le_mul_of_nonneg_left hQ (upperShift_nonneg hR (X ω))
    change Y ω≤T ω
    dsimp [Y,T,Q,quadraticForm] at *
    nlinarith
  · exact upperComparison_endpoint_rare_probability hcert hsg hiso.measurable hR i top hw hcap hκ
  · exact hTail
  · exact endpoint_row_cutoff i
  · exact endpointGaussian_second i hx.2 top hκ
  · intro p hp
    exact (hGMom p).2

/-- Lemma S1.12: endpoint variance factor four, from the endpoint mean bound.
The rare event need not be independent of any quadratic form. -/
theorem upperShift_endpoint_mgf_of_mean
    (hcert : EndpointLogratioCertificateConditions)
    {X : Ω → ι → ℝ} (hiso : CentredIsotropic μ X)
    (hsg : SubGaussianMGF μ X 1) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {b w t : ℝ} (hw : (23/10 : ℝ)≤w)
    (hcap : Matrix.trace R+w*frobenius R≤b) (hb : b<1)
    (hMean : (∫ω,(1-b)*upperShift R hR (X ω) ∂μ)≤1)
    (ht : 0≤t) (ht4 : 4*t<1) :
    Integrable (fun ω => Real.exp (t*((1-b)*upperShift R hR (X ω)))) μ ∧
      (∫ω,Real.exp (t*((1-b)*upperShift R hR (X ω))) ∂μ)≤
        Real.exp (t/(1-4*t)) := by
  let x := upperNormalizedSpectrum R hR
  have hx := upperNormalizedSpectrum_properties hR
  obtain ⟨top,htop,hmax⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  have hx1 : x top≤1 := by
    have hh := Finset.single_le_sum (s := Finset.univ) (fun j hj => sq_nonneg (x j))
      (Finset.mem_univ top)
    rw [hx.2] at hh
    nlinarith [hx.1 top]
  by_cases hLow : x top≤(15/16 : ℝ)
  · have hY : Measurable (fun ω => (1-b)*upperShift R hR (X ω)) := by
      have hp : Measurable (fun ω =>
          ((⟨R,hR⟩ : {R : Matrix ι ι ℝ // R.PosDef}),X ω)) :=
        measurable_const.prodMk hiso.measurable
      exact measurable_const.mul (by
        simpa only [Function.comp_def] using (measurable_upperShift (ι := ι)).comp hp)
    have htrace : Matrix.trace R≤b := by nlinarith [frobenius_pos hR]
    have hnorm : (frobenius R)^2=∑j,hR.isHermitian.eigenvalues j^2 := by
      rw [frobenius_eq_sqrt_trace_square hR.isHermitian,
        Real.sq_sqrt (trace_square_pos hR).le,real_spectral_trace_square hR.isHermitian]
    apply endpoint_mgf_of_low_tail hY
      (fun ω => mul_nonneg (sub_pos.mpr hb).le (upperShift_nonneg hR (X ω))) hMean
      (fun u hu => upperShift_endpoint_low_tail hsg hiso.measurable hR htrace hb
        (frobenius_pos hR) hnorm (fun j => ?_) hu) ht ht4
    have hh := (hmax j (Finset.mem_univ j)).trans hLow
    exact (div_le_iff₀ (frobenius_pos hR)).mp hh
  · have hPos : (15/16 : ℝ)≤x top := le_of_not_ge hLow
    by_cases h0 : x top≤(47/50 : ℝ)
    · exact upperShift_endpoint_high_mgf hcert hiso hsg hR 0 top
        (by simpa [endpointSpectralRow] using And.intro hPos h0) hw hcap hb hMean ht ht4
    · by_cases h1 : x top≤(19/20 : ℝ)
      · exact upperShift_endpoint_high_mgf hcert hiso hsg hR 1 top
          (by norm_num [endpointSpectralRow]; exact ⟨le_of_not_ge h0,h1⟩) hw hcap hb hMean ht ht4
      · exact upperShift_endpoint_high_mgf hcert hiso hsg hR 2 top
          (by norm_num [endpointSpectralRow]; exact ⟨le_of_not_ge h1,hx1⟩) hw hcap hb hMean ht ht4

end
end SingularValueBounds.KL
