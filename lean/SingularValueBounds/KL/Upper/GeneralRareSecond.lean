import SingularValueBounds.KL.Upper.GeneralSecondAnalytic

/-! The actual rare-event second-moment reduction in S1.6.4. -/
open MeasureTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1500000
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem second_moment_good_event {Y T : Ω → ℝ} {E : Set Ω}
    (hE : MeasurableSet E) (hY0 : ∀ ω,0 ≤ Y ω) (hT0 : ∀ ω,0 ≤ T ω)
    (hY2 : Integrable (fun ω=>Y ω^2) μ) (hT2 : Integrable (fun ω=>T ω^2) μ)
    (hgood : ∀ ω,ω∉E → Y ω ≤ T ω) :
    (∫ ω,Y ω^2 ∂μ) ≤ (∫ ω,T ω^2 ∂μ)+(∫ ω in E,Y ω^2 ∂μ) := by
  have hpoint (ω : Ω) : Y ω^2 ≤ T ω^2+E.indicator (fun ω=>Y ω^2) ω := by
    by_cases hω : ω∈E
    · simp only [Set.indicator_of_mem hω]
      linarith [sq_nonneg (T ω)]
    · simp only [Set.indicator_of_notMem hω,add_zero]
      exact pow_le_pow_left₀ (hY0 ω) (hgood ω hω) 2
  have h := integral_mono hY2 (hT2.add (hY2.indicator hE)) hpoint
  change (∫ ω,Y ω^2 ∂μ) ≤ (∫ ω,T ω^2+E.indicator (fun ω=>Y ω^2) ω ∂μ) at h
  rw [integral_add hT2 (hY2.indicator hE),integral_indicator hE] at h
  exact h

theorem upperSquareWeight_trace_square {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix.trace (upperSquareWeight R^2) = ∑j,upperNormalizedSpectrum R hR j^4 := by
  have h := congrArg (fun P : Matrix ι ι ℝ => Matrix.trace (P^2)) (upperSquareWeight_spectral hR)
  simp only [pow_two] at h
  rw [unitary_conjugate_mul,Matrix.diagonal_mul_diagonal,unitary_conjugate_trace,Matrix.trace_diagonal] at h
  simp_rw [upperWeight_eq_normalized_square hR] at h
  rw [← pow_two] at h
  calc
    _ = ∑j,upperNormalizedSpectrum R hR j^2*upperNormalizedSpectrum R hR j^2 := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem upperSquareWeight_endpoint_fourth {X : Ω → ι → ℝ} {K m4 : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hm4 : 0 ≤ m4)
    (hfourth : ∀ u : ι → ℝ,(∫ ω,(u ⬝ᵥ X ω)^4 ∂μ) ≤ m4*(u ⬝ᵥ u)^2)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (i : Fin 3) (top : ι)
    (hκ : upperNormalizedSpectrum R hR top∈Icc (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    (∫ ω,quadraticForm (upperSquareWeight R) X ω^2 ∂μ) ≤
      m4*(1+2*(endpointRareRow i).zeta)/3 := by
  have h := quadratic_second_of_directional_fourth hsg hm hm4 hfourth
    (upperSquareWeight R) (upperSquareWeight_posDef hR).posSemidef
  rw [upperSquareWeight_trace hR,upperSquareWeight_trace_square hR] at h
  have hmass := endpoint_spectral_fourth_mass i (upperNormalizedSpectrum_properties hR).1
    (upperNormalizedSpectrum_properties hR).2 top hκ
  nlinarith [mul_nonneg hm4 (sub_nonneg.mpr hmass)]

theorem upperShift_general_rare_second
    (hcert : EndpointLogratioCertificateConditions) {X : Ω → ι → ℝ} {K d m4 : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 0 < K) (hd : 0 ≤ d)
    (hm4 : 0 ≤ m4)
    (hfourth : ∀ u : ι → ℝ,(∫ ω,(u ⬝ᵥ X ω)^4 ∂μ) ≤ m4*(u ⬝ᵥ u)^2)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (i : Fin 3) (top : ι)
    {b w : ℝ} (hw : (23/10:ℝ) ≤ w)
    (hcap : K^2*Matrix.trace R+w*K^2*(1+d)*frobenius R ≤ b) (hb : b < 1)
    (hκ : upperNormalizedSpectrum R hR top∈Icc (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    (∫ ω,((1-b)*upperShift R hR (X ω))^2 ∂μ)/2 ≤
      m4*(1+2*(endpointRareRow i).zeta)/6+
      (endpointRareRow i).probability*Real.exp (-((69/25:ℝ)*d))*K^4*
        tailMomentSeries 3 ((endpointRareRow i).cutoff+6*d) (50/23) := by
  let Y := fun ω=>(1-b)*upperShift R hR (X ω)
  let T := quadraticForm (upperSquareWeight R) X
  let Q := quadraticForm (upperFixedComparison R) X
  let E := {ω | b<Q ω}
  have hY : Measurable Y := by
    have hp : Measurable (fun ω=>((⟨R,hR⟩:{R:Matrix ι ι ℝ//R.PosDef}),X ω)) :=
      measurable_const.prodMk hiso.measurable
    exact measurable_const.mul (by simpa only [Function.comp_def] using (measurable_upperShift (ι:=ι)).comp hp)
  have hQ : Measurable Q := by have hmX:=hiso.measurable; unfold Q quadraticForm dotProduct Matrix.mulVec; fun_prop
  have hE : MeasurableSet E := measurableSet_lt measurable_const hQ
  have hY0 (ω : Ω) : 0 ≤ Y ω := mul_nonneg (sub_pos.mpr hb).le (upperShift_nonneg hR _)
  have hT0 := quadraticForm_nonneg (upperSquareWeight_posDef hR).posSemidef X
  have htrace : K^2*Matrix.trace R ≤ b := by
    have hw0 : 0 ≤ w := by linarith
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hw0 (sq_nonneg K)) (by linarith : 0 ≤ 1+d)) (frobenius_pos hR).le]
  have hTail : ∀ u,0 ≤ u → μ.real {ω | u<Y ω} ≤ (177/50:ℝ)*Real.exp (-((23/(50*K^2))*u)) := by
    intro u hu
    have h := upperShift_tail_family hsg hiso.measurable hK hR htrace hb (q:=23/25) (by norm_num) (by norm_num) hu
    have hs : (Real.sqrt (1-(23/25:ℝ)))⁻¹ ≤ (177/50:ℝ) := by
      have hn := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1-23/25)
      have hp := Real.sqrt_pos.2 (by norm_num : (0:ℝ)<1-23/25)
      rw [← one_div]
      apply (div_le_iff₀ hp).2
      nlinarith
    have hh := h.trans (mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _))
    convert! hh using 1 <;> congr 2 <;> ring
  have hY2 := (exponential_tail_moment hY.aemeasurable hY0 (by norm_num : (0:ℝ)≤177/50)
    (by positivity : 0 < 23/(50*K^2)) hTail 1).1
  have hprob := upperComparison_general_rare_probability hcert hsg hK hd hiso.measurable hR i top hw hcap hκ
  have hp0 : 0 ≤ (endpointRareRow i).probability := (endpointRareRow_bounds i).1.le
  have hA0 : 0 ≤ (endpointRareRow i).cutoff+6*d := by
    have hh : 0 ≤ (endpointRareRow i).cutoff := (endpointRareRow_bounds i).2.1
    linarith
  have hcut : (177/50:ℝ)*Real.exp (-((23/(50*K^2))*(K^2*((endpointRareRow i).cutoff+6*d)))) ≤
      (endpointRareRow i).probability*Real.exp (-((69/25:ℝ)*d)) := by
    have hh := mul_le_mul_of_nonneg_right (endpoint_row_cutoff i) (Real.exp_nonneg (-((69/25:ℝ)*d)))
    rw [mul_assoc,← Real.exp_add] at hh
    convert! hh using 1
    congr 2
    field_simp
    <;> ring
  obtain ⟨hRare,hRareBound⟩ := rare_event_moment hY hY0 hE
    (mul_nonneg hp0 (Real.exp_nonneg _)) (by norm_num : (0:ℝ)≤177/50)
    (by positivity : 0<23/(50*K^2)) (mul_nonneg (sq_nonneg K) hA0) hprob hTail hcut 2
  have hgood (ω : Ω) (hω : ω∉E) : Y ω ≤ T ω := by
    have hqb : Q ω ≤ b := le_of_not_gt hω
    have hh := upperShift_fixed_comparison hR (X ω)
    have hδ := upperShift_nonneg hR (X ω)
    dsimp [Y,T,Q,quadraticForm] at *
    nlinarith [mul_le_mul_of_nonneg_left hqb hδ]
  have hsplit := second_moment_good_event hE hY0 hT0 hY2
    (hsg.quadratic_memLp_two (upperSquareWeight R)).integrable_sq hgood
  have hTbound := upperSquareWeight_endpoint_fourth hsg hiso.measurable hm4 hfourth hR i top hκ
  have hscale : tailMomentSeries 3 (K^2*((endpointRareRow i).cutoff+6*d)) (1/(23/(50*K^2))) =
      K^4*tailMomentSeries 3 ((endpointRareRow i).cutoff+6*d) (50/23) := by
    norm_num [tailMomentSeries,Finset.sum_range_succ]
    ring
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hRareBound
  rw [hscale] at hRareBound
  dsimp [Y,T] at *
  nlinarith

end
end SingularValueBounds.KL
