import SingularValueBounds.KL.Upper.GeneralSecondRange
import SingularValueBounds.KL.Upper.MGFSeries

/-! General upper exponential moment: actual matrix second moments, the
finite fourth-exclusion family, and the complete moment-series consequence. -/
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators NNReal
namespace SingularValueBounds.KL
open UpperSecond
noncomputable section
set_option maxHeartbeats 1800000
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem directional_fourth_of_unit {X : Ω → ι → ℝ} {m4 : ℝ}
    (hunit : ∀ v : ι → ℝ,v ⬝ᵥ v=1 → (∫ ω,(v ⬝ᵥ X ω)^4 ∂μ) ≤ m4)
    (u : ι → ℝ) : (∫ ω,(u ⬝ᵥ X ω)^4 ∂μ) ≤ m4*(u ⬝ᵥ u)^2 := by
  by_cases hu : u=0
  · simp [hu]
  have hu2 : 0 < u ⬝ᵥ u := by simpa only [star_trivial] using Matrix.dotProduct_star_self_pos_iff.mpr hu
  let r := Real.sqrt (u ⬝ᵥ u)
  have hr : 0 < r := Real.sqrt_pos.2 hu2
  have hr2 : r^2=u ⬝ᵥ u := Real.sq_sqrt hu2.le
  let v := r⁻¹ • u
  have hv : v ⬝ᵥ v=1 := by
    simp only [v,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    calc
      r⁻¹*(r⁻¹*(u ⬝ᵥ u))=(u ⬝ᵥ u)/r^2 := by ring
      _ = 1 := by rw [hr2,div_self hu2.ne']
  have hp (ω : Ω) : (u ⬝ᵥ X ω)^4=r^4*(v ⬝ᵥ X ω)^4 := by
    simp only [v,smul_dotProduct,smul_eq_mul,mul_pow]
    field_simp [hr.ne']
  calc
    _ = r^4*(∫ ω,(v ⬝ᵥ X ω)^4 ∂μ) := by simp_rw [hp]; rw [integral_const_mul]
    _ ≤ r^4*m4 := mul_le_mul_of_nonneg_left (hunit v hv) (by positivity)
    _ = _ := by rw [← hr2]; ring

theorem general_second_uniform_fourth
    (hcert : GeneralSecondCertificateConditions) {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    (hL : logParameter K < 5/4) :
    ∃ m4 : ℝ,0 ≤ m4 ∧
      (∀ u : ι → ℝ,(∫ ω,(u ⬝ᵥ X ω)^4 ∂μ) ≤ m4*(u ⬝ᵥ u)^2) ∧
      (∀ i : Fin 3,generalSecondScalar i m4 (logParameter K-1) ≤ 9/2) := by
  have hK0 : 0 < K := by linarith
  have hL1 := one_le_logParameter hK
  have hL0 : 0 < logParameter K := by linarith
  rcases general_second_range_coverage (logParameter K) with hs|⟨j,hj⟩|hl
  · refine ⟨4,by norm_num,?_,?_⟩
    · apply directional_fourth_of_unit
      intro v hv
      have hsgv : HasSubgaussianMGF (fun ω=>v ⬝ᵥ X ω) ⟨K^2,sq_nonneg K⟩ μ := by simpa [hv] using hsg.directional v
      exact (general_second_small_fourth hcert hsgv ((hiso.second_moment v).trans hv) hK0 hs).le
    · intro i
      exact general_second_small_bound hcert i le_rfl ⟨by linarith,by linarith⟩
  · refine ⟨(secondCellM j:ℝ),?_,?_,?_⟩
    · have hh := (hcert.2.2.2.1 j).2.2.2.2.2.2.m_pos
      exact_mod_cast hh.le
    · apply directional_fourth_of_unit
      intro v hv
      have hsgv : HasSubgaussianMGF (fun ω=>v ⬝ᵥ X ω) ⟨K^2,sq_nonneg K⟩ μ := by simpa [hv] using hsg.directional v
      exact (general_second_cell_fourth hcert hsgv ((hiso.second_moment v).trans hv) hK0 j hj.2).le
    · intro i
      exact general_second_cell_bound hcert j i le_rfl hj
  · exact (not_le_of_gt hL hl).elim

theorem general_rare_scalar_normalization (i : Fin 3) {K d m ey : ℝ}
    (hK : 0 < K) (hd : 0 ≤ d) (hpow : K^2=Real.exp (2*d))
    (hbound : ey/2 ≤ m*(1+2*(endpointRareRow i).zeta)/6+
      (endpointRareRow i).probability*Real.exp (-((69/25:ℝ)*d))*K^4*
        tailMomentSeries 3 ((endpointRareRow i).cutoff+6*d) (50/23)) :
    ey/(2*K^2*(1+d))-1/(2*K^2*(1+d)) ≤ generalSecondScalar i m d := by
  have hd1 : 1+d ≠ 0 := by linarith
  have hInv : 1/K^2=Real.exp (-2*d) := by
    rw [hpow,show -2*d=-(2*d) by ring,Real.exp_neg,one_div]
  have hExp : Real.exp (-((69/25:ℝ)*d))*K^2=Real.exp (-(19/25:ℝ)*d) := by
    rw [hpow,← Real.exp_add]
    congr 1
    ring
  have hn1 : (m*(1+2*(endpointRareRow i).zeta)/6)/(K^2*(1+d)) =
      m*Real.exp (-2*d)*(1+2*(endpointRareRow i).zeta)/(6*(1+d)) := by
    rw [← hInv]
    field_simp
  have hn2 : ((endpointRareRow i).probability*Real.exp (-((69/25:ℝ)*d))*K^4*
        tailMomentSeries 3 ((endpointRareRow i).cutoff+6*d) (50/23))/(K^2*(1+d)) = generalRareR i d := by
    calc
      _ = (endpointRareRow i).probability*(Real.exp (-((69/25:ℝ)*d))*K^2)*
        tailMomentSeries 3 ((endpointRareRow i).cutoff+6*d) (50/23)/(1+d) := by
          field_simp [hK.ne']
      _ = _ := by
        rw [hExp]
        norm_num [generalRareR,tailMomentSeries,Finset.sum_range_succ]
        ring
  have hn3 : 1/(2*K^2*(1+d))=Real.exp (-2*d)/(2*(1+d)) := by
    rw [← hInv]
    field_simp
  have hh := sub_le_sub_right (div_le_div_of_nonneg_right hbound
    (show 0 ≤ K^2*(1+d) by positivity)) (1/(2*K^2*(1+d)))
  rw [add_div,hn1,hn2,hn3] at hh
  dsimp [generalSecondScalar]
  rw [hn3]
  convert! hh using 1 <;> field_simp [hK.ne',hd1]

variable [DecidableEq ι] [Nonempty ι]

theorem upperShift_tail_nine_tenths {X : Ω → ι → ℝ} {K b : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (htrace : K^2*Matrix.trace R ≤ b) (hb : b<1) :
    ∀ u,0 ≤ u → μ.real {ω | u<(1-b)*upperShift R hR (X ω)} ≤
      Real.sqrt 10*Real.exp (-(9*u/(20*K^2))) := by
  intro u hu
  have h := upperShift_tail_family hsg hm hK hR htrace hb (q:=9/10) (by norm_num) (by norm_num) hu
  have he : (Real.sqrt (1-(9/10:ℝ)))⁻¹=Real.sqrt 10 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1-9/10)
    have ht := Real.sq_sqrt (by norm_num : (0:ℝ)≤10)
    have hp := Real.sqrt_pos.2 (by norm_num : (0:ℝ)<1-9/10)
    have hm : Real.sqrt (1-(9/10:ℝ))*Real.sqrt 10=1 := by nlinarith [Real.sqrt_nonneg 10]
    rw [← one_div]
    apply (div_eq_iff hp.ne').2
    nlinarith
  rw [he] at h
  convert! h using 1 <;> congr 2 <;> ring

theorem upperShift_general_high_second_of_mean
    (hcert : EndpointLogratioCertificateConditions) (hsecond : GeneralSecondCertificateConditions)
    {X : Ω → ι → ℝ} {K : ℝ} (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X)
    (hK : 1 ≤ K) (hL : logParameter K < 5/4)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (i : Fin 3) (top : ι)
    {b w : ℝ} (hw : (23/10:ℝ) ≤ w)
    (hcap : K^2*Matrix.trace R+w*K^2*logParameter K*frobenius R ≤ b) (hb : b<1)
    (hκ : upperNormalizedSpectrum R hR top∈Icc (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    (∫ ω,((1-b)*upperShift R hR (X ω))^2 ∂μ)/(2*K^2*logParameter K)-
      1/(2*K^2*logParameter K) ≤ (9/2:ℝ) := by
  have hK0 : 0 < K := by linarith
  have hd : 0 ≤ logParameter K-1 := by linarith [one_le_logParameter hK]
  obtain ⟨m4,hm4,hfourth,hScalar⟩ := general_second_uniform_fourth hsecond hsg hiso hK hL
  have hr := upperShift_general_rare_second hcert hsg hiso hK0 hd hm4 hfourth hR i top hw
    (by convert! hcap using 1 <;> ring) hb hκ
  have hh := general_rare_scalar_normalization i hK0 hd (K_sq_eq_exp_logParameter hK0) hr
  have hf := hh.trans (hScalar i)
  convert! hf using 1 <;> ring

theorem upperShift_general_second_of_mean
    (hcert : EndpointLogratioCertificateConditions) (hsecond : GeneralSecondCertificateConditions)
    {X : Ω → ι → ℝ} {K : ℝ} (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X)
    (hK : 1 ≤ K) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {b w : ℝ} (hw : (23/10:ℝ) ≤ w)
    (hcap : K^2*Matrix.trace R+w*K^2*logParameter K*frobenius R ≤ b) (hb : b<1)
    (hMean : (∫ ω,(1-b)*upperShift R hR (X ω) ∂μ) ≤ 1) :
    Integrable (fun ω=>((1-b)*upperShift R hR (X ω))^2) μ ∧
    (∫ ω,((1-b)*upperShift R hR (X ω))^2 ∂μ)/(2*K^2*logParameter K)-
      1/(2*K^2*logParameter K) ≤ (9/2:ℝ) := by
  let Y := fun ω=>(1-b)*upperShift R hR (X ω)
  have hK0 : 0 < K := by linarith
  have hL1 := one_le_logParameter hK
  have hL0 : 0 < logParameter K := by linarith
  have hY : Measurable Y := by
    have hp : Measurable (fun ω=>((⟨R,hR⟩:{R:Matrix ι ι ℝ//R.PosDef}),X ω)) := measurable_const.prodMk hiso.measurable
    exact measurable_const.mul (by simpa only [Function.comp_def] using (measurable_upperShift (ι:=ι)).comp hp)
  have hY0 (ω : Ω) : 0 ≤ Y ω := mul_nonneg (sub_pos.mpr hb).le (upperShift_nonneg hR _)
  have htrace : K^2*Matrix.trace R ≤ b := by
    have hw0 : 0 ≤ w := by linarith
    have hnon : 0 ≤ w*K^2*logParameter K*frobenius R :=
      mul_nonneg (mul_nonneg (mul_nonneg hw0 (sq_nonneg K)) hL0.le) (frobenius_pos hR).le
    linarith
  have hTail := upperShift_tail_nine_tenths hsg hiso.measurable hK0 hR htrace hb
  by_cases hlarge : (5/4:ℝ) ≤ logParameter K
  · have hh := upper_tail_second_moment hY hY0 hK rfl hlarge hMean hTail
    exact ⟨hh.1,hh.2.le⟩
  have hsmall : logParameter K < 5/4 := lt_of_not_ge hlarge
  have hi := (exponential_tail_moment hY.aemeasurable hY0 (Real.sqrt_nonneg 10)
    (by positivity : 0 < 9/(20*K^2)) (by
      intro u hu
      convert! hTail u hu using 1 <;> congr 2 <;> ring) 1).1
  refine ⟨hi,?_⟩
  let x := upperNormalizedSpectrum R hR
  have hx := upperNormalizedSpectrum_properties hR
  obtain ⟨top,htop,hmax⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  have hx1 : x top ≤ 1 := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (fun j _=>sq_nonneg (x j)) (Finset.mem_univ top)
    rw [hx.2] at hh
    nlinarith [hx.1 top]
  by_cases hlow : x top ≤ (15/16:ℝ)
  · have hnorm : frobenius R^2=∑ j,hR.isHermitian.eigenvalues j^2 := by
      rw [frobenius_eq_sqrt_trace_square hR.isHermitian,Real.sq_sqrt (trace_square_pos hR).le,
        real_spectral_trace_square hR.isHermitian]
    have htlow : ∀ u,0 ≤ u → μ.real {ω | u<Y ω} ≤ (46/15:ℝ)*Real.exp (-u/(2*K^2)) := by
      intro u hu
      exact upperShift_general_low_tail hsg hK0 hiso.measurable hR htrace hb (frobenius_pos hR) hnorm
        (fun j => (div_le_iff₀ (frobenius_pos hR)).1 ((hmax j (Finset.mem_univ j)).trans hlow)) hu
    have hd : 0 ≤ logParameter K-1 := by linarith
    have hh := (upper_low_second_of_tail hY hY0 hMean hK0 hd (K_sq_eq_exp_logParameter hK0) htlow).2
    have hf := hh.trans ((generalLowSecondCost_le_four hd).trans (by norm_num : (4:ℝ) ≤ 9/2))
    convert! hf using 1 <;> ring
  · have hpos : (15/16:ℝ) ≤ x top := le_of_not_ge hlow
    by_cases h0 : x top ≤ (47/50:ℝ)
    · exact upperShift_general_high_second_of_mean hcert hsecond hsg hiso hK hsmall hR 0 top hw hcap hb
        (by simpa [endpointSpectralRow] using And.intro hpos h0)
    · by_cases h1 : x top ≤ (19/20:ℝ)
      · exact upperShift_general_high_second_of_mean hcert hsecond hsg hiso hK hsmall hR 1 top hw hcap hb
          (by norm_num [endpointSpectralRow]; exact ⟨le_of_not_ge h0,h1⟩)
      · exact upperShift_general_high_second_of_mean hcert hsecond hsg hiso hK hsmall hR 2 top hw hcap hb
          (by norm_num [endpointSpectralRow]; exact ⟨le_of_not_ge h1,hx1⟩)

/-- Supplementary Lemma S1.13, retaining exactly the stated finite premises.
The endpoint mean and the complete moment-series proof supply the hypotheses. -/
theorem upperShift_general_mgf_of_mean
    (hcert : EndpointLogratioCertificateConditions) (hsecond : GeneralSecondCertificateConditions)
    {X : Ω → ι → ℝ} {K : ℝ} (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X)
    (hK : 1 ≤ K) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {b w t : ℝ} (hw : (23/10:ℝ) ≤ w)
    (hcap : K^2*Matrix.trace R+w*K^2*logParameter K*frobenius R ≤ b) (hb : b<1)
    (hMean : (∫ ω,(1-b)*upperShift R hR (X ω) ∂μ) ≤ 1)
    (ht : 0 ≤ t) (hvt : ((9/2:ℝ)*K^2*logParameter K)*t < 1) :
    Integrable (fun ω=>Real.exp (t*((1-b)*upperShift R hR (X ω)))) μ ∧
    (∫ ω,Real.exp (t*((1-b)*upperShift R hR (X ω))) ∂μ) ≤
      Real.exp (t/(1-((9/2:ℝ)*K^2*logParameter K)*t)) := by
  let Y := fun ω=>(1-b)*upperShift R hR (X ω)
  have hK0 : 0 < K := by linarith
  have hL1 := one_le_logParameter hK
  have hL0 : 0 < logParameter K := by linarith
  have hY : Measurable Y := by
    have hp : Measurable (fun ω=>((⟨R,hR⟩:{R:Matrix ι ι ℝ//R.PosDef}),X ω)) := measurable_const.prodMk hiso.measurable
    exact measurable_const.mul (by simpa only [Function.comp_def] using (measurable_upperShift (ι:=ι)).comp hp)
  have hY0 (ω : Ω) : 0 ≤ Y ω := mul_nonneg (sub_pos.mpr hb).le (upperShift_nonneg hR _)
  have htrace : K^2*Matrix.trace R ≤ b := by
    have hw0 : 0 ≤ w := by linarith
    have hnon : 0 ≤ w*K^2*logParameter K*frobenius R :=
      mul_nonneg (mul_nonneg (mul_nonneg hw0 (sq_nonneg K)) hL0.le) (frobenius_pos hR).le
    linarith
  have hTail := upperShift_tail_nine_tenths hsg hiso.measurable hK0 hR htrace hb
  have hTail' : ∀ u,0 ≤ u → μ.real {ω | u<Y ω} ≤ Real.sqrt 10*Real.exp (-((9/(20*K^2))*u)) := by
    intro u hu
    convert! hTail u hu using 1 <;> congr 2 <;> ring
  have hmom (p : ℕ) : Integrable (fun ω=>Y ω^p) μ := by
    cases p with
    | zero => simpa using integrable_const (1:ℝ)
    | succ p => exact (exponential_tail_moment hY.aemeasurable hY0 (Real.sqrt_nonneg 10)
        (by positivity : 0 < 9/(20*K^2)) hTail' p).1
  apply mgf_of_bernstein_moments hY.aemeasurable hY0 (by positivity : 0 ≤ (9/2:ℝ)*K^2*logParameter K)
    ht hvt hmom hMean
  · have hs := (upperShift_general_second_of_mean hcert hsecond hsg hiso hK hR hw hcap hb hMean).2
    have hd : 0 < 2*K^2*logParameter K := by positivity
    rw [← sub_div] at hs
    have hh := (div_le_iff₀ hd).1 hs
    norm_num
    dsimp [Y]
    nlinarith
  · intro p hp
    exact (upper_tail_higher_moments hY hY0 hK rfl hMean hTail p hp).2

end
end SingularValueBounds.KL
