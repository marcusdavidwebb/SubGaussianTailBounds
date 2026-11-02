import SingularValueBounds.KL.Lower.GeneralProfile
import SingularValueBounds.KL.Lower.EndpointCap

/-! Positive scaling of the normalized lower comparison. Only the comparison
matrix, not the nonlinear exact shift, is scaled. -/
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem lower_posDef_smul {R : Matrix ι ι ℝ} (hR : R.PosDef) {s : ℝ} (hs : 0<s) :
    (s • R).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · change (s • R)ᴴ=s • R
    simp only [Matrix.conjTranspose_smul,star_trivial,hR.isHermitian.eq]
  · intro x hx
    simpa only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul] using mul_pos hs (hR.dotProduct_mulVec_pos hx)

omit [DecidableEq ι] [Nonempty ι] in
theorem lower_frobenius_smul (R : Matrix ι ι ℝ) {s : ℝ} (hs : 0≤s) :
    frobenius (s • R)=s*frobenius R := by
  have hsum : (∑i,∑j,((s • R) i j)^2)=s^2*(∑i,∑j,R i j^2) := by
    simp only [Matrix.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
  unfold frobenius
  rw [hsum,Real.sqrt_mul (sq_nonneg s),Real.sqrt_sq hs]

theorem lower_spectralMaximum_smul {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {s : ℝ} (hs : 0<s) :
    spectralMaximum (s • R) (lower_posDef_smul hR hs).isHermitian=
      s*spectralMaximum R hR.isHermitian := by
  apply le_antisymm
  · apply (spectralMaximum_le_iff_euclidean_quadratic _ _).mpr
    intro x
    simpa only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,mul_assoc] using
      mul_le_mul_of_nonneg_left (euclidean_quadratic_le_spectralMaximum hR.isHermitian x) hs.le
  · obtain ⟨x,hx,hq⟩ := spectralMaximum_attained hR.isHermitian
    have hh := euclidean_quadratic_le_spectralMaximum (lower_posDef_smul hR hs).isHermitian x
    simpa only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,hq,hx,one_pow,mul_one] using hh

theorem lowerWeight_smul {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {s : ℝ} (hs : s≠0) : lowerWeight (s • R)=lowerWeight R := by
  have hp : (s • R)^2=s^2 • R^2 := by simp only [pow_two,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [lowerWeight,hp,Matrix.trace_smul,smul_eq_mul,smul_smul]
  have ht := (trace_square_pos hR).ne'
  have hfactor : (s^2*Matrix.trace (R^2))⁻¹*s^2=(Matrix.trace (R^2))⁻¹ := by
    field_simp
  rw [hfactor]
  rfl

theorem lowerComparison_smul {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {s : ℝ} (hs : 0<s) (A c : ℝ) :
    lowerComparison (s • R) A c=s • lowerComparison R A c := by
  rw [lowerComparison,lower_frobenius_smul R hs.le,lowerWeight_smul hR hs.ne']
  rw [show (A*(s*frobenius R)) • (1 : Matrix ι ι ℝ)-c • (s • R)=
      s • ((A*frobenius R) • (1 : Matrix ι ι ℝ)-c • R) by
    simp only [smul_sub,smul_smul]
    rw [show A*(s*frobenius R)=s*(A*frobenius R) by ring,
      show c*s=s*c by ring]]
  rw [Matrix.mul_smul,← smul_add]
  rfl

end
end SingularValueBounds.KL


/-! Preserve the parameters of the normalized comparison when restoring its
scale. The exact lower shift is then controlled by the proved deterministic
comparison at the original resolvent. -/
open MeasureTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
open LowerCertificates
noncomputable section
set_option maxHeartbeats 1600000
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem normalized_general_lower_parameters {X : Ω→ι→ℝ} {K : ℝ}
    (hdata : GeneralLowerCertificateConditions) (hsg : SubGaussianMGF μ X K)
    (hiso : CentredIsotropic μ X) (hK : 1≤K) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hF : frobenius R=1) :
    ∃ A c : ℝ,LowerComparisonProfile (spectralMaximum R hR.isHermitian) A c ∧
      (∫ω,quadraticForm (lowerWeight R) X ω*quadraticForm (lowerComparison R A c) X ω ∂μ)-
        K^2*Matrix.trace R≤generalLowerProfile (spectralMaximum R hR.isHermitian)*K^2*logParameter K := by
  let k := spectralMaximum R hR.isHermitian
  have hk1 : k≤1 := by simpa only [hF] using spectralMaximum_le_frobenius hR.posSemidef
  by_cases hk : k≤711/1000
  · refine ⟨k,1,?_,?_⟩
    · intro z hz hz1
      change min k (Real.sqrt (1-z^2))+(1-1)*z≤k
      simpa only [sub_self,zero_mul,add_zero] using min_le_left k (Real.sqrt (1-z^2))
    · simpa only [lowerComparison0,hF,div_one] using
        normalized_lower_mixed_nonplateau hsg hiso hK hR hF hdata.1 hk
  · have hk' : (711/1000:ℝ)≤k := (lt_of_not_ge hk).le
    rw [generalLowerProfile_plateau hk' hk1]
    by_cases hnear : k≤147/200
    · have hkr : k∈Icc (71/100:ℝ) (147/200) := ⟨by linarith,hnear⟩
      have hp := plateau_near_profile hkr
      refine ⟨plateauA k,17/10,hp,?_⟩
      apply normalized_plateau_mixed_cost hsg hiso hK hR hF
        (u:=1207/1000) (v:=plateauV (plateauA k)) (w:=26/25)
        (by norm_num) (by norm_num) hp
      · intro r hr
        exact plateau_near_scalar hdata.2.1 (plateauA_bounds hkr) ⟨hr.1,hr.2.trans hnear⟩
      · exact plateau_near_cost hdata.2.2 hkr
    · have hp := plateau_far_profile k
      refine ⟨74/55,19/10,hp,?_⟩
      apply normalized_plateau_mixed_cost hsg hiso hK hR hF
        (u:=6/5) (v:=27/16) (w:=21/20) (by norm_num) (by norm_num) hp
      · intro r hr
        exact plateau_far_scalar hdata.2.1 ⟨hr.1,hr.2.trans hk1⟩
      · exact plateau_far_cost hdata.2.2 ⟨le_of_not_ge hnear,hk1⟩

omit [MeasurableSpace Ω] [DecidableEq ι] [Nonempty ι] in
theorem lower_quadratic_smul (B : Matrix ι ι ℝ) (s : ℝ) (X : Ω→ι→ℝ) (ω : Ω) :
    quadraticForm (s • B) X ω=s*quadraticForm B X ω := by
  simp only [quadraticForm,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

theorem general_lower_mixed_cap_of_certificates {X : Ω→ι→ℝ} {K : ℝ}
    (hdata : GeneralLowerCertificateConditions) (hsg : SubGaussianMGF μ X K)
    (hiso : CentredIsotropic μ X) (hK : 1≤K) {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    ∃ B : Matrix ι ι ℝ,B.PosSemidef ∧
      (∀x:ι→ℝ,x ⬝ᵥ (lowerWeight R *ᵥ x)≤(1+x ⬝ᵥ (B *ᵥ x))*lowerShift R hR x) ∧
      (∫ω,quadraticForm (lowerWeight R) X ω*quadraticForm B X ω ∂μ)≤
        K^2*Matrix.trace R+K^2*logParameter K*frobenius R*generalLowerProfile (spectralRatio R hR) := by
  let eta := frobenius R
  have he : 0<eta := frobenius_pos hR
  let S := eta⁻¹ • R
  have hS : S.PosDef := lower_posDef_smul hR (inv_pos.mpr he)
  have hFS : frobenius S=1 := by
    rw [lower_frobenius_smul R (inv_nonneg.mpr he.le)]
    exact inv_mul_cancel₀ he.ne'
  have hMS : spectralMaximum S hS.isHermitian=spectralRatio R hR := by
    rw [lower_spectralMaximum_smul hR (inv_pos.mpr he)]
    simp only [spectralRatio,eta,div_eq_mul_inv,mul_comm]
  obtain ⟨A,c,hp,hcost⟩ := normalized_general_lower_parameters hdata hsg hiso hK hS hFS
  have hp' : LowerComparisonProfile (spectralRatio R hR) A c := hMS ▸ hp
  refine ⟨lowerComparison R A c,lowerComparison_posSemidef hR hp',
    (fun x=>lowerShift_quadratic_comparison hR x hp'),?_⟩
  have hP : lowerWeight S=lowerWeight R := lowerWeight_smul hR (inv_ne_zero he.ne')
  have hB : lowerComparison S A c=eta⁻¹ • lowerComparison R A c :=
    lowerComparison_smul hR (inv_pos.mpr he) A c
  have htr : Matrix.trace S=eta⁻¹*Matrix.trace R := Matrix.trace_smul _ _
  have hi : (∫ω,quadraticForm (lowerWeight S) X ω*quadraticForm (lowerComparison S A c) X ω ∂μ)=
      eta⁻¹*(∫ω,quadraticForm (lowerWeight R) X ω*quadraticForm (lowerComparison R A c) X ω ∂μ) := by
    simp_rw [hP,hB,lower_quadratic_smul]
    rw [←integral_const_mul]
    congr 1
    funext ω
    ring
  rw [hi,htr,hMS] at hcost
  have hh := mul_le_mul_of_nonneg_left hcost he.le
  have hid (z t : ℝ) : eta*(eta⁻¹*z-K^2*(eta⁻¹*t))=z-K^2*t := by
    field_simp
  rw [hid] at hh
  dsimp [eta] at hh
  nlinarith only [hh]

end
end SingularValueBounds.KL
