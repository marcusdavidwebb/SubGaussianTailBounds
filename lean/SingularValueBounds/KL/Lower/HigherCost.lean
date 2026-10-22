import SingularValueBounds.KL.Lower.CellConsequences

/-! Actual-matrix higher-moment lower mixed cost, before and after selecting
the finite scalar cell. -/
open MeasureTheory
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1600000

theorem momentB_identity {k p : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hp : (19:ℝ)/4 ≤ p) :
    2*k^2 < momentB k p ∧ 1-2*k^2/momentB k p = 1/momentD k p := by
  have hk2 : k^2 ≤ 1 := by nlinarith
  have hd : 0 < p-2*k^2 := by linarith
  have hB := (LowerCertificates.momentB_pos_and_product hk.le hk1 hp).1
  have hD := momentD_gt_one hk hk1 hp
  constructor
  · dsimp [momentB]
    have hh := one_div_pos.mpr hd
    linarith
  · have hform : momentB k p = momentD k p/(p-2*k^2) := by
      dsimp [momentB,momentD]
      field_simp
      <;> ring
    rw [hform]
    field_simp [ne_of_gt (by linarith : 0 < momentD k p)]
    dsimp [momentD]
    <;> ring

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem normalized_lower_higher_mixed {X : Ω → ι → ℝ} {K p u C : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R = 1)
    {shape : ℝ} (hshape0 : 0 < shape) (hshape1 : shape ≤ 1)
    (hcap : spectralMaximum R hR.isHermitian ≤ shape)
    (hp : (19:ℝ)/4 ≤ p) (hu : 0 < u)
    (huk : u*spectralMaximum R hR.isHermitian < 1)
    (hM : spectralMaximum R hR.isHermitian^2 < lowerM (u*spectralMaximum R hR.isHermitian))
    (huC : u*(p-1)*C = 4*p)
    (hcondition : (p-1)*(lowerJ (u*spectralMaximum R hR.isHermitian)/(2*spectralMaximum R hR.isHermitian^2))+
      Real.log (Real.exp (momentLogM shape p)-1)+
      p*Real.log (p*momentB shape p)-
      Real.log (1-Real.exp (-(p-1/20))) ≤ 3*p) :
    (∫ ω,quadraticForm (lowerWeight R) X ω*quadraticForm (lowerComparison0 R hR) X ω ∂μ)-
      K^2*Matrix.trace R ≤ C*K^2*logParameter K := by
  let k := shape
  let B := momentB k p
  let M := Real.exp (momentLogM k p)
  let T := quadraticForm (lowerWeight R) X
  have hk : 0 < k := hshape0
  have hk1 : k ≤ 1 := hshape1
  have hK0 : 0 < K := by linarith
  have hB : 0 < B := (LowerCertificates.momentB_pos_and_product hk.le hk1 hp).1
  have hD := momentD_gt_one hk hk1 hp
  have hIdent := momentB_identity hk hk1 hp
  have hM1 : 1 < M := Real.one_lt_exp_iff.mpr (div_pos (Real.log_pos hD) (by positivity))
  have hExp := normalized_weight_exponential hsg hiso.measurable hK0 hR hF hk hcap hB hIdent.1
  have hExp' : Integrable (fun ω => Real.exp (T ω/(K^2*B))) μ ∧
      (∫ ω,Real.exp (T ω/(K^2*B)) ∂μ) ≤ M := by
    have he : -Real.log (1-2*k^2/B)/(2*k^2) = momentLogM k p := by
      change -Real.log (1-2*k^2/momentB k p)/(2*k^2) = _
      rw [hIdent.2]
      simp [momentLogM,Real.log_inv]
    simpa only [he] using hExp
  have hP : (lowerWeight R).PosSemidef := by
    have he : lowerWeight R = R^2 := by simp [lowerWeight,normalized_trace_square hR hF]
    rw [he,pow_two]
    simpa only [hR.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self R
  have htrace : Matrix.trace (lowerWeight R) = 1 := by simp [lowerWeight,normalized_trace_square hR hF]
  have hT := hsg.quadratic_memLp_two (lowerWeight R)
  have hTmean := (hiso.quadratic_mean (lowerWeight R)).trans htrace
  have hT0 := quadraticForm_nonneg hP X
  have hEnt := entropy_integrable_of_second_moment hT.aestronglyMeasurable.aemeasurable hT0 hT.integrable_sq
  have hEntropy := entropy_of_real_exponential (by have hmX := hiso.measurable; unfold quadraticForm dotProduct Matrix.mulVec; fun_prop) hT0
    (hT.integrable (by norm_num)) hTmean hEnt hp (by positivity : 0 < K^2*B) hM1 hExp'.1 hExp'.2
  have hlog : p*Real.log (K^2*B)+p*Real.log p-p =
      2*p*logParameter K-3*p+p*Real.log (p*B) := by
    rw [Real.log_mul (by positivity) hB.ne',Real.log_pow,
      Real.log_mul (by linarith : p ≠ 0) hB.ne']
    dsimp [logParameter]
    ring
  rw [hlog] at hEntropy
  apply normalized_lower_mixed_of_entropy_bound hsg hiso hK hR hF hu huk hM
  have hden : 0 < p-1 := by linarith
  have he := (le_div_iff₀ hden).1 hEntropy
  have hscale : (u/2)*C*logParameter K*(p-1) = 2*p*logParameter K := by
    nlinarith [congrArg (fun z : ℝ => z*logParameter K) huC]
  apply (mul_le_mul_right hden).1
  rw [add_mul,hscale]
  change _ ≤ _
  change _ ≤ _ at hcondition
  dsimp [T,M,B,k] at *
  nlinarith

theorem normalized_lower_mixed_on_cell {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R = 1)
    {a b p : ℚ} (h : LowerCertificates.MomentCellCertificate a b p)
    (hk : spectralMaximum R hR.isHermitian ∈ Set.Icc (a:ℝ) (b:ℝ)) :
    (∫ ω,quadraticForm (lowerWeight R) X ω*quadraticForm (lowerComparison0 R hR) X ω ∂μ)-
      K^2*Matrix.trace R ≤ generalLowerProfile (spectralMaximum R hR.isHermitian)*K^2*logParameter K := by
  have hs := h.shape_bounds hk
  have hp : (19:ℝ)/4 ≤ p := by
    have hh := (Rat.cast_le (K:=ℝ)).2 h.power
    norm_num at hh
    exact hh
  have hk0 : 0 < spectralMaximum R hR.isHermitian :=
    (hR.eigenvalues_pos (Classical.arbitrary ι)).trans_le (eigenvalue_le_spectralMaximum hR.isHermitian _)
  have hk1 : spectralMaximum R hR.isHermitian ≤ 1 := by simpa [hF] using spectralMaximum_le_frobenius hR.posSemidef
  apply normalized_lower_higher_mixed hsg hiso hK hR hF hk0 hk1 le_rfl hp
    (lowerMomentU_pos (by linarith : 1 < (p:ℝ))) hs.1 hs.2.1 _
    (h.entropy_condition hk).le
  unfold lowerMomentU
  have hh := (generalLowerProfile_bounds (spectralMaximum R hR.isHermitian)).1
  have hp1 : (p:ℝ)-1 ≠ 0 := by linarith
  have hprof : generalLowerProfile (spectralMaximum R hR.isHermitian) ≠ 0 := by linarith
  field_simp [hp1,hprof]
  <;> ring

end
end SingularValueBounds.KL
