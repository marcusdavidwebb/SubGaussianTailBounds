import SingularValueBounds.KL.Lower.NormMoment
import SingularValueBounds.KL.Lower.Moments

/-! Higher real moments and the normalized actual-matrix mixed-cost deduction. -/
open MeasureTheory
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem entropy_of_real_exponential {T : Ω → ℝ} {p scale M : ℝ}
    (hm : Measurable T) (hT0 : ∀ ω,0 ≤ T ω) (hT : Integrable T μ)
    (hMean : (∫ ω,T ω ∂μ) = 1)
    (hEnt : Integrable (fun ω => T ω*Real.log (T ω)) μ)
    (hp : (19:ℝ)/4 ≤ p) (hs : 0 < scale) (hM1 : 1 < M)
    (hExp : Integrable (fun ω => Real.exp (T ω/scale)) μ)
    (hM : (∫ ω,Real.exp (T ω/scale) ∂μ) ≤ M) :
    (∫ ω,T ω*Real.log (T ω) ∂μ) ≤
      (p*Real.log scale+p*Real.log p-p+Real.log (M-1)-
        Real.log (1-Real.exp (-(p-1/20))))/(p-1) := by
  obtain ⟨hMoment,hbound⟩ := real_moment_of_exponential hm hT0 hp hs hExp hM
  have hpos := positive_real_moment_of_mean_one hT0 hMean hMoment (by linarith)
  have hren := renyi_entropy_bound hT0 hT hMean hEnt hMoment hpos (by linarith)
  have hd : 0 < 1-Real.exp (-(p-1/20)) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -(p-1/20) < 0)
    linarith
  have hp0 : 0 < p := by linarith
  have hMpos : 0 < M-1 := by linarith
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_div (by positivity) hd.ne',
    Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_rpow hs,
    Real.log_rpow hp0,Real.log_exp] at hlog
  apply hren.trans
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem normalized_lower_mixed_of_entropy_bound {X : Ω → ι → ℝ} {K C : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R = 1)
    {u : ℝ} (hu : 0 < u) (huk : u*spectralMaximum R hR.isHermitian < 1)
    (hM : spectralMaximum R hR.isHermitian^2 < lowerM (u*spectralMaximum R hR.isHermitian))
    (hEntropy : (∫ ω,quadraticForm (lowerWeight R) X ω*
      Real.log (quadraticForm (lowerWeight R) X ω) ∂μ)+
      lowerJ (u*spectralMaximum R hR.isHermitian)/(2*spectralMaximum R hR.isHermitian^2) ≤
        (u/2)*C*logParameter K) :
    (∫ ω,quadraticForm (lowerWeight R) X ω*quadraticForm (lowerComparison0 R hR) X ω ∂μ)-
      K^2*Matrix.trace R ≤ C*K^2*logParameter K := by
  let P := lowerWeight R
  let B := lowerComparison0 R hR
  let lam := u/(2*K^2)
  have hK0 : 0 < K := by linarith
  have hP : P.PosSemidef := by
    have hp : P = R^2 := by simp [P,lowerWeight,normalized_trace_square hR hF]
    rw [hp,pow_two]
    simpa only [hR.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self R
  have htr : Matrix.trace P = 1 := by simp [P,lowerWeight,normalized_trace_square hR hF]
  have hT := hsg.quadratic_memLp_two P
  have hQ := hsg.quadratic_memLp_two B
  have hMean := (hiso.quadratic_mean P).trans htr
  have hEnt := entropy_integrable_of_second_moment hT.aestronglyMeasurable.aemeasurable
    (quadraticForm_nonneg hP X) hT.integrable_sq
  have hWZ : Integrable (fun ω => quadraticForm P X ω*
      (lam*(quadraticForm B X ω-K^2*Matrix.trace R))) μ := by
    have hi := ((hT.integrable_mul hQ).sub ((hT.integrable (by norm_num)).mul_const (K^2*Matrix.trace R))).const_mul lam
    convert! hi using 1
    ext ω
    simp only [Pi.sub_apply,Pi.mul_apply]
    ring
  have hExp := normalized_lower_log_mgf hsg hiso.measurable hK0 hR hF hu huk hM
  have h := weighted_entropy (Filter.Eventually.of_forall (quadraticForm_nonneg hP X))
    (hT.integrable (by norm_num)) hMean hEnt hWZ hExp.1
  have hi : (∫ ω,quadraticForm P X ω*(lam*(quadraticForm B X ω-K^2*Matrix.trace R)) ∂μ) =
      lam*((∫ ω,quadraticForm P X ω*quadraticForm B X ω ∂μ)-K^2*Matrix.trace R) := by
    have hp (ω : Ω) : quadraticForm P X ω*(lam*(quadraticForm B X ω-K^2*Matrix.trace R)) =
        lam*(quadraticForm P X ω*quadraticForm B X ω-quadraticForm P X ω*(K^2*Matrix.trace R)) := by ring
    simp_rw [hp]
    rw [integral_const_mul,integral_sub (f:=fun ω=>quadraticForm P X ω*quadraticForm B X ω) (hT.integrable_mul hQ)
      ((hT.integrable (by norm_num)).mul_const _),integral_mul_const,hMean,one_mul]
  rw [hi] at h
  have hh := h.trans (add_le_add_right hExp.2 _)
  have hh' := hh.trans hEntropy
  dsimp [lam] at hh'
  have hpos : 0 < u/(2*K^2) := by positivity
  have hid : (u/(2*K^2))*(C*K^2*logParameter K) = (u/2)*C*logParameter K := by field_simp
  rw [← hid] at hh'
  exact (mul_le_mul_iff_right₀ hpos).1 hh'

end
end SingularValueBounds.KL
