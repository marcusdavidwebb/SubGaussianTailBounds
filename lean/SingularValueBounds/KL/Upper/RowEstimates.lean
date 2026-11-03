import SingularValueBounds.KL.Upper.GeneralApplication
import SingularValueBounds.KL.Upper.EndpointFullApplication
import SingularValueBounds.KL.Transfer

/-! The complete upper exponential moments discharge the one-row interfaces
used by the actual independent-row barrier process. -/
open MeasureTheory ProbabilityTheory
namespace SingularValueBounds.KL
open Certificates UpperSecond
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upper_row_estimate_general_of_certificates
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    (hrate : RateCertificateConditions) (hcells : GeneralMeanCellConditions)
    (hnum : GeneralMeanEntropyConditions)
    (hcert : EndpointLogratioCertificateConditions) (hsecond : GeneralSecondCertificateConditions)
    {X : Ω → ι → ℝ} {K : ℝ} (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X)
    (hK : 1 ≤ K) :
    UpperRowEstimate μ X K ((47/20)*K^2*logParameter K) ((9/2)*K^2*logParameter K) := by
  intro R hR b hcap hb ℓ hℓ hℓν
  have hν : 0 < (9/2:ℝ)*K^2*logParameter K := by
    have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
    have hL : 0 < logParameter K := lt_of_lt_of_le zero_lt_one (one_le_logParameter hK)
    positivity
  have hνℓ : ((9/2:ℝ)*K^2*logParameter K)*ℓ < 1 := by
    have h := (lt_div_iff₀ hν).mp hℓν
    simpa only [mul_comm] using h
  have h := upperShift_general_mgf_of_certificates hmajor hnorm hrate hcells hnum
    hcert hsecond hsg hiso hK hR hcap hb hℓ.le hνℓ
  simpa only [mul_assoc] using h

theorem upper_row_estimate_one_of_certificates
    (hmean : EndpointMeanCertificateConditions)
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    (hcert : EndpointLogratioCertificateConditions)
    {X : Ω → ι → ℝ} (hiso : CentredIsotropic μ X) (hsg : SubGaussianMGF μ X 1) :
    UpperRowEstimate μ X 1 (58/25) 4 := by
  intro R hR b hcap hb ℓ hℓ hℓ4
  have hcap' : Matrix.trace R+(58/25:ℝ)*frobenius R ≤ b := by
    simpa only [regularityCost, one_pow, one_mul] using hcap
  have h4ℓ : 4*ℓ < 1 := by linarith
  have h := upperShift_endpoint_mgf_of_certificates hmean hmajor hnorm hcert
    hiso hsg hR hcap' hb hℓ.le h4ℓ
  simpa only [mul_assoc] using h

end

section Tails
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m n : ℕ} [NeZero n]

/-- The exact general upper quartet, from the original row assumptions and
the explicitly finite upper certificate families. -/
theorem upper_tail_general_of_certificates
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    (hrate : RateCertificateConditions) (hcells : GeneralMeanCellConditions)
    (hnum : GeneralMeanEntropyConditions)
    (hcert : EndpointLogratioCertificateConditions) (hsecond : GeneralSecondCertificateConditions)
    (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ) {K : ℝ} (hK : 1 ≤ K)
    (hindep : iIndepFun X μ) (hiso : ∀ i, CentredIsotropic μ (X i))
    (hsg : ∀ i, SubGaussianMGF μ (X i) K) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | UpperThreshold generalConstants m n K t ≤
      largestSingularValue (rowMatrix X ω)} ≤ Real.exp (-t^2/2) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL : 0 < logParameter K := lt_of_lt_of_le zero_lt_one (one_le_logParameter hK)
  have hw : 0 < (47/20:ℝ)*K^2*logParameter K := by positivity
  have hν : 0 < (9/2:ℝ)*K^2*logParameter K := by positivity
  have hwK : ((47/20:ℝ)*K^2*logParameter K)/K = (47/20:ℝ)*K*logParameter K := by
    field_simp
  have hsqrt : Real.sqrt (((9/2:ℝ)*K^2*logParameter K)/2) =
      (3/2:ℝ)*K*Real.sqrt (logParameter K) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    rw [mul_pow, mul_pow, Real.sq_sqrt hL.le]
    ring
  have h := upper_tail_from_row_estimates X (fun i => (hiso i).measurable) hindep
    ((NeZero.pos n).trans_le hnm) hK0 hw hν
    (fun i => upper_row_estimate_general_of_certificates hmajor hnorm hrate hcells hnum
      hcert hsecond (hsg i) (hiso i) hK) ht
  have hgamma : SubGaussian.Constants.generalGamma = (47/20:ℝ) := by
    norm_num [SubGaussian.Constants.generalGamma]
  have hdelta : SubGaussian.Constants.generalDelta = (3/2:ℝ) := by
    norm_num [SubGaussian.Constants.generalDelta]
  simpa only [hwK, hsqrt, UpperThreshold, generalConstants, hgamma, hdelta] using h

/-- The exact endpoint upper quartet. -/
theorem upper_tail_one_of_certificates
    (hmean : EndpointMeanCertificateConditions)
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    (hcert : EndpointLogratioCertificateConditions)
    (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ)
    (hindep : iIndepFun X μ) (hiso : ∀ i, CentredIsotropic μ (X i))
    (hsg : ∀ i, SubGaussianMGF μ (X i) 1) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | UpperThreshold oneConstants m n 1 t ≤
      largestSingularValue (rowMatrix X ω)} ≤ Real.exp (-t^2/2) := by
  have h := upper_tail_from_row_estimates X (fun i => (hiso i).measurable) hindep
    ((NeZero.pos n).trans_le hnm) (K := 1) (w := 58/25) (ν := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (fun i => upper_row_estimate_one_of_certificates hmean hmajor hnorm hcert (hiso i) (hsg i)) ht
  have hdelta : Real.sqrt 2 ≤ (71/50 : ℝ) := by
    norm_num [Real.sqrt_le_iff]
  apply le_trans (measureReal_mono ?_) h
  intro ω hω
  change UpperThreshold oneConstants m n 1 t ≤ largestSingularValue (rowMatrix X ω) at hω
  change Real.sqrt m+1*Real.sqrt n+(58/25:ℝ)/1+Real.sqrt ((4:ℝ)/2)*t ≤
    largestSingularValue (rowMatrix X ω)
  have hdt := mul_le_mul_of_nonneg_right hdelta ht
  simp only [UpperThreshold, oneConstants, logParameter, Real.log_one, add_zero,
    Real.sqrt_one, mul_one, one_mul] at hω
  norm_num only [SubGaussian.Constants.unitGamma, SubGaussian.Constants.unitDelta] at hω
  simp only [one_mul, div_one, show (4:ℝ)/2=2 by norm_num]
  linarith

end Tails
end SingularValueBounds.KL
