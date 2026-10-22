import SingularValueBounds.KL.Certificates.Final
import SingularValueBounds.KL.Upper.RowEstimates
import SingularValueBounds.KL.Lower.FinalTransfer
import SingularValueBounds.KL.Lower.MixedApplication

/-! Assembly of the current singular-value tails from the original row
assumptions and the explicitly finite rational certificate conditions. -/
open MeasureTheory ProbabilityTheory
namespace SingularValueBounds.KL
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upper_tail_general_of_final_certificates (hcert : FinalCertificateConditions)
    {m n : ℕ} [NeZero n] (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ)
    {K : ℝ} (hK : 1 ≤ K) (hindep : iIndepFun X μ)
    (hiso : ∀ i, CentredIsotropic μ (X i)) (hsg : ∀ i, SubGaussianMGF μ (X i) K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | UpperThreshold generalConstants m n K t ≤
      largestSingularValue (rowMatrix X ω)} ≤ Real.exp (-t^2/2) :=
  upper_tail_general_of_certificates hcert.majorant hcert.normDeterminant hcert.rate
    hcert.generalMeanCells hcert.generalMeanEntropy hcert.endpointLogratio
    hcert.generalSecond hnm X hK hindep hiso hsg ht

theorem upper_tail_one_of_final_certificates (hcert : FinalCertificateConditions)
    {m n : ℕ} [NeZero n] (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ)
    (hindep : iIndepFun X μ)
    (hiso : ∀ i, CentredIsotropic μ (X i)) (hsg : ∀ i, SubGaussianMGF μ (X i) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | UpperThreshold oneConstants m n 1 t ≤
      largestSingularValue (rowMatrix X ω)} ≤ Real.exp (-t^2/2) :=
  upper_tail_one_of_certificates hcert.endpointMean hcert.majorant hcert.normDeterminant
    hcert.endpointLogratio hnm X hindep hiso hsg ht

/-- Both non-strict tails with the general quartet
`(96/25, 79/50, 47/20, 3/2)`. Besides the explicitly finite certificate
conditions, these are precisely the original row assumptions. -/
theorem singular_value_tails_general_of_certificates (hcert : FinalCertificateConditions)
    {m n : ℕ} [NeZero n] (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ)
    {K : ℝ} (hK : 1 ≤ K) (hindep : iIndepFun X μ)
    (hiso : ∀ i, CentredIsotropic μ (X i)) (hsg : ∀ i, SubGaussianMGF μ (X i) K)
    {t : ℝ} (ht : 0 ≤ t) : TailBounds μ X generalConstants K t := by
  exact ⟨lower_tail_general_of_certificates hcert.generalLower hnm X hK hindep hiso hsg ht,
    upper_tail_general_of_final_certificates hcert hnm X hK hindep hiso hsg ht⟩

/-- Both non-strict endpoint tails with the improved quartet
`(33/25, 28/25, 58/25, sqrt 2)`. -/
theorem singular_value_tails_one_of_certificates (hcert : FinalCertificateConditions)
    {m n : ℕ} [NeZero n] (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ)
    (hindep : iIndepFun X μ)
    (hiso : ∀ i, CentredIsotropic μ (X i)) (hsg : ∀ i, SubGaussianMGF μ (X i) 1)
    {t : ℝ} (ht : 0 ≤ t) : TailBounds μ X oneConstants 1 t := by
  exact ⟨lower_tail_one_of_certificates hcert.endpointLowerTable hcert.endpointLowerFar
      hnm X hindep hiso hsg ht,
    upper_tail_one_of_final_certificates hcert hnm X hindep hiso hsg ht⟩

/-- Supplementary Theorem S1.1 with both exact numerical quartets. The
conditional premises are exclusively finite rational certificate checks. -/
theorem theorem_explicit_constants_of_certificates (hcert : FinalCertificateConditions) :
    TheoremKL μ generalConstants ∧ TheoremKLOne μ := by
  constructor
  · intro m n _ hnm X K hK hindep hiso hsg t ht
    exact singular_value_tails_general_of_certificates hcert hnm X hK hindep hiso hsg ht
  · intro m n _ hnm X hindep hiso hsg t ht
    exact singular_value_tails_one_of_certificates hcert hnm X hindep hiso hsg ht

end
end SingularValueBounds.KL
