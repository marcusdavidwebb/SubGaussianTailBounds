import SingularValueBounds.KL.Upper.EndpointMean
import SingularValueBounds.KL.Upper.EndpointApplication

/-! # Complete endpoint upper mean and exponential moment

Supplementary Lemmas S1.9 and S1.12, bundled with only the explicitly finite
rational certificate conditions as numerical premises.
-/
open MeasureTheory
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upperShift_endpoint_mgf_of_certificates
    (hMeanCert : EndpointMeanCertificateConditions)
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    (hRareCert : EndpointLogratioCertificateConditions)
    {X : Ω → ι → ℝ} (hiso : CentredIsotropic μ X) (hsg : SubGaussianMGF μ X 1)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) {b t : ℝ}
    (hcap : Matrix.trace R+(58/25 : ℝ)*frobenius R≤b) (hb : b<1)
    (ht : 0≤t) (ht4 : 4*t<1) :
    Integrable (fun ω => Real.exp (t*((1-b)*upperShift R hR (X ω)))) μ ∧
      (∫ω,Real.exp (t*((1-b)*upperShift R hR (X ω))) ∂μ)≤Real.exp (t/(1-4*t)) := by
  exact upperShift_endpoint_mgf_of_mean hRareCert hiso hsg hR
    (w := (58/25 : ℝ)) (by norm_num) hcap hb
    (upperShift_endpoint_mean hMeanCert hmajor hnorm hiso hsg hR hcap hb).2 ht ht4

end
end SingularValueBounds.KL
