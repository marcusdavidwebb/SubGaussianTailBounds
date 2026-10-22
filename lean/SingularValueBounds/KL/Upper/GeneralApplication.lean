import SingularValueBounds.KL.Upper.GeneralMean
import SingularValueBounds.KL.Upper.GeneralMGF

/-! Complete general-K upper MGF, with the certified mean supplied internally. -/
open MeasureTheory
namespace SingularValueBounds.KL
open Certificates UpperSecond
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upperShift_general_mgf_of_certificates
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    (hrate : RateCertificateConditions) (hcells : GeneralMeanCellConditions)
    (hnum : GeneralMeanEntropyConditions)
    (hcert : EndpointLogratioCertificateConditions) (hsecond : GeneralSecondCertificateConditions)
    {X : Ω → ι → ℝ} {K : ℝ} (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X)
    (hK : 1≤K) {R : Matrix ι ι ℝ} (hR : R.PosDef) {b t : ℝ}
    (hcap : K^2*Matrix.trace R+(47/20)*K^2*logParameter K*frobenius R≤b) (hb : b<1)
    (ht : 0≤t) (hvt : ((9/2:ℝ)*K^2*logParameter K)*t<1) :
    Integrable (fun ω => Real.exp (t*((1-b)*upperShift R hR (X ω)))) μ ∧
      (∫ω,Real.exp (t*((1-b)*upperShift R hR (X ω))) ∂μ)≤
        Real.exp (t/(1-((9/2:ℝ)*K^2*logParameter K)*t)) := by
  have hMean := upperShift_general_mean_of_certificates hmajor hnorm hrate hcells hnum
    hiso hsg hK rfl hR hcap hb
  exact upperShift_general_mgf_of_mean hcert hsecond hsg hiso hK hR
    (by norm_num : (23/10:ℝ)≤47/20) hcap hb hMean.2 ht hvt

end
end SingularValueBounds.KL
