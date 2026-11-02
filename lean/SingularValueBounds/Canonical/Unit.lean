import SingularValueBounds.Canonical.Adapter
import SingularValueBounds.KL.Lower.MixedApplication
import SingularValueBounds.KL.Upper.RowEstimates
import SingularValueBounds.KL.Certificates.ConcreteEndpointMean
import SingularValueBounds.KL.Certificates.ConcreteEndpointTable
import SingularValueBounds.KL.Certificates.ConcreteEndpointFar
import SingularValueBounds.KL.Certificates.ConcreteMajorants
import SingularValueBounds.KL.Certificates.ConcreteNormDeterminants
import SingularValueBounds.KL.Certificates.ConcreteEndpointLogratio

/-! The unit baseline with all finite instances supplied by kernel-checked proofs. -/
open MeasureTheory ProbabilityTheory
namespace SingularValueBounds.Canonical
universe u

theorem unit_baseline :
    SubGaussian.UnitSingularValueTailBound.{u} 1.32 1.12 2.32 1.42 := by
  apply unit_of_tailBounds
  intro Ω _ μ _ m n _ hnm X hindep hiso hsg t ht
  exact ⟨KL.lower_tail_one_of_certificates KL.Certificates.endpointTableConditions
      KL.Certificates.endpointFarConditions hnm X hindep hiso hsg ht,
    KL.upper_tail_one_of_certificates KL.Certificates.endpointMeanCertificateConditions
      KL.Certificates.majorantCertificateConditions KL.normDeterminantCertificateConditions
      KL.endpointLogratioCertificateConditions hnm X hindep hiso hsg ht⟩

end SingularValueBounds.Canonical
