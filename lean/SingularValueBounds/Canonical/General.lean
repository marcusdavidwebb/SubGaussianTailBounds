import SingularValueBounds.Canonical.Adapter
import SingularValueBounds.KL.Lower.MixedApplication
import SingularValueBounds.KL.Upper.RowEstimates
import SingularValueBounds.KL.Certificates.ConcreteGeneralLower
import SingularValueBounds.KL.Certificates.ConcreteMajorants
import SingularValueBounds.KL.Certificates.ConcreteNormDeterminants
import SingularValueBounds.KL.Certificates.ConcreteRates
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanCells
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropy
import SingularValueBounds.KL.Certificates.ConcreteEndpointLogratio
import SingularValueBounds.KL.Certificates.ConcreteGeneralSecond

/-! The general baseline, assembled independently of the unit-regime mean bound. -/

open MeasureTheory ProbabilityTheory

namespace SingularValueBounds.Canonical
universe u

theorem general_baseline :
    SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5 := by
  apply general_of_tailBounds
  intro Ω _ μ _ m n _ hnm X K hK hindep hiso hsg t ht
  exact ⟨KL.lower_tail_general_of_certificates KL.generalLowerCertificateConditions
      hnm X hK hindep hiso hsg ht,
    KL.upper_tail_general_of_certificates KL.Certificates.majorantCertificateConditions
      KL.normDeterminantCertificateConditions KL.Certificates.rateCertificateConditions
      KL.Certificates.generalMeanCellConditions KL.Certificates.generalMeanEntropyConditions
      KL.endpointLogratioCertificateConditions
      KL.UpperSecond.generalSecondCertificateConditions hnm X hK hindep hiso hsg ht⟩

end SingularValueBounds.Canonical
