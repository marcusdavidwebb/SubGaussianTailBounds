import SingularValueBounds.KL.Lower.GeneralProfile
import SingularValueBounds.KL.Certificates.ConcreteMomentCells
import SingularValueBounds.KL.Certificates.ConcretePlateauScalars
import SingularValueBounds.KL.Certificates.ConcretePlateauCost

/-! Complete concrete lower-profile certificates, with no external premises. -/
namespace SingularValueBounds.KL

theorem generalLowerCertificateConditions : GeneralLowerCertificateConditions :=
  ⟨LowerCertificates.momentCellConditions, LowerCertificates.plateauCertificateConditions,
    LowerCertificates.plateauCostCertificateConditions⟩

end SingularValueBounds.KL
