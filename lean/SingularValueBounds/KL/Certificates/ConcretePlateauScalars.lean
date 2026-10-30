import SingularValueBounds.KL.Certificates.ConcretePlateauScalars.Row0
import SingularValueBounds.KL.Certificates.ConcretePlateauScalars.Row1
import SingularValueBounds.KL.Certificates.ConcretePlateauScalars.Row2

/-! Complete internal certificates for all three plateau determinant families. -/
namespace SingularValueBounds.KL.LowerCertificates

theorem plateauCertificateConditions : PlateauCertificateConditions :=
  ⟨ScalarRow0.plateauScalarRow0, ScalarRow1.plateauScalarRow1, ScalarRow2.plateauScalarRow2⟩

end SingularValueBounds.KL.LowerCertificates
