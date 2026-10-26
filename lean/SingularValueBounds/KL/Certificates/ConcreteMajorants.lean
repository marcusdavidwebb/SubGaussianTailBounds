import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row0
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row1
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row2
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row3
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row4
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5

/-! Concrete proofs for all six upper determinant majorants and 165 boxes. -/
namespace SingularValueBounds.KL.Certificates

theorem majorantCertificateConditions : MajorantCertificateConditions := by
  intro i
  refine ⟨majorant_cleared_factorization i, ?_⟩
  fin_cases i
  · exact concrete_majorant_row_0
  · exact concrete_majorant_row_1
  · exact concrete_majorant_row_2
  · exact concrete_majorant_row_3
  · exact concrete_majorant_row_4
  · exact concrete_majorant_row_5

end SingularValueBounds.KL.Certificates
