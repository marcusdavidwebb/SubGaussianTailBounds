import SingularValueBounds.KL.Certificates.ConcretePlateauCost0
import SingularValueBounds.KL.Certificates.ConcretePlateauCost1

/-! Both complete plateau-cost interval certificate families. -/
namespace SingularValueBounds.KL.LowerCertificates

theorem plateauCostCertificateConditions : PlateauCostCertificateConditions := by
  intro i
  fin_cases i
  · exact plateauCost_range_0
  · exact plateauCost_range_1

end SingularValueBounds.KL.LowerCertificates
