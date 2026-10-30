import SingularValueBounds.KL.Certificates.ConcreteRates.Row00
import SingularValueBounds.KL.Certificates.ConcreteRates.Row01
import SingularValueBounds.KL.Certificates.ConcreteRates.Row02
import SingularValueBounds.KL.Certificates.ConcreteRates.Row03
import SingularValueBounds.KL.Certificates.ConcreteRates.Row04
import SingularValueBounds.KL.Certificates.ConcreteRates.Row05
import SingularValueBounds.KL.Certificates.ConcreteRates.Row06
import SingularValueBounds.KL.Certificates.ConcreteRates.Row07
import SingularValueBounds.KL.Certificates.ConcreteRates.Row08
import SingularValueBounds.KL.Certificates.ConcreteRates.Row09
import SingularValueBounds.KL.Certificates.ConcreteRates.Row10
import SingularValueBounds.KL.Certificates.ConcreteRates.Row11
import SingularValueBounds.KL.Certificates.ConcreteRates.Row12
import SingularValueBounds.KL.Certificates.ConcreteRates.Row13
import SingularValueBounds.KL.Certificates.ConcreteRates.Row14

/-! Concrete kernel proofs of all fifteen upper-rate polynomial certificates.
The finite tree memberships, polynomial identities, and every Bernstein sign
are checked in Lean; no external certificate hypothesis remains in this field. -/
namespace SingularValueBounds.KL.Certificates

/-- All leaves of the fifteen prescribed upper-rate subdivisions are certified. -/
theorem rateCertificateConditions : RateCertificateConditions := by
  intro i
  fin_cases i
  · exact concrete_rate_row_0
  · exact concrete_rate_row_1
  · exact concrete_rate_row_2
  · exact concrete_rate_row_3
  · exact concrete_rate_row_4
  · exact concrete_rate_row_5
  · exact concrete_rate_row_6
  · exact concrete_rate_row_7
  · exact concrete_rate_row_8
  · exact concrete_rate_row_9
  · exact concrete_rate_row_10
  · exact concrete_rate_row_11
  · exact concrete_rate_row_12
  · exact concrete_rate_row_13
  · exact concrete_rate_row_14

end SingularValueBounds.KL.Certificates
