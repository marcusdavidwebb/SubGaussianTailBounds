import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanGeometry
import SingularValueBounds.KL.Certificates.ConcreteEndpointAnalytic
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials

/-! Complete endpoint mean certificates: exact analytic interval sums and
polynomial signs. All numerical fields are discharged by kernel-checked proofs. -/
namespace SingularValueBounds.KL.Certificates

theorem endpointMeanCertificateConditions : EndpointMeanCertificateConditions := {
  aGrid := endpointMean_aGrid
  quarterNondegenerate := endpointMean_quarterNondegenerate
  smallCutoff := endpointMean_smallCutoff
  smallNumerical := endpointSmall_analytic
  smallTotal := endpointMean_smallTotal
  jointCutoff := endpointMean_jointCutoff
  jointBoxes := fun ki ai _ => endpointMean_jointBoxes ki ai
  jointNumerical := endpointMean_analytic
  chosenDomain := endpointMean_chosenDomain
  polynomialTests := endpointMean_polynomialTests
}

end SingularValueBounds.KL.Certificates
