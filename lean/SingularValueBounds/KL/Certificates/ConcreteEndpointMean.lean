import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPrefactors
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanEntropy
import SingularValueBounds.KL.Certificates.ConcreteEndpointSmallEntropy
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials

/-!
Concrete endpoint upper-mean conditions. The reusable assembly separates its
finite families; the closed instance below supplies every field with Lean proofs.
-/
namespace SingularValueBounds.KL.Certificates

theorem endpointMeanCertificateConditions_of_finite_bounds
    (hsmall : ∀ i : Fin 50, entropyGridBoundQ (endpointSmallCutoff i)
      (endpointSmallBound i) (endpointDecayQ 90 8000) ≤ endpointSmallTarget i)
    (hcorners : ∀ ki : Fin 60, ∀ ai : Fin 42, endpointMeanActive ki ai →
      ∀ h : Fin 4, endpointMeanNumericCorner ki ai h ≤ endpointMeanCorner ki ai h)
    (hpolynomials : ∀ ki : Fin 60, ∀ ai : Fin 42, endpointMeanActive ki ai →
      ∃ n m, BoxCertificate (endpointMeanTestQ ki ai) n m (endpointMeanBox ki ai)) :
    EndpointMeanCertificateConditions := {
  gridLogs := endpointMean_gridLogs
  decays := fun qi _ => endpointDecayConditions qi
  aGrid := endpointMean_aGrid
  quarterNondegenerate := endpointMean_quarterNondegenerate
  smallCutoff := endpointMean_smallCutoff
  smallPrefactors := endpointMean_smallPrefactors
  smallRounding := fun i j _ h => endpointMean_smallRounding i j h
  smallNumerical := hsmall
  smallTotal := endpointMean_smallTotal
  jointCutoff := endpointMean_jointCutoff
  jointBoxes := fun ki ai _ => endpointMean_jointBoxes ki ai
  jointRates := endpointMean_jointRates
  jointPrefactors := endpointMean_jointPrefactors
  jointCorners := hcorners
  chosenDomain := endpointMean_chosenDomain
  polynomialTests := hpolynomials
}

theorem endpointMeanCertificateConditions : EndpointMeanCertificateConditions :=
  endpointMeanCertificateConditions_of_finite_bounds endpointMean_smallNumerical
    endpointMean_jointCorners endpointMean_polynomialTests

end SingularValueBounds.KL.Certificates
