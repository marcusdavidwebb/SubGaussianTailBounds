import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block00
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block01
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block02
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block03
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block04
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block05
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block06
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block07
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block08
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Block09

/-! Kernel-checked polynomial certificates for all 837 active endpoint rectangles.
The finite case split also proves that every omitted rectangle is inactive. -/
namespace SingularValueBounds.KL.Certificates

theorem endpointMean_polynomialTests (ki : Fin 60) (ai : Fin 42) :
    endpointMeanActive ki ai →
      ∃ n m, BoxCertificate (endpointMeanTestQ ki ai) n m (endpointMeanBox ki ai) := by
  revert ki ai
  exact Fin.cases (motive := fun ki => ∀ ai : Fin 42, endpointMeanActive ki ai →
      ∃ n m, BoxCertificate (endpointMeanTestQ ki ai) n m (endpointMeanBox ki ai))
    endpointMeanPolynomial_row00 <|
    Fin.cases endpointMeanPolynomial_row01 <|
    Fin.cases endpointMeanPolynomial_row02 <|
    Fin.cases endpointMeanPolynomial_row03 <|
    Fin.cases endpointMeanPolynomial_row04 <|
    Fin.cases endpointMeanPolynomial_row05 <|
    Fin.cases endpointMeanPolynomial_row06 <|
    Fin.cases endpointMeanPolynomial_row07 <|
    Fin.cases endpointMeanPolynomial_row08 <|
    Fin.cases endpointMeanPolynomial_row09 <|
    Fin.cases endpointMeanPolynomial_row10 <|
    Fin.cases endpointMeanPolynomial_row11 <|
    Fin.cases endpointMeanPolynomial_row12 <|
    Fin.cases endpointMeanPolynomial_row13 <|
    Fin.cases endpointMeanPolynomial_row14 <|
    Fin.cases endpointMeanPolynomial_row15 <|
    Fin.cases endpointMeanPolynomial_row16 <|
    Fin.cases endpointMeanPolynomial_row17 <|
    Fin.cases endpointMeanPolynomial_row18 <|
    Fin.cases endpointMeanPolynomial_row19 <|
    Fin.cases endpointMeanPolynomial_row20 <|
    Fin.cases endpointMeanPolynomial_row21 <|
    Fin.cases endpointMeanPolynomial_row22 <|
    Fin.cases endpointMeanPolynomial_row23 <|
    Fin.cases endpointMeanPolynomial_row24 <|
    Fin.cases endpointMeanPolynomial_row25 <|
    Fin.cases endpointMeanPolynomial_row26 <|
    Fin.cases endpointMeanPolynomial_row27 <|
    Fin.cases endpointMeanPolynomial_row28 <|
    Fin.cases endpointMeanPolynomial_row29 <|
    Fin.cases endpointMeanPolynomial_row30 <|
    Fin.cases endpointMeanPolynomial_row31 <|
    Fin.cases endpointMeanPolynomial_row32 <|
    Fin.cases endpointMeanPolynomial_row33 <|
    Fin.cases endpointMeanPolynomial_row34 <|
    Fin.cases endpointMeanPolynomial_row35 <|
    Fin.cases endpointMeanPolynomial_row36 <|
    Fin.cases endpointMeanPolynomial_row37 <|
    Fin.cases endpointMeanPolynomial_row38 <|
    Fin.cases endpointMeanPolynomial_row39 <|
    Fin.cases endpointMeanPolynomial_row40 <|
    Fin.cases endpointMeanPolynomial_row41 <|
    Fin.cases endpointMeanPolynomial_row42 <|
    Fin.cases endpointMeanPolynomial_row43 <|
    Fin.cases endpointMeanPolynomial_row44 <|
    Fin.cases endpointMeanPolynomial_row45 <|
    Fin.cases endpointMeanPolynomial_row46 <|
    Fin.cases endpointMeanPolynomial_row47 <|
    Fin.cases endpointMeanPolynomial_row48 <|
    Fin.cases endpointMeanPolynomial_row49 <|
    Fin.cases endpointMeanPolynomial_row50 <|
    Fin.cases endpointMeanPolynomial_row51 <|
    Fin.cases endpointMeanPolynomial_row52 <|
    Fin.cases endpointMeanPolynomial_row53 <|
    Fin.cases endpointMeanPolynomial_row54 <|
    Fin.cases endpointMeanPolynomial_row55 <|
    Fin.cases endpointMeanPolynomial_row56 <|
    Fin.cases endpointMeanPolynomial_row57 <|
    Fin.cases endpointMeanPolynomial_row58 <|
    Fin.cases endpointMeanPolynomial_row59 <|
    fun ki => Fin.elim0 ki

end SingularValueBounds.KL.Certificates
