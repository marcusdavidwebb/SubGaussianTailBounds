import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row00
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row01
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row02
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row03
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row04
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row05
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row06
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row07
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row08
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row09
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row10
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row11
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row12
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row13
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row14
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row15
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row16
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row17
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row18
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row19
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row20
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row21
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row22
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row23
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row24
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row25
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row26
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row27
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row28
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row29
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row30
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row31
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row32
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row33
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row34
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row35
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row36
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row37
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row38
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row39
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row40
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row41
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row42
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row43
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row44
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row45
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row46
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row47
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row48
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row49
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row50
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row51
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row52
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row53
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row54
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row55
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row56
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row57
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row58
import SingularValueBounds.KL.Certificates.ConcreteEndpointMeanPolynomials.Row59

/-! Kernel-checked polynomial certificates for all 837 active endpoint rectangles.
The finite case split also proves that every omitted rectangle is inactive. -/
namespace SingularValueBounds.KL.Certificates

theorem endpointMean_polynomialTests (ki : Fin 60) (ai : Fin 42) :
    endpointMeanActive ki ai →
      BoxCertificate (endpointMeanTestQ ki ai) 8 16 (endpointMeanBox ki ai) := by
  fin_cases ki
  · exact endpointMeanPolynomial_row00 ai
  · exact endpointMeanPolynomial_row01 ai
  · exact endpointMeanPolynomial_row02 ai
  · exact endpointMeanPolynomial_row03 ai
  · exact endpointMeanPolynomial_row04 ai
  · exact endpointMeanPolynomial_row05 ai
  · exact endpointMeanPolynomial_row06 ai
  · exact endpointMeanPolynomial_row07 ai
  · exact endpointMeanPolynomial_row08 ai
  · exact endpointMeanPolynomial_row09 ai
  · exact endpointMeanPolynomial_row10 ai
  · exact endpointMeanPolynomial_row11 ai
  · exact endpointMeanPolynomial_row12 ai
  · exact endpointMeanPolynomial_row13 ai
  · exact endpointMeanPolynomial_row14 ai
  · exact endpointMeanPolynomial_row15 ai
  · exact endpointMeanPolynomial_row16 ai
  · exact endpointMeanPolynomial_row17 ai
  · exact endpointMeanPolynomial_row18 ai
  · exact endpointMeanPolynomial_row19 ai
  · exact endpointMeanPolynomial_row20 ai
  · exact endpointMeanPolynomial_row21 ai
  · exact endpointMeanPolynomial_row22 ai
  · exact endpointMeanPolynomial_row23 ai
  · exact endpointMeanPolynomial_row24 ai
  · exact endpointMeanPolynomial_row25 ai
  · exact endpointMeanPolynomial_row26 ai
  · exact endpointMeanPolynomial_row27 ai
  · exact endpointMeanPolynomial_row28 ai
  · exact endpointMeanPolynomial_row29 ai
  · exact endpointMeanPolynomial_row30 ai
  · exact endpointMeanPolynomial_row31 ai
  · exact endpointMeanPolynomial_row32 ai
  · exact endpointMeanPolynomial_row33 ai
  · exact endpointMeanPolynomial_row34 ai
  · exact endpointMeanPolynomial_row35 ai
  · exact endpointMeanPolynomial_row36 ai
  · exact endpointMeanPolynomial_row37 ai
  · exact endpointMeanPolynomial_row38 ai
  · exact endpointMeanPolynomial_row39 ai
  · exact endpointMeanPolynomial_row40 ai
  · exact endpointMeanPolynomial_row41 ai
  · exact endpointMeanPolynomial_row42 ai
  · exact endpointMeanPolynomial_row43 ai
  · exact endpointMeanPolynomial_row44 ai
  · exact endpointMeanPolynomial_row45 ai
  · exact endpointMeanPolynomial_row46 ai
  · exact endpointMeanPolynomial_row47 ai
  · exact endpointMeanPolynomial_row48 ai
  · exact endpointMeanPolynomial_row49 ai
  · exact endpointMeanPolynomial_row50 ai
  · exact endpointMeanPolynomial_row51 ai
  · exact endpointMeanPolynomial_row52 ai
  · exact endpointMeanPolynomial_row53 ai
  · exact endpointMeanPolynomial_row54 ai
  · exact endpointMeanPolynomial_row55 ai
  · exact endpointMeanPolynomial_row56 ai
  · exact endpointMeanPolynomial_row57 ai
  · exact endpointMeanPolynomial_row58 ai
  · exact endpointMeanPolynomial_row59 ai

end SingularValueBounds.KL.Certificates
