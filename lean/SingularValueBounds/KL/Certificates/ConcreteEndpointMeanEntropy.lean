import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row00
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row01
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row02
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row03
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row04
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row05
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row06
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row07
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row08
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row09
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row10
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row11
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row12
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row13
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row14
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row15
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row16
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row17
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row18
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row19
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row20
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row21
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row22
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row23
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row24
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row25
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row26
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row27
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row28
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row29
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row30
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row31
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row32
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row33
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row34
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row35
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row36
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row37
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row38
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row39
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row40
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row41
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row42
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row43
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row44
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row45
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row46
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row47
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row48
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row49
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row50
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row51
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row52
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row53
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row54
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row55
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row56
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row57
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row58
import SingularValueBounds.KL.Certificates.EndpointMeanEntropyRows.Row59

/-! All four entropy corners of every active endpoint rectangle. -/
namespace SingularValueBounds.KL.Certificates

theorem endpointMean_jointCorners (ki : Fin 60) (ai : Fin 42)
    (hactive : endpointMeanActive ki ai) (h : Fin 4) :
    endpointMeanNumericCorner ki ai h ≤ endpointMeanCorner ki ai h := by
  revert ki ai hactive h
  exact Fin.cases (motive := fun ki => ∀ ai : Fin 42, endpointMeanActive ki ai →
      ∀ h : Fin 4, endpointMeanNumericCorner ki ai h ≤ endpointMeanCorner ki ai h)
    endpointMeanEntropyRow00 <|
    Fin.cases endpointMeanEntropyRow01 <|
    Fin.cases endpointMeanEntropyRow02 <|
    Fin.cases endpointMeanEntropyRow03 <|
    Fin.cases endpointMeanEntropyRow04 <|
    Fin.cases endpointMeanEntropyRow05 <|
    Fin.cases endpointMeanEntropyRow06 <|
    Fin.cases endpointMeanEntropyRow07 <|
    Fin.cases endpointMeanEntropyRow08 <|
    Fin.cases endpointMeanEntropyRow09 <|
    Fin.cases endpointMeanEntropyRow10 <|
    Fin.cases endpointMeanEntropyRow11 <|
    Fin.cases endpointMeanEntropyRow12 <|
    Fin.cases endpointMeanEntropyRow13 <|
    Fin.cases endpointMeanEntropyRow14 <|
    Fin.cases endpointMeanEntropyRow15 <|
    Fin.cases endpointMeanEntropyRow16 <|
    Fin.cases endpointMeanEntropyRow17 <|
    Fin.cases endpointMeanEntropyRow18 <|
    Fin.cases endpointMeanEntropyRow19 <|
    Fin.cases endpointMeanEntropyRow20 <|
    Fin.cases endpointMeanEntropyRow21 <|
    Fin.cases endpointMeanEntropyRow22 <|
    Fin.cases endpointMeanEntropyRow23 <|
    Fin.cases endpointMeanEntropyRow24 <|
    Fin.cases endpointMeanEntropyRow25 <|
    Fin.cases endpointMeanEntropyRow26 <|
    Fin.cases endpointMeanEntropyRow27 <|
    Fin.cases endpointMeanEntropyRow28 <|
    Fin.cases endpointMeanEntropyRow29 <|
    Fin.cases endpointMeanEntropyRow30 <|
    Fin.cases endpointMeanEntropyRow31 <|
    Fin.cases endpointMeanEntropyRow32 <|
    Fin.cases endpointMeanEntropyRow33 <|
    Fin.cases endpointMeanEntropyRow34 <|
    Fin.cases endpointMeanEntropyRow35 <|
    Fin.cases endpointMeanEntropyRow36 <|
    Fin.cases endpointMeanEntropyRow37 <|
    Fin.cases endpointMeanEntropyRow38 <|
    Fin.cases endpointMeanEntropyRow39 <|
    Fin.cases endpointMeanEntropyRow40 <|
    Fin.cases endpointMeanEntropyRow41 <|
    Fin.cases endpointMeanEntropyRow42 <|
    Fin.cases endpointMeanEntropyRow43 <|
    Fin.cases endpointMeanEntropyRow44 <|
    Fin.cases endpointMeanEntropyRow45 <|
    Fin.cases endpointMeanEntropyRow46 <|
    Fin.cases endpointMeanEntropyRow47 <|
    Fin.cases endpointMeanEntropyRow48 <|
    Fin.cases endpointMeanEntropyRow49 <|
    Fin.cases endpointMeanEntropyRow50 <|
    Fin.cases endpointMeanEntropyRow51 <|
    Fin.cases endpointMeanEntropyRow52 <|
    Fin.cases endpointMeanEntropyRow53 <|
    Fin.cases endpointMeanEntropyRow54 <|
    Fin.cases endpointMeanEntropyRow55 <|
    Fin.cases endpointMeanEntropyRow56 <|
    Fin.cases endpointMeanEntropyRow57 <|
    Fin.cases endpointMeanEntropyRow58 <|
    Fin.cases endpointMeanEntropyRow59 <|
    fun ki => Fin.elim0 ki

end SingularValueBounds.KL.Certificates
