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
  fin_cases ki
  · exact endpointMeanEntropyRow00 ai hactive h
  · exact endpointMeanEntropyRow01 ai hactive h
  · exact endpointMeanEntropyRow02 ai hactive h
  · exact endpointMeanEntropyRow03 ai hactive h
  · exact endpointMeanEntropyRow04 ai hactive h
  · exact endpointMeanEntropyRow05 ai hactive h
  · exact endpointMeanEntropyRow06 ai hactive h
  · exact endpointMeanEntropyRow07 ai hactive h
  · exact endpointMeanEntropyRow08 ai hactive h
  · exact endpointMeanEntropyRow09 ai hactive h
  · exact endpointMeanEntropyRow10 ai hactive h
  · exact endpointMeanEntropyRow11 ai hactive h
  · exact endpointMeanEntropyRow12 ai hactive h
  · exact endpointMeanEntropyRow13 ai hactive h
  · exact endpointMeanEntropyRow14 ai hactive h
  · exact endpointMeanEntropyRow15 ai hactive h
  · exact endpointMeanEntropyRow16 ai hactive h
  · exact endpointMeanEntropyRow17 ai hactive h
  · exact endpointMeanEntropyRow18 ai hactive h
  · exact endpointMeanEntropyRow19 ai hactive h
  · exact endpointMeanEntropyRow20 ai hactive h
  · exact endpointMeanEntropyRow21 ai hactive h
  · exact endpointMeanEntropyRow22 ai hactive h
  · exact endpointMeanEntropyRow23 ai hactive h
  · exact endpointMeanEntropyRow24 ai hactive h
  · exact endpointMeanEntropyRow25 ai hactive h
  · exact endpointMeanEntropyRow26 ai hactive h
  · exact endpointMeanEntropyRow27 ai hactive h
  · exact endpointMeanEntropyRow28 ai hactive h
  · exact endpointMeanEntropyRow29 ai hactive h
  · exact endpointMeanEntropyRow30 ai hactive h
  · exact endpointMeanEntropyRow31 ai hactive h
  · exact endpointMeanEntropyRow32 ai hactive h
  · exact endpointMeanEntropyRow33 ai hactive h
  · exact endpointMeanEntropyRow34 ai hactive h
  · exact endpointMeanEntropyRow35 ai hactive h
  · exact endpointMeanEntropyRow36 ai hactive h
  · exact endpointMeanEntropyRow37 ai hactive h
  · exact endpointMeanEntropyRow38 ai hactive h
  · exact endpointMeanEntropyRow39 ai hactive h
  · exact endpointMeanEntropyRow40 ai hactive h
  · exact endpointMeanEntropyRow41 ai hactive h
  · exact endpointMeanEntropyRow42 ai hactive h
  · exact endpointMeanEntropyRow43 ai hactive h
  · exact endpointMeanEntropyRow44 ai hactive h
  · exact endpointMeanEntropyRow45 ai hactive h
  · exact endpointMeanEntropyRow46 ai hactive h
  · exact endpointMeanEntropyRow47 ai hactive h
  · exact endpointMeanEntropyRow48 ai hactive h
  · exact endpointMeanEntropyRow49 ai hactive h
  · exact endpointMeanEntropyRow50 ai hactive h
  · exact endpointMeanEntropyRow51 ai hactive h
  · exact endpointMeanEntropyRow52 ai hactive h
  · exact endpointMeanEntropyRow53 ai hactive h
  · exact endpointMeanEntropyRow54 ai hactive h
  · exact endpointMeanEntropyRow55 ai hactive h
  · exact endpointMeanEntropyRow56 ai hactive h
  · exact endpointMeanEntropyRow57 ai hactive h
  · exact endpointMeanEntropyRow58 ai hactive h
  · exact endpointMeanEntropyRow59 ai hactive h
end SingularValueBounds.KL.Certificates
