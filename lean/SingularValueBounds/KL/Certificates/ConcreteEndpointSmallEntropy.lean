import SingularValueBounds.KL.Certificates.EndpointSmallEntropyRows.Block00
import SingularValueBounds.KL.Certificates.EndpointSmallEntropyRows.Block01
import SingularValueBounds.KL.Certificates.EndpointSmallEntropyRows.Block02
import SingularValueBounds.KL.Certificates.EndpointSmallEntropyRows.Block03
import SingularValueBounds.KL.Certificates.EndpointSmallEntropyRows.Block04

/-! All fifty small-spectrum entropy intervals at the exact endpoint constants. -/
namespace SingularValueBounds.KL.Certificates

theorem endpointMean_smallNumerical (i : Fin 50) :
    entropyGridBoundQ (endpointSmallCutoff i) (endpointSmallBound i)
      (endpointDecayQ 90 8000) ≤ endpointSmallTarget i := by
  fin_cases i
  · exact EndpointSmallEntropy00.numerical
  · exact EndpointSmallEntropy01.numerical
  · exact EndpointSmallEntropy02.numerical
  · exact EndpointSmallEntropy03.numerical
  · exact EndpointSmallEntropy04.numerical
  · exact EndpointSmallEntropy05.numerical
  · exact EndpointSmallEntropy06.numerical
  · exact EndpointSmallEntropy07.numerical
  · exact EndpointSmallEntropy08.numerical
  · exact EndpointSmallEntropy09.numerical
  · exact EndpointSmallEntropy10.numerical
  · exact EndpointSmallEntropy11.numerical
  · exact EndpointSmallEntropy12.numerical
  · exact EndpointSmallEntropy13.numerical
  · exact EndpointSmallEntropy14.numerical
  · exact EndpointSmallEntropy15.numerical
  · exact EndpointSmallEntropy16.numerical
  · exact EndpointSmallEntropy17.numerical
  · exact EndpointSmallEntropy18.numerical
  · exact EndpointSmallEntropy19.numerical
  · exact EndpointSmallEntropy20.numerical
  · exact EndpointSmallEntropy21.numerical
  · exact EndpointSmallEntropy22.numerical
  · exact EndpointSmallEntropy23.numerical
  · exact EndpointSmallEntropy24.numerical
  · exact EndpointSmallEntropy25.numerical
  · exact EndpointSmallEntropy26.numerical
  · exact EndpointSmallEntropy27.numerical
  · exact EndpointSmallEntropy28.numerical
  · exact EndpointSmallEntropy29.numerical
  · exact EndpointSmallEntropy30.numerical
  · exact EndpointSmallEntropy31.numerical
  · exact EndpointSmallEntropy32.numerical
  · exact EndpointSmallEntropy33.numerical
  · exact EndpointSmallEntropy34.numerical
  · exact EndpointSmallEntropy35.numerical
  · exact EndpointSmallEntropy36.numerical
  · exact EndpointSmallEntropy37.numerical
  · exact EndpointSmallEntropy38.numerical
  · exact EndpointSmallEntropy39.numerical
  · exact EndpointSmallEntropy40.numerical
  · exact EndpointSmallEntropy41.numerical
  · exact EndpointSmallEntropy42.numerical
  · exact EndpointSmallEntropy43.numerical
  · exact EndpointSmallEntropy44.numerical
  · exact EndpointSmallEntropy45.numerical
  · exact EndpointSmallEntropy46.numerical
  · exact EndpointSmallEntropy47.numerical
  · exact EndpointSmallEntropy48.numerical
  · exact EndpointSmallEntropy49.numerical
end SingularValueBounds.KL.Certificates
