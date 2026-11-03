import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block00
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block01
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block02
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block03
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block04
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block05
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block06
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block07
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block08
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block09
import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Small

namespace SingularValueBounds.KL.Certificates
theorem endpointMean_analytic (ki : Fin 60) (ai : Fin 42) : endpointMeanActive ki ai →
    EndpointJointNumericalConditions ki ai := by
  revert ki ai
  exact Fin.cases (motive := fun ki => ∀ai : Fin 42, endpointMeanActive ki ai →
    EndpointJointNumericalConditions ki ai) endpointAnalyticRow00 <|
    Fin.cases endpointAnalyticRow01 <|
    Fin.cases endpointAnalyticRow02 <|
    Fin.cases endpointAnalyticRow03 <|
    Fin.cases endpointAnalyticRow04 <|
    Fin.cases endpointAnalyticRow05 <|
    Fin.cases endpointAnalyticRow06 <|
    Fin.cases endpointAnalyticRow07 <|
    Fin.cases endpointAnalyticRow08 <|
    Fin.cases endpointAnalyticRow09 <|
    Fin.cases endpointAnalyticRow10 <|
    Fin.cases endpointAnalyticRow11 <|
    Fin.cases endpointAnalyticRow12 <|
    Fin.cases endpointAnalyticRow13 <|
    Fin.cases endpointAnalyticRow14 <|
    Fin.cases endpointAnalyticRow15 <|
    Fin.cases endpointAnalyticRow16 <|
    Fin.cases endpointAnalyticRow17 <|
    Fin.cases endpointAnalyticRow18 <|
    Fin.cases endpointAnalyticRow19 <|
    Fin.cases endpointAnalyticRow20 <|
    Fin.cases endpointAnalyticRow21 <|
    Fin.cases endpointAnalyticRow22 <|
    Fin.cases endpointAnalyticRow23 <|
    Fin.cases endpointAnalyticRow24 <|
    Fin.cases endpointAnalyticRow25 <|
    Fin.cases endpointAnalyticRow26 <|
    Fin.cases endpointAnalyticRow27 <|
    Fin.cases endpointAnalyticRow28 <|
    Fin.cases endpointAnalyticRow29 <|
    Fin.cases endpointAnalyticRow30 <|
    Fin.cases endpointAnalyticRow31 <|
    Fin.cases endpointAnalyticRow32 <|
    Fin.cases endpointAnalyticRow33 <|
    Fin.cases endpointAnalyticRow34 <|
    Fin.cases endpointAnalyticRow35 <|
    Fin.cases endpointAnalyticRow36 <|
    Fin.cases endpointAnalyticRow37 <|
    Fin.cases endpointAnalyticRow38 <|
    Fin.cases endpointAnalyticRow39 <|
    Fin.cases endpointAnalyticRow40 <|
    Fin.cases endpointAnalyticRow41 <|
    Fin.cases endpointAnalyticRow42 <|
    Fin.cases endpointAnalyticRow43 <|
    Fin.cases endpointAnalyticRow44 <|
    Fin.cases endpointAnalyticRow45 <|
    Fin.cases endpointAnalyticRow46 <|
    Fin.cases endpointAnalyticRow47 <|
    Fin.cases endpointAnalyticRow48 <|
    Fin.cases endpointAnalyticRow49 <|
    Fin.cases endpointAnalyticRow50 <|
    Fin.cases endpointAnalyticRow51 <|
    Fin.cases endpointAnalyticRow52 <|
    Fin.cases endpointAnalyticRow53 <|
    Fin.cases endpointAnalyticRow54 <|
    Fin.cases endpointAnalyticRow55 <|
    Fin.cases endpointAnalyticRow56 <|
    Fin.cases endpointAnalyticRow57 <|
    Fin.cases endpointAnalyticRow58 <|
    Fin.cases endpointAnalyticRow59 <|
    fun ki => Fin.elim0 ki

theorem endpointSmall_analytic (i : Fin 50) : EndpointSmallNumericalConditions i := by
  fin_cases i
  · exact EndpointAnalyticSmall00.conditions
  · exact EndpointAnalyticSmall01.conditions
  · exact EndpointAnalyticSmall02.conditions
  · exact EndpointAnalyticSmall03.conditions
  · exact EndpointAnalyticSmall04.conditions
  · exact EndpointAnalyticSmall05.conditions
  · exact EndpointAnalyticSmall06.conditions
  · exact EndpointAnalyticSmall07.conditions
  · exact EndpointAnalyticSmall08.conditions
  · exact EndpointAnalyticSmall09.conditions
  · exact EndpointAnalyticSmall10.conditions
  · exact EndpointAnalyticSmall11.conditions
  · exact EndpointAnalyticSmall12.conditions
  · exact EndpointAnalyticSmall13.conditions
  · exact EndpointAnalyticSmall14.conditions
  · exact EndpointAnalyticSmall15.conditions
  · exact EndpointAnalyticSmall16.conditions
  · exact EndpointAnalyticSmall17.conditions
  · exact EndpointAnalyticSmall18.conditions
  · exact EndpointAnalyticSmall19.conditions
  · exact EndpointAnalyticSmall20.conditions
  · exact EndpointAnalyticSmall21.conditions
  · exact EndpointAnalyticSmall22.conditions
  · exact EndpointAnalyticSmall23.conditions
  · exact EndpointAnalyticSmall24.conditions
  · exact EndpointAnalyticSmall25.conditions
  · exact EndpointAnalyticSmall26.conditions
  · exact EndpointAnalyticSmall27.conditions
  · exact EndpointAnalyticSmall28.conditions
  · exact EndpointAnalyticSmall29.conditions
  · exact EndpointAnalyticSmall30.conditions
  · exact EndpointAnalyticSmall31.conditions
  · exact EndpointAnalyticSmall32.conditions
  · exact EndpointAnalyticSmall33.conditions
  · exact EndpointAnalyticSmall34.conditions
  · exact EndpointAnalyticSmall35.conditions
  · exact EndpointAnalyticSmall36.conditions
  · exact EndpointAnalyticSmall37.conditions
  · exact EndpointAnalyticSmall38.conditions
  · exact EndpointAnalyticSmall39.conditions
  · exact EndpointAnalyticSmall40.conditions
  · exact EndpointAnalyticSmall41.conditions
  · exact EndpointAnalyticSmall42.conditions
  · exact EndpointAnalyticSmall43.conditions
  · exact EndpointAnalyticSmall44.conditions
  · exact EndpointAnalyticSmall45.conditions
  · exact EndpointAnalyticSmall46.conditions
  · exact EndpointAnalyticSmall47.conditions
  · exact EndpointAnalyticSmall48.conditions
  · exact EndpointAnalyticSmall49.conditions

end SingularValueBounds.KL.Certificates
