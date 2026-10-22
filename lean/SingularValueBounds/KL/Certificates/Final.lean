import SingularValueBounds.KL.Lower.GeneralProfile
import SingularValueBounds.KL.Lower.EndpointCap
import SingularValueBounds.KL.Upper.GeneralApplication
import SingularValueBounds.KL.Upper.EndpointFullApplication

/-! Finite numerical premises for the current supplementary theorem.
Every field is a bounded rational comparison, coefficient identity, finite
partition condition or exact rounded-arithmetic transcript. Analytic row
estimates and pathwise budgets are deliberately absent from this structure. -/
namespace SingularValueBounds.KL
open Certificates UpperSecond

structure FinalCertificateConditions : Prop where
  generalLower : GeneralLowerCertificateConditions
  endpointLowerTable : EndpointTableConditions
  endpointLowerFar : EndpointFarConditions
  majorant : MajorantCertificateConditions
  normDeterminant : NormDeterminantCertificateConditions
  rate : RateCertificateConditions
  generalMeanCells : GeneralMeanCellConditions
  generalMeanEntropy : GeneralMeanEntropyConditions
  endpointMean : EndpointMeanCertificateConditions
  endpointLogratio : EndpointLogratioCertificateConditions
  generalSecond : GeneralSecondCertificateConditions

end SingularValueBounds.KL
