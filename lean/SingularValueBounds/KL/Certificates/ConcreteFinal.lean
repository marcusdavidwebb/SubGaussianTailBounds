import SingularValueBounds.KL.Certificates.Final
import SingularValueBounds.KL.Certificates.ConcreteGeneralLower
import SingularValueBounds.KL.Certificates.ConcreteEndpointTable
import SingularValueBounds.KL.Certificates.ConcreteEndpointFar
import SingularValueBounds.KL.Certificates.ConcreteMajorants
import SingularValueBounds.KL.Certificates.ConcreteNormDeterminants
import SingularValueBounds.KL.Certificates.ConcreteRates
import SingularValueBounds.KL.Certificates.ConcreteEndpointLogratio
import SingularValueBounds.KL.Certificates.ConcreteGeneralSecond
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanCells
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropy
import SingularValueBounds.KL.Certificates.ConcreteEndpointMean

/-!
All eleven finite certificate families, assembled from concrete Lean proofs.
-/
namespace SingularValueBounds.KL
open Certificates

theorem finalCertificateConditions_of_endpointMean
    (hendpoint : EndpointMeanCertificateConditions) : FinalCertificateConditions := {
  generalLower := generalLowerCertificateConditions
  endpointLowerTable := endpointTableConditions
  endpointLowerFar := endpointFarConditions
  majorant := majorantCertificateConditions
  normDeterminant := normDeterminantCertificateConditions
  rate := rateCertificateConditions
  generalMeanCells := generalMeanCellConditions
  generalMeanEntropy := generalMeanEntropyConditions
  endpointMean := hendpoint
  endpointLogratio := endpointLogratioCertificateConditions
  generalSecond := UpperSecond.generalSecondCertificateConditions
}

theorem finalCertificateConditions : FinalCertificateConditions :=
  finalCertificateConditions_of_endpointMean endpointMeanCertificateConditions

end SingularValueBounds.KL
