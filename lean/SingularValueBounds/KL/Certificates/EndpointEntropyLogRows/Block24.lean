import SingularValueBounds.KL.Certificates.EndpointEntropyLogData
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanSmall
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Kernel checks for endpoint logarithm grid nodes 6145 through 6400. -/
namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem endpointLogGridBlock24 : ∀ i : Fin 256,
    logRoundedQ (((6144+i.val+1 : ℕ) : ℚ)/200) =
      (fixedQ (endpointLogLower (6144+i.val+1)), fixedQ (endpointLogUpper (6144+i.val+1))) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

end SingularValueBounds.KL.Certificates
