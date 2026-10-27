import SingularValueBounds.KL.Certificates.EndpointEntropyLogData
import SingularValueBounds.KL.Certificates.IntegerRoundedLogEvaluation
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Kernel checks for endpoint logarithm grid nodes 7681 through 7936. -/
namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem endpointLogGridBlock30 : ∀ i : Fin 256,
    logRoundedQ (((7680+i.val+1 : ℕ) : ℚ)/200) =
      (fixedQ (endpointLogLower (7680+i.val+1)), fixedQ (endpointLogUpper (7680+i.val+1))) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

end SingularValueBounds.KL.Certificates
