import SingularValueBounds.KL.Upper.RoundedAlgorithm

/-! Exact constant terms shared by every scaled rounded logarithm. -/
namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem logUnitLowerQ_two : logUnitLowerQ 2 = 693147180559935/1000000000000000 := by
  decide +kernel

theorem logUnitUpperQ_two : logUnitUpperQ 2 = 693147180559958/1000000000000000 := by
  decide +kernel

end SingularValueBounds.KL.Certificates
