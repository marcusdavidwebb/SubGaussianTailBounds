import SingularValueBounds.KL.Upper.GeneralSecondData

/-! Concrete second-moment upper margins, proved by kernel-checked rational
arithmetic. The finite indices cover every cell, not a numerical sample. -/

namespace SingularValueBounds.KL.UpperSecond
open Certificates.NumericalCertificateConditions
set_option maxHeartbeats 800000000
set_option maxRecDepth 10000

/-- All three bounds in each of the 334 spectral cells. -/
theorem secondCellUpperQ_lt (j : Fin 334) (i : Fin 3) :
    secondCellUpperQ j i < 9 / 2 := by
  revert j i
  decide +kernel

end SingularValueBounds.KL.UpperSecond
