import SingularValueBounds.KL.Lower.CellData

/-! The complete 681-cell lower moment family is checked by Lean's kernel. -/
namespace SingularValueBounds.KL.LowerCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every rational moment-cell condition, including the separate endpoint cell. -/
theorem momentCellConditions : MomentCellConditions := by
  constructor
  · intro j
    constructor <;> revert j <;> decide +kernel
  · constructor <;> decide +kernel

end SingularValueBounds.KL.LowerCertificates
