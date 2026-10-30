import SingularValueBounds.KL.Certificates.ConcreteGeneralSecondBounds
import SingularValueBounds.KL.Certificates.ConcreteGeneralSecondCells

/-! The complete concrete general upper second-moment certificate family.
Each finite condition is supplied by a kernel-checked Lean theorem. -/

namespace SingularValueBounds.KL.UpperSecond

theorem generalSecondCertificateConditions : GeneralSecondCertificateConditions :=
  ⟨secondSmallExclusion, secondSmallExp_nonneg, secondSmallUpperQ_lt,
    secondCellConditions, secondCellUpperQ_lt⟩

end SingularValueBounds.KL.UpperSecond
