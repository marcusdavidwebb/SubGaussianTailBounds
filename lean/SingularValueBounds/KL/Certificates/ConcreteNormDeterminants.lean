import SingularValueBounds.KL.Upper.NormDeterminants

/-!
Kernel-checked concrete instances for the two norm determinant Taylor bounds.
These proofs remove this numerical field from the remaining certificate obligations.
-/

namespace SingularValueBounds.KL

open Certificates.NumericalCertificateConditions

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Both rational Taylor inequalities are proved by exact Lean arithmetic. -/
theorem normDeterminantCertificateConditions : NormDeterminantCertificateConditions := by
  constructor <;>
    norm_num [expTaylorQ, Finset.sum_range_succ]

end SingularValueBounds.KL
