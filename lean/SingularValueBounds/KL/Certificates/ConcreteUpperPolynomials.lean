import SingularValueBounds.KL.Upper.CertificateData
open Polynomial
open scoped BigOperators
/-! Kernel-checked algebraic components of the upper polynomial certificates.
This module does not yet prove the complete majorant or rate finite conditions. -/

namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private theorem eq_X_sq_mul_divX_divX {R : Type*} [CommRing R] (p : Polynomial R)
    (h0 : p.coeff 0 = 0) (h1 : p.coeff 1 = 0) :
    p = X ^ 2 * p.divX.divX := by
  have hp : p = X * p.divX := by simpa [h0] using (X_mul_divX_add p).symm
  have hq : p.divX = X * p.divX.divX := by
    simpa [coeff_divX, h1] using (X_mul_divX_add p.divX).symm
  calc
    p = X * p.divX := hp
    _ = X * (X * p.divX.divX) := congrArg (X * ·) hq
    _ = X ^ 2 * p.divX.divX := by ring

/-- The double `divX` used by all six majorants loses no term. -/
theorem majorant_cleared_factorization (i : Fin 6) : majorantCleared i = X ^ 2 * majorantQuotient i := by
  apply eq_X_sq_mul_divX_divX
  · simp [majorantCleared, majorantHQ, padeDQ, padeNQ, comparisonZQ, coeff_zero_eq_eval_zero]
  · simp [majorantCleared, majorantHQ, padeDQ, padeNQ, comparisonZQ,
      pow_succ, mul_coeff_one, mul_coeff_zero]

end SingularValueBounds.KL.Certificates
