import SingularValueBounds.KL.Lower.PlateauCertificates
import SingularValueBounds.KL.Certificates.BernsteinIdentity
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.LowerCertificates
set_option maxRecDepth 10000
set_option maxHeartbeats 0
/-- The degree-zero and degree-one terms cancel exactly. -/
theorem plateauQ_factorization (u A v w c : ℚ) : X^2*plateauQ u A v w c =
    plateauD u A c*polynomialExpTaylor 24 (plateauPsi u v w)-1 := by
  let p := plateauD u A c*polynomialExpTaylor 24 (plateauPsi u v w)-1
  have h0 : p.coeff 0 = 0 := by
    simp [p, plateauD, polynomialExpTaylor, plateauPsi, coeff_zero_eq_eval_zero,
      Finset.sum_range_succ]
  have h1 : p.coeff 1 = 0 := by
    simp [p, plateauD, polynomialExpTaylor, plateauPsi, Finset.sum_range_succ,
      pow_succ, mul_coeff_one, mul_coeff_zero]
    norm_num [Polynomial.coeff_one]
  have hp : p = X * p.divX := by simpa [h0] using (X_mul_divX_add p).symm
  have hq : p.divX = X * p.divX.divX := by
    simpa [coeff_divX, h1] using (X_mul_divX_add p.divX).symm
  change X^2*p.divX.divX = p
  calc
    X^2*p.divX.divX = X*(X*p.divX.divX) := by ring
    _ = X*p.divX := congrArg (X * ·) hq.symm
    _ = p := hp.symm
end SingularValueBounds.KL.LowerCertificates
