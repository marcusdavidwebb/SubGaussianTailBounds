import SingularValueBounds.KL.Certificates.IntegerRoundedLogEvaluation
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Upper.EndpointRoundedEval

/-! A shared exact rewrite for endpoint prefactor computations. -/
namespace SingularValueBounds.KL.Certificates

noncomputable def integerEndpointJointPrefactor (k a q : ℚ) : ℚ :=
  integerExpUpper (roundUpQ (q / 2) +
    roundUpQ (a * (-(integerLogRounded (1 - q * k^2)).1 - roundDownQ (q * k^2)) /
      (2 * k^3)))

/-- The evaluator preserves every rounding step of the endpoint prefactor. -/
theorem endpointJointPrefactorQ_eq_integer (k a q : ℚ) :
    endpointJointPrefactorQ k a q = integerEndpointJointPrefactor k a q := by
  simp only [endpointJointPrefactorQ, endpointJointLogUpperQ,
    integerEndpointJointPrefactor, logRoundedQ_eq_integer, expUpperRoundedQ_eq_integer]

end SingularValueBounds.KL.Certificates
