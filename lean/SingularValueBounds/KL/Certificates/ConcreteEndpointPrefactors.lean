import SingularValueBounds.KL.Upper.EndpointMeanFinite
import SingularValueBounds.KL.Certificates.ConcreteLog

/-!
Uniform endpoint-prefactor transcripts and the complete small-range family.
The logarithm and rounding conditions follow from uniform Lean proofs. The
remaining concrete Taylor-domain bounds use exact rational kernel evaluation.
-/
namespace SingularValueBounds.KL.Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem endpointJointPrefactorConditions {k a q : ℚ}
    (hk : 0 < k) (ha : 0 ≤ a) (hgap : q * k^2 < 1)
    (hexp : roundUpQ (endpointJointLogUpperQ k a q) < 82) :
    EndpointJointPrefactorConditions k a q := by
  exact ⟨hk, ha, hgap, roundedLogConditions (by linarith),
    roundDownQ_le _, le_roundUpQ _, le_roundUpQ _, roundedExpConditions hexp⟩

theorem endpointSmallPrefactorConditions {k q : ℚ}
    (hk : 0 < k) (hgap : q * k^2 < 1)
    (hexp : roundUpQ (roundUpQ (-(logRoundedQ (1-q*k^2)).1/(2*k^2))) < 82) :
    EndpointSmallPrefactorConditions k q := by
  exact ⟨hk, hgap, roundedLogConditions (by linarith),
    le_roundUpQ _, roundedExpConditions hexp⟩

theorem endpointMean_smallPrefactor_shape (i : Fin 50) : 0 < endpointSmallK i := by
  unfold endpointSmallK
  positivity

theorem endpointMean_smallPrefactor_gap (i : Fin 50) (h : Fin 23) :
    ((endpointSmallQ h : ℚ)/100) * (endpointSmallK i)^2 < 1 := by
  revert i h
  decide +kernel

theorem endpointMean_smallPrefactor_expDomain (i : Fin 50) (h : Fin 23) :
    roundUpQ (roundUpQ
      (-(logRoundedQ (1-((endpointSmallQ h : ℚ)/100)*(endpointSmallK i)^2)).1 /
        (2*(endpointSmallK i)^2))) < 82 := by
  revert i h
  decide +kernel

/-- All 1,150 small-range endpoint prefactor conditions, without numerical premises. -/
theorem endpointMean_smallPrefactors (i : Fin 50) (h : Fin 23) :
    EndpointSmallPrefactorConditions (endpointSmallK i) ((endpointSmallQ h : ℚ)/100) :=
  endpointSmallPrefactorConditions (endpointMean_smallPrefactor_shape i)
    (endpointMean_smallPrefactor_gap i h) (endpointMean_smallPrefactor_expDomain i h)

end SingularValueBounds.KL.Certificates
