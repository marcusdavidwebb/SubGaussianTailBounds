import SingularValueBounds.KL.Upper.EndpointMeanFinite
import SingularValueBounds.KL.Certificates.UniformEndpointPrefactors

/-!
Uniform endpoint-prefactor transcripts and the complete small-range family.
The logarithm, rounding and small-range Taylor-domain conditions follow from
uniform inequalities; no input-specific prefactor evaluation is needed.
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

private theorem endpointSmallK_bounds (i : Fin 50) :
    1/200 ≤ endpointSmallK i ∧ endpointSmallK i ≤ 1/4 := by
  have hi : (i.val : ℚ) ≤ 49 := by exact_mod_cast (show i.val ≤ 49 by omega)
  have hi0 : (0 : ℚ) ≤ i.val := Nat.cast_nonneg _
  unfold endpointSmallK
  constructor <;> linarith

private theorem endpointSmallQ_bounds (h : Fin 23) :
    0 < (endpointSmallQ h : ℚ)/100 ∧ (endpointSmallQ h : ℚ)/100 ≤ 2 := by
  have hh : (h.val : ℚ) ≤ 22 := by exact_mod_cast (show h.val ≤ 22 by omega)
  have hh0 : (0 : ℚ) ≤ h.val := Nat.cast_nonneg _
  unfold endpointSmallQ
  push_cast
  constructor <;> linarith

theorem endpointMean_smallPrefactor_gap (i : Fin 50) (h : Fin 23) :
    ((endpointSmallQ h : ℚ)/100) * (endpointSmallK i)^2 < 1 := by
  have hk := endpointSmallK_bounds i
  have hq := endpointSmallQ_bounds h
  have hk2 : (endpointSmallK i)^2 ≤ 1/16 := by nlinarith
  have hb := mul_le_mul hq.2 hk2 (sq_nonneg (endpointSmallK i))
    (by norm_num : (0 : ℚ) ≤ 2)
  linarith

theorem endpointMean_smallPrefactor_expDomain (i : Fin 50) (h : Fin 23) :
    roundUpQ (roundUpQ
      (-(logRoundedQ (1-((endpointSmallQ h : ℚ)/100)*(endpointSmallK i)^2)).1 /
        (2*(endpointSmallK i)^2))) < 82 := by
  exact endpointSmallPrefactor_expDomain_uniform
    (endpointSmallK_bounds i).1 (endpointSmallK_bounds i).2
    (endpointSmallQ_bounds h).1 (endpointSmallQ_bounds h).2

/-- All 1,150 small-range endpoint prefactor conditions, without numerical premises. -/
theorem endpointMean_smallPrefactors (i : Fin 50) (h : Fin 23) :
    EndpointSmallPrefactorConditions (endpointSmallK i) ((endpointSmallQ h : ℚ)/100) :=
  endpointSmallPrefactorConditions (endpointMean_smallPrefactor_shape i)
    (endpointMean_smallPrefactor_gap i h) (endpointMean_smallPrefactor_expDomain i h)

end SingularValueBounds.KL.Certificates
