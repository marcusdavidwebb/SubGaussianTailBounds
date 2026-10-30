import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Whole-function integer evaluation of the original rounded logarithm.
The exact reduction fuel, 18 terms, remainder, and base-two constants are preserved. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A structurally recursive evaluator for the natural base-two logarithm.
The fuel is deliberately a separate argument so kernel reduction can stop as
soon as the repeatedly halved input is below two. -/
def logTwoFuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if 2 ≤ n then logTwoFuel f (n / 2) + 1 else 0

theorem logTwoFuel_correct (f n : ℕ) (hn : n ≤ f) :
    logTwoFuel f n = Nat.log 2 n := by
  induction f generalizing n with
  | zero =>
    have hz : n = 0 := by omega
    subst n
    simp [logTwoFuel]
  | succ f ih =>
    by_cases h : 2 ≤ n
    · rw [logTwoFuel, if_pos h, Nat.log_of_one_lt_of_le (by decide) h]
      rw [ih]
      have : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      omega
    · rw [logTwoFuel, if_neg h, Nat.log_of_lt (by omega : n < 2)]

/-- Replace the opaque well-founded logarithm by a proved kernel computation. -/
theorem natLog_two_eq_logTwoFuel (n : ℕ) : Nat.log 2 n = logTwoFuel n n :=
  (logTwoFuel_correct n n le_rfl).symm

noncomputable def integerLogPositive (x : ℚ) : ℚ × ℚ :=
  let pair := reduceLogPowTwo (logTwoFuel x.num.natAbs x.num.natAbs + 1) x
  let lower := fixedQ (∑ j ∈ Finset.range 18, logCoeffLowerInt pair.2 j)
  let upper := fixedQ (∑ j ∈ Finset.range 18, logCoeffUpperInt pair.2 j) +
    roundUpQ (2 * fixedQ (logPowerUpperInt (logZUpperInt pair.2) (logZ2UpperInt pair.2) 18) /
      (37 * (1 - fixedQ (logZ2UpperInt pair.2))))
  (lower + (pair.1 : ℚ) * (693147180559935 / 1000000000000000),
    upper + (pair.1 : ℚ) * (693147180559958 / 1000000000000000))

theorem logPositiveRoundedQ_eq_integer (x : ℚ) :
    logPositiveRoundedQ x = integerLogPositive x := by
  simp only [logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [integerLogPositive, logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]

noncomputable def integerLogRounded (x : ℚ) : ℚ × ℚ :=
  if x < 1 then
    let pair := integerLogPositive (1 / x)
    (-pair.2, -pair.1)
  else integerLogPositive x

/-- Exact equality with the complete original rounded algorithm. -/
theorem logRoundedQ_eq_integer (x : ℚ) :
    logRoundedQ x = integerLogRounded x := by
  simp only [logRoundedQ, integerLogRounded, logPositiveRoundedQ_eq_integer]

end SingularValueBounds.KL.Certificates
