import SingularValueBounds.KL.Upper.GeneralMeanCells
import SingularValueBounds.KL.Certificates.ConcreteLog

/-!
Concrete numerical conditions for the general upper-mean small spectral range.
Rounded-function transcripts follow from the uniform Lean soundness lemmas;
the remaining finite rational margins are evaluated by Lean's kernel.
-/
namespace SingularValueBounds.KL.Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem le_finalEntropyRoundQ (x : ℚ) : x ≤ finalEntropyRoundQ x := by
  unfold finalEntropyRoundQ
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 10000000000)]
  have h := Int.floor_le (-(x * 10000000000))
  linarith

theorem generalMeanGrid_pos (j : ℕ) : 0 < generalMeanGrid j := by
  unfold generalMeanGrid
  positivity

theorem generalMeanCriticalPoint_pos (r : GeneralMeanRow) (j : ℕ) :
    0 < r.criticalPoint j := by
  unfold GeneralMeanRow.criticalPoint
  exact lt_min (generalMeanGrid_pos _) ((generalMeanGrid_pos _).trans_le (le_max_left _ _))

theorem generalMeanSmallRow_prefactor_domain :
    roundUpQ generalMeanSmallRow.prefactorArgument < 82 := by
  decide +kernel

theorem generalMeanSmallRow_slopePositive (j : Fin 120) :
    0 < generalMeanSmallRow.criticalRate j.val := by
  revert j
  decide +kernel

theorem generalMeanSmallRow_criticalMargin (j : Fin 120) :
    0 ≤ 2 + generalMeanSmallRow.criticalRate j.val * generalMeanSmallRow.criticalPoint j.val -
      (logRoundedQ (generalMeanSmallRow.c * generalMeanSmallRow.criticalPoint j.val)).2 -
      generalMeanSmallRow.J / 2 - generalMeanSmallRow.error (generalMeanGrid j.val) +
      generalMeanSmallRow.slope j.val * generalMeanGrid j.val := by
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  decide +kernel

theorem generalMeanSmallRow_finalMargin :
    0 ≤ 2 + 4 * (47 / 20 - 2) - (logRoundedQ (4 * generalMeanSmallRow.c)).2 -
      generalMeanSmallRow.J / 2 - generalMeanSmallRow.error 4 := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  decide +kernel

/-- The complete small-range member of the general upper-mean numerical family. -/
theorem generalMeanSmallRow_numerical : GeneralMeanNumericalConditions generalMeanSmallRow := by
  refine {
    shape := by norm_num [generalMeanSmallRow]
    third := by norm_num [generalMeanSmallRow]
    rate := by norm_num [generalMeanSmallRow]
    cutoff := by norm_num [generalMeanSmallRow]
    gap := by norm_num [generalMeanSmallRow]
    correction := by norm_num [generalMeanSmallRow]
    decay := by norm_num [generalMeanSmallRow]
    continuation := by norm_num [generalMeanSmallRow, GeneralMeanRow.cutoff]
    prefactorLog := roundedLogConditions (by norm_num [generalMeanSmallRow])
    prefactorExp := roundedExpConditions generalMeanSmallRow_prefactor_domain
    continuationLog := ?_
    nodeExp := ?_
    nodeContinuationExp := ?_
    nodeRound := fun _ => le_finalEntropyRoundQ _
    slopePositive := generalMeanSmallRow_slopePositive
    criticalLog := ?_
    criticalMargin := generalMeanSmallRow_criticalMargin
    finalLog := roundedLogConditions (by norm_num [generalMeanSmallRow])
    finalMargin := generalMeanSmallRow_finalMargin
  }
  · intro _
    exact roundedLogConditions (by norm_num [generalMeanSmallRow, GeneralMeanRow.cutoff])
  · intro j
    apply roundedExpConditions_nonpos
    have h := generalMeanGrid_pos j.val
    norm_num [generalMeanSmallRow]
    linarith
  · intro _ j
    apply roundedExpConditions_nonpos
    have h := generalMeanGrid_pos j.val
    norm_num [generalMeanSmallRow, GeneralMeanRow.cutoff]
    linarith
  · intro j
    apply roundedLogConditions
    exact mul_pos (by norm_num [generalMeanSmallRow]) (generalMeanCriticalPoint_pos _ _)

end SingularValueBounds.KL.Certificates
