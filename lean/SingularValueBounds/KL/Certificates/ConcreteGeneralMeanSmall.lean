import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo
import SingularValueBounds.KL.Certificates.IntegerRoundedLogEvaluation
import SingularValueBounds.KL.Upper.GeneralMeanCells
import SingularValueBounds.KL.Certificates.ConcreteLog

/-!
Concrete numerical conditions for the general upper-mean small spectral range.
Rounded-function transcripts follow from the uniform Lean soundness lemmas;
the rounded node values are checked once with verified integer evaluators,
then reused in the finite rational margins checked by Lean's kernel.
-/
namespace SingularValueBounds.KL.Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

/-- Exact rounded node values are checked once and reused by the margin proofs. -/
private def smallErrorNumerators : Fin 121 → ℤ :=
  ![5800864306, 5603462040, 5416261907, 5238584536, 5069803203, 4909339139, 4756657331, 4611262745, 4472696937, 4340534991, 4214382753, 4093874325, 3978669796, 3868453174, 3762930507, 3661828169, 3564891300, 3471882371, 3382579879, 3296777146, 3214281222, 3134911873, 3058500652, 2984890050, 2913932704, 2845490677, 2779434786, 2715643992, 2654004821, 2594410846, 2536762197, 2480965110, 2426931513, 2374578635, 2323828654, 2274608359, 2226848848, 2180485237, 2135456397, 2091704708, 2049175829, 2007818484, 1967584266, 1928427451, 1890304826, 1853175532, 1817000911, 1781744371, 1747371256, 1713848721, 1681145628, 1649232435, 1618081098, 1587664983, 1557958780, 1528938420, 1500581006, 1472864739, 1445768854, 1419273561, 1393359988, 1368010124, 1343206774, 1318933510, 1295174629, 1271915110, 1249140576, 1226837261, 1204991974, 1183592067, 1162625406, 1142080346, 1121945699, 1102210718, 1082865065, 1063898797, 1045302340, 1027066474, 1009182315, 991641295, 974435150, 957555900, 940995843, 924747534, 908803776, 893157611, 877802302, 862731330, 847938380, 833417332, 819162254, 805167392, 791427164, 777936150, 764689090, 751680870, 738906523, 726361219, 714040261, 701939079, 690053225, 678378370, 666910295, 655644893, 644578161, 633706194, 623025189, 612531434, 602221307, 592091275, 582137888, 572357779, 562747658, 553304313, 544024604, 534905463, 525943892, 517136958, 508481796, 499975601, 491615631]

private def smallErrorValues (j : Fin 121) : ℚ := (smallErrorNumerators j : ℚ)/10000000000

private theorem smallPrefactorValue : generalMeanSmallRow.prefactor = (3137646878119867/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem smallCutoffLogValue : (logRoundedQ (generalMeanSmallRow.cutoff/generalMeanSmallRow.c)).2 = (27678513458901/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem smallErrorValue (j : ℕ) (hj : j < 121) :
    generalMeanSmallRow.error (generalMeanGrid j) = smallErrorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, generalMeanSmallRow.error (generalMeanGrid j.val) = smallErrorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, smallPrefactorValue, smallCutoffLogValue]
    simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

theorem generalMeanSmallRow_prefactor_domain :
    roundUpQ generalMeanSmallRow.prefactorArgument < 82 := by
  decide +kernel

theorem generalMeanSmallRow_slopePositive (j : Fin 120) :
    0 < generalMeanSmallRow.criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [smallErrorValue j.val (by omega), smallErrorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

theorem generalMeanSmallRow_criticalMargin (j : Fin 120) :
    0 ≤ 2 + generalMeanSmallRow.criticalRate j.val * generalMeanSmallRow.criticalPoint j.val -
      (logRoundedQ (generalMeanSmallRow.c * generalMeanSmallRow.criticalPoint j.val)).2 -
      generalMeanSmallRow.J / 2 - generalMeanSmallRow.error (generalMeanGrid j.val) +
      generalMeanSmallRow.slope j.val * generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [smallErrorValue j.val (by omega), smallErrorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem generalMeanSmallRow_finalMargin :
    0 ≤ 2 + 4 * (47 / 20 - 2) - (logRoundedQ (4 * generalMeanSmallRow.c)).2 -
      generalMeanSmallRow.J / 2 - generalMeanSmallRow.error 4 := by
  have he : generalMeanSmallRow.error 4 = smallErrorValues 120 := by
    convert! smallErrorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
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
