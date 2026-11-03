import SingularValueBounds.KL.Upper.GeneralMeanCells
import SingularValueBounds.KL.Certificates.GeneralMeanPrefactorLogs
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SingularValueBounds.KL.Certificates.SmallEntropyRow
open SingularValueBounds.KL.Certificates
private theorem prefactorValue : generalMeanSmallRow.prefactor = (3137646878119839/500000000000000:ℚ) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument, GeneralPrefactorLogs.lower_eq_cache]
  simp only [generalMeanExpUpperQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ (generalMeanSmallRow.cutoff/generalMeanSmallRow.c)).2 = (27678513458901/50000000000000:ℚ) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private noncomputable def nodes : Fin 3 → Fin 121 := ![0, 37, 120]
private noncomputable def values : Fin 3 → ℚ := ![(580087/1000000:ℚ), (218049/1000000:ℚ), (24581/500000:ℚ)]
private theorem nodeValues (j : Fin 3) :
    generalMeanSmallRow.error (generalMeanGrid (nodes j).val) = values j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  simp only [generalMeanExpUpperQ_eq_integer, resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem segmentConditions (i : Fin 2) :
    let j := (nodes ⟨i.val,by omega⟩).val
    let k := (nodes ⟨i.val+1,by omega⟩).val
    0 < generalMeanSmallRow.criticalRate j k ∧
    0 ≤ 2+generalMeanSmallRow.criticalRate j k*generalMeanSmallRow.criticalPoint j k-
      (logRoundedQ (generalMeanSmallRow.c*generalMeanSmallRow.criticalPoint j k)).2-generalMeanSmallRow.J/2-
      generalMeanSmallRow.error (generalMeanGrid j)+generalMeanSmallRow.slope j k*generalMeanGrid j := by
  dsimp only
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope, nodeValues]
  revert i
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*generalMeanSmallRow.c)).2-generalMeanSmallRow.J/2-generalMeanSmallRow.error 4 := by
  have he : generalMeanSmallRow.error 4 = (24581/500000:ℚ) := by
    have hn := nodeValues (2 : Fin 3)
    have hi : (nodes (2 : Fin 3)).val = 120 := by decide +kernel
    have hv : values (2 : Fin 3) = (24581/500000:ℚ) := by decide +kernel
    rw [hi, hv, generalMeanGrid_last] at hn
    exact hn
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions generalMeanSmallRow := by
  apply generalMeanNumericalConditions_of_margins _ (by unfold GeneralMeanBasicDomains; decide +kernel)
    (by decide +kernel) [(0,37), (37,120)]
  · simp only [GeneralMeanPartition]
    decide +kernel
  · simp only [List.forall_mem_cons]
    exact ⟨(segmentConditions 0).1, ⟨(segmentConditions 1).1, List.forall_mem_nil _⟩⟩
  · simp only [List.forall_mem_cons]
    exact ⟨(segmentConditions 0).2, ⟨(segmentConditions 1).2, List.forall_mem_nil _⟩⟩
  · exact finalMargin
end SingularValueBounds.KL.Certificates.SmallEntropyRow

namespace SingularValueBounds.KL.Certificates
theorem generalMeanSmallRow_numerical : GeneralMeanNumericalConditions generalMeanSmallRow :=
  SmallEntropyRow.numerical
end SingularValueBounds.KL.Certificates
