import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanSmall

/-! Uniform assembly of finite general upper-mean scalar margins and rounded transcripts. -/
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0

/-- The inexpensive scalar domains needed by every numerical row. -/
def GeneralMeanBasicDomains (r : GeneralMeanRow) : Prop :=
  0 < r.khi ∧ 0 ≤ r.ahi ∧ 0 < r.q ∧ 0 < r.c ∧ r.q*r.khi^2 < 1 ∧
  0 ≤ r.C ∧ 2 < r.q*r.c/2 ∧
  (1 < r.q → r.c ≤ r.cutoff ∧ 2 < r.q*r.cutoff/2)

theorem generalMeanNumericalConditions_of_margins (r : GeneralMeanRow)
    (hb : GeneralMeanBasicDomains r)
    (hp : roundUpQ r.prefactorArgument < 82)
    (hs : ∀ j : Fin 120, 0 < r.criticalRate j.val)
    (hc : ∀ j : Fin 120,
      0 ≤ 2+r.criticalRate j.val*r.criticalPoint j.val-
        (logRoundedQ (r.c*r.criticalPoint j.val)).2-r.J/2-
        r.error (generalMeanGrid j.val)+r.slope j.val*generalMeanGrid j.val)
    (hf : 0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*r.c)).2-r.J/2-r.error 4) :
    GeneralMeanNumericalConditions r := by
  rcases hb with ⟨hk,ha,hq,hc0,hgap,hC,hdec,hcont⟩
  refine {
    shape := hk, third := ha, rate := hq, cutoff := hc0,
    gap := hgap, correction := hC, decay := hdec, continuation := hcont,
    prefactorLog := roundedLogConditions (by linarith),
    prefactorExp := roundedExpConditions hp,
    continuationLog := ?_, nodeExp := ?_, nodeContinuationExp := ?_,
    nodeRound := fun _ => le_finalEntropyRoundQ _,
    slopePositive := hs, criticalLog := ?_, criticalMargin := hc,
    finalLog := roundedLogConditions (mul_pos (by norm_num) hc0), finalMargin := hf
  }
  · intro hq1
    apply roundedLogConditions
    exact div_pos (hc0.trans_le (hcont hq1).1) hc0
  · intro j
    apply roundedExpConditions_nonpos
    have hn := mul_nonneg (sub_nonneg.mpr hdec.le) (generalMeanGrid_pos j.val).le
    linarith
  · intro hq1 j
    apply roundedExpConditions_nonpos
    have hn := mul_nonneg (sub_nonneg.mpr (hcont hq1).2.le) (generalMeanGrid_pos j.val).le
    linarith
  · intro j
    exact roundedLogConditions (mul_pos hc0 (generalMeanCriticalPoint_pos r j.val))

theorem generalMeanRows_basicDomains (i : Fin 1330) : GeneralMeanBasicDomains (generalMeanRows i) := by
  unfold GeneralMeanBasicDomains
  revert i
  decide +kernel

end SingularValueBounds.KL.Certificates
