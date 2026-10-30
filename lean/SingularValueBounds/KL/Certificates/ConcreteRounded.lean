import SingularValueBounds.KL.Upper.EndpointRoundedEval

/-!
Kernel proofs of the fixed-point exponential and endpoint decay conditions.
The recurrence inequalities hold uniformly and require no finite transcript oracle.
The positive exponential branch retains only its mathematical Taylor-domain bound.
-/

open scoped BigOperators
namespace SingularValueBounds.KL.Certificates

lemma roundingScale_pos : 0 < roundingScale := by norm_num [roundingScale]

lemma roundDownQ_le (x : ℚ) : roundDownQ x ≤ x := by
  rw [roundDownQ, div_le_iff₀ roundingScale_pos]
  exact Int.floor_le _

lemma le_roundUpQ (x : ℚ) : x ≤ roundUpQ x := by
  rw [roundUpQ, le_div_iff₀ roundingScale_pos]
  have h := Int.floor_le (-(x*roundingScale))
  linarith

lemma roundDownQ_nonneg {x : ℚ} (hx : 0 ≤ x) : 0 ≤ roundDownQ x := by
  unfold roundDownQ
  apply div_nonneg _ roundingScale_pos.le
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hx roundingScale_pos.le)

lemma roundUpQ_nonpos {x : ℚ} (hx : x ≤ 0) : roundUpQ x ≤ 0 := by
  unfold roundUpQ
  apply div_nonpos_of_nonpos_of_nonneg _ roundingScale_pos.le
  have h : (0:ℚ) ≤ (⌊-(x*roundingScale)⌋ : ℤ) := by
    exact_mod_cast Int.floor_nonneg.mpr (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hx roundingScale_pos.le))
  linarith

lemma expTermLowerQ_nonneg {x : ℚ} (hx : 0 ≤ x) (j : ℕ) : 0 ≤ expTermLowerQ x j := by
  induction j with
  | zero => norm_num [expTermLowerQ]
  | succ j ih =>
    exact roundDownQ_nonneg (div_nonneg (mul_nonneg ih hx) (by positivity))

lemma expLowerSumQ_pos {x : ℚ} (hx : 0 ≤ x) : 0 < expLowerSumQ x := by
  have h : (1 : ℚ) ≤ expLowerSumQ x := by
    simpa only [expTermLowerQ] using
      (Finset.single_le_sum (fun j _ => expTermLowerQ_nonneg hx j)
        (show 0 ∈ Finset.range 81 by decide))
  exact lt_of_lt_of_le (by norm_num) h

theorem expLowerTranscript (x : ℚ) (hx : 0 ≤ x) :
    ExpLowerTranscript 80 x (expLowerSumQ x) (expTermLowerQ x) := by
  refine ⟨hx, by simp [expTermLowerQ], ?_, le_rfl⟩
  intro j _
  exact roundDownQ_le _

theorem expUpperTranscript (x : ℚ) (hx : 0 ≤ x) (hdom : x < 82) :
    ExpUpperTranscript 80 x (expPositiveUpperQ x) (expTermUpperQ x) := by
  refine ⟨hx, by norm_num; exact hdom, by simp [expTermUpperQ], ?_, ?_⟩
  · intro j _
    exact le_roundUpQ _
  · apply add_le_add_left
    apply le_trans _ (le_roundUpQ _)
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    apply div_le_div_of_nonneg_right (le_roundUpQ _)
    exact sub_nonneg.mpr ((div_le_one (by norm_num : (0:ℚ)<82)).mpr hdom.le)

/-- The rounded exponential transcript is proved uniformly on its exact domain. -/
theorem roundedExpConditions {x : ℚ} (hdom : roundUpQ x < 82) :
    RoundedExpConditions x := by
  refine ⟨le_roundUpQ x, ?_⟩
  split_ifs with hx
  · exact ⟨expLowerTranscript _ (neg_nonneg.mpr hx.le),
      expLowerSumQ_pos (neg_nonneg.mpr hx.le), le_roundUpQ _⟩
  · exact expUpperTranscript _ (le_of_not_gt hx) hdom

/-- Every nonpositive input has a fully proved rounded exponential transcript. -/
theorem roundedExpConditions_nonpos {x : ℚ} (hx : x ≤ 0) :
    RoundedExpConditions x :=
  roundedExpConditions ((roundUpQ_nonpos hx).trans_lt (by norm_num))

/-- The entire decay family follows from the rounding recurrences, for every index. -/
theorem endpointDecayConditions (qi : ℕ) : EndpointDecayConditions qi := by
  refine ⟨roundDownQ_le _, roundedExpConditions_nonpos ?_, ?_⟩
  · exact neg_nonpos.mpr (roundDownQ_nonneg (by positivity))
  · intro j _
    exact le_roundUpQ _

end SingularValueBounds.KL.Certificates
