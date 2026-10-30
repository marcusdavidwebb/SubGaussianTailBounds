import SingularValueBounds.KL.Certificates.ConcreteRounded

/-!
Uniform kernel proofs for the rounded logarithm algorithm on every positive
rational input. No input-specific numerical certificate remains in these lemmas.
-/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
lemma roundUpQ_lt_add (x : ℚ) : roundUpQ x < x + 1 / roundingScale := by
  rw [roundUpQ, div_lt_iff₀ roundingScale_pos]
  have h := Int.lt_floor_add_one (-(x*roundingScale))
  have hs : (1/roundingScale)*roundingScale = (1:ℚ) := by norm_num [roundingScale]
  nlinarith

lemma logUnitZ_nonneg {x : ℚ} (hx : 1 ≤ x) : 0 ≤ logUnitZ x := by
  unfold logUnitZ
  exact div_nonneg (sub_nonneg.mpr hx) (by linarith)

lemma logUnitZ_le_third {x : ℚ} (hx : 1 ≤ x) (h2 : x ≤ 2) : logUnitZ x ≤ 1/3 := by
  unfold logUnitZ
  rw [div_le_iff₀ (by linarith : (0:ℚ)<x+1)]
  linarith

lemma logUnitPowerLower_nonneg {x : ℚ} (hx : 1 ≤ x) (j : ℕ) :
    0 ≤ logUnitPowerLower x j := by
  have hz : 0 ≤ logUnitZLower x := roundDownQ_nonneg (logUnitZ_nonneg hx)
  have hs : 0 ≤ logUnitZ2Lower x := roundDownQ_nonneg (sq_nonneg _)
  induction j with
  | zero => exact hz
  | succ j ih => exact roundDownQ_nonneg (mul_nonneg ih hs)

lemma logUnitPowerUpper_nonneg {x : ℚ} (hx : 1 ≤ x) (j : ℕ) :
    0 ≤ logUnitPowerUpper x j := by
  have hz : 0 ≤ logUnitZUpper x := (logUnitZ_nonneg hx).trans (le_roundUpQ _)
  have hs : 0 ≤ logUnitZ2Upper x := (sq_nonneg _).trans (le_roundUpQ _)
  induction j with
  | zero => exact hz
  | succ j ih => exact (mul_nonneg ih hs).trans (le_roundUpQ _)

lemma logUnitZ2Lower_le {x : ℚ} (hx : 1 ≤ x) : logUnitZ2Lower x ≤ logUnitZ x ^ 2 := by
  have h := roundDownQ_le (logUnitZLower x ^ 2)
  have hz : logUnitZLower x ≤ logUnitZ x := roundDownQ_le _
  have hz0 : 0 ≤ logUnitZLower x := roundDownQ_nonneg (logUnitZ_nonneg hx)
  change roundDownQ (logUnitZLower x ^ 2) ≤ _
  exact h.trans (by nlinarith)

lemma logUnitZ2Upper_ge {x : ℚ} (hx : 1 ≤ x) : logUnitZ x ^ 2 ≤ logUnitZ2Upper x := by
  have h := le_roundUpQ (logUnitZUpper x ^ 2)
  have hz : logUnitZ x ≤ logUnitZUpper x := le_roundUpQ _
  have hz0 := logUnitZ_nonneg hx
  change _ ≤ roundUpQ (logUnitZUpper x ^ 2)
  exact le_trans (by nlinarith) h

lemma logUnitZ2Upper_lt_one {x : ℚ} (hx : 1 ≤ x) (h2 : x ≤ 2) :
    logUnitZ2Upper x < 1 := by
  have hu := roundUpQ_lt_add (logUnitZ x)
  have hz := logUnitZ_le_third hx h2
  have h0 : 0 ≤ logUnitZUpper x := (logUnitZ_nonneg hx).trans (le_roundUpQ _)
  have hhalf : logUnitZUpper x ≤ 1/2 := by
    dsimp [logUnitZUpper, roundingScale] at *
    linarith
  have hsq : logUnitZUpper x ^ 2 ≤ 1/4 := by nlinarith
  have h := roundUpQ_lt_add (logUnitZUpper x ^ 2)
  change roundUpQ (logUnitZUpper x ^ 2) < 1
  dsimp [roundingScale] at h
  linarith

/-- The logarithm transcript holds uniformly throughout the reduced interval. -/
theorem unitLogConditions {x : ℚ} (hx : 1 ≤ x) (h2 : x ≤ 2) : UnitLogConditions x := by
  refine ⟨by linarith, ?_⟩
  refine ⟨logUnitZ_nonneg hx, (logUnitZ_le_third hx h2).trans_lt (by norm_num),
    (fun j _ => logUnitPowerLower_nonneg hx j),
    (fun j _ => logUnitPowerUpper_nonneg hx j),
    roundDownQ_le _, le_roundUpQ _, ?_, ?_, ?_, ?_, le_rfl, ?_⟩
  · intro j _
    exact (roundDownQ_le _).trans
      (mul_le_mul_of_nonneg_left (logUnitZ2Lower_le hx) (logUnitPowerLower_nonneg hx j))
  · intro j _
    exact (mul_le_mul_of_nonneg_left (logUnitZ2Upper_ge hx)
      (logUnitPowerUpper_nonneg hx j)).trans (le_roundUpQ _)
  · intro j _
    exact roundDownQ_le _
  · intro j _
    exact le_roundUpQ _
  · apply add_le_add_left
    apply le_trans _ (le_roundUpQ _)
    norm_num only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd]
    apply div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (logUnitPowerUpper_nonneg hx 18))
    · exact mul_pos (by norm_num) (sub_pos.mpr (logUnitZ2Upper_lt_one hx h2))
    · exact mul_le_mul_of_nonneg_left (sub_le_sub_left (logUnitZ2Upper_ge hx) _) (by norm_num)

lemma reduceLogPowTwo_correct (fuel : ℕ) {x : ℚ} (hx : 1 ≤ x)
    (hbound : x < (2:ℚ)^(fuel+1)) :
    x = 2 ^ (reduceLogPowTwo fuel x).1 * (reduceLogPowTwo fuel x).2 ∧
      1 ≤ (reduceLogPowTwo fuel x).2 ∧ (reduceLogPowTwo fuel x).2 < 2 := by
  induction fuel generalizing x with
  | zero => simpa [reduceLogPowTwo] using (show x = x ∧ 1 ≤ x ∧ x < 2 from ⟨rfl, hx, by simpa using hbound⟩)
  | succ fuel ih =>
    by_cases htwo : 2 ≤ x
    · have hhalf : 1 ≤ x/2 := by linarith
      have hboundhalf : x/2 < (2:ℚ)^(fuel+1) := by
        rw [div_lt_iff₀ (by norm_num : (0:ℚ)<2)]
        simpa only [Nat.succ_add, pow_succ] using hbound
      obtain ⟨he, hlo, hhi⟩ := ih hhalf hboundhalf
      simp only [reduceLogPowTwo, if_pos htwo, pow_add, pow_one]
      refine ⟨?_, hlo, hhi⟩
      nlinarith [he]
    · simpa [reduceLogPowTwo, htwo] using (show x = x ∧ 1 ≤ x ∧ x < 2 from ⟨rfl, hx, lt_of_not_ge htwo⟩)

lemma rational_le_natAbs_num {x : ℚ} (hx : 0 ≤ x) : x ≤ x.num.natAbs := by
  have hnum : (0:ℚ) ≤ x.num := by exact_mod_cast Rat.num_nonneg.mpr hx
  have hden : (1:ℚ) ≤ x.den := by exact_mod_cast x.den_pos
  have hnat : (x.num:ℚ) ≤ x.num.natAbs := by
    rw [Int.cast_natAbs]
    exact_mod_cast (le_abs_self x.num)
  calc
    x = (x.num:ℚ)/x.den := (Rat.num_div_den x).symm
    _ ≤ (x.num:ℚ) := div_le_self hnum hden
    _ ≤ x.num.natAbs := hnat

/-- The finite power-of-two reduction always reaches its required domain. -/
theorem logReductionQ_correct {x : ℚ} (hx : 1 ≤ x) :
    x = 2^(logReductionQ x).1*(logReductionQ x).2 ∧
      1 ≤ (logReductionQ x).2 ∧ (logReductionQ x).2 < 2 := by
  apply reduceLogPowTwo_correct _ hx
  have hp : (x.num.natAbs:ℚ) < (2:ℚ)^(Nat.log 2 x.num.natAbs+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1<2) x.num.natAbs
  have hpow : (2:ℚ)^(Nat.log 2 x.num.natAbs+1) ≤ (2:ℚ)^(Nat.log 2 x.num.natAbs+1+1) := by
    simp only [pow_add, pow_one]
    nlinarith [pow_nonneg (by norm_num : (0:ℚ)≤2) (Nat.log 2 x.num.natAbs)]
  exact ((rational_le_natAbs_num (by linarith)).trans_lt hp).trans_le hpow

/-- The scaled logarithm conditions hold for every argument at least one. -/
theorem scaledLogConditions {x : ℚ} (hx : 1 ≤ x) : ScaledLogConditions x := by
  obtain ⟨he, hlo, hhi⟩ := logReductionQ_correct hx
  exact ⟨he, unitLogConditions hlo hhi.le, unitLogConditions (by norm_num) le_rfl⟩

/-- The complete rounded logarithm transcript holds for every positive rational. -/
theorem roundedLogConditions {x : ℚ} (hx : 0 < x) : RoundedLogConditions x := by
  refine ⟨hx, ?_⟩
  split_ifs with hone
  · apply scaledLogConditions
    exact (one_le_div hx).mpr hone.le
  · exact scaledLogConditions (le_of_not_gt hone)

end SingularValueBounds.KL.Certificates
