import SingularValueBounds.KL.Certificates.IntegerFixedPoint

/-! Exact integer evaluation of the existing fixed-point exponential algorithm.
Every recurrence and sum is proved equal to its rational specification in Lean. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def expIntegerStep (upper : Bool) (b : ℤ) (j : ℕ) (term : ℤ) : ℤ :=
  if upper then -((-term*b)/(fixedScaleNat*(j+1):ℕ))
    else term*b/(fixedScaleNat*(j+1):ℕ)

def expIntegerTerm (upper : Bool) (b : ℤ) : ℕ → ℤ
  | 0 => fixedScaleNat
  | j+1 => expIntegerStep upper b j (expIntegerTerm upper b j)

def expIntegerFold (upper : Bool) (b : ℤ) : ℕ → ℕ → ℤ → ℤ → ℤ × ℤ
  | 0, _, term, total => (term, total)
  | steps+1, j, term, total =>
    let next := expIntegerStep upper b j term
    expIntegerFold upper b steps (j+1) next (total+next)

private theorem expIntegerFold_correct (upper : Bool) (b : ℤ) (n j : ℕ) :
    expIntegerFold upper b n j (expIntegerTerm upper b j)
      (∑ i ∈ Finset.range (j+1), expIntegerTerm upper b i) =
      (expIntegerTerm upper b (j+n),
        ∑ i ∈ Finset.range (j+n+1), expIntegerTerm upper b i) := by
  induction n generalizing j with
  | zero => simp [expIntegerFold]
  | succ n ih =>
    simp only [expIntegerFold]
    rw [show expIntegerStep upper b j (expIntegerTerm upper b j) =
      expIntegerTerm upper b (j+1) from rfl]
    have hs : (∑ i ∈ Finset.range (j+1), expIntegerTerm upper b i) +
        expIntegerTerm upper b (j+1) =
        ∑ i ∈ Finset.range (j+1+1), expIntegerTerm upper b i :=
      (Finset.sum_range_succ _ _).symm
    rw [hs, ih]
    rw [show j+1+n = j+(n+1) by omega]

theorem expTermLowerQ_fixedQ (b : ℤ) (j : ℕ) :
    expTermLowerQ (fixedQ b) j = fixedQ (expIntegerTerm false b j) := by
  induction j with
  | zero => norm_num [expTermLowerQ, expIntegerTerm, fixedQ, fixedScaleNat, roundingScale]
  | succ j ih =>
    rw [expTermLowerQ, ih]
    simpa [expIntegerTerm, expIntegerStep] using
      roundDownQ_fixed_mul_div (expIntegerTerm false b j) b (j+1)

theorem expTermUpperQ_fixedQ (b : ℤ) (j : ℕ) :
    expTermUpperQ (fixedQ b) j = fixedQ (expIntegerTerm true b j) := by
  induction j with
  | zero => norm_num [expTermUpperQ, expIntegerTerm, fixedQ, fixedScaleNat, roundingScale]
  | succ j ih =>
    rw [expTermUpperQ, ih]
    simpa [expIntegerTerm, expIntegerStep] using
      roundUpQ_fixed_mul_div (expIntegerTerm true b j) b (j+1)

private theorem fixedQ_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, fixedQ (f i)) = fixedQ (∑ i ∈ s, f i) := by
  simp [fixedQ, Finset.sum_div, Int.cast_sum]

theorem expLowerSumQ_fixedQ (b : ℤ) :
    expLowerSumQ (fixedQ b) = fixedQ (expIntegerFold false b 80 0 fixedScaleNat fixedScaleNat).2 := by
  have h := congrArg Prod.snd (expIntegerFold_correct false b 80 0)
  simp only [Finset.sum_range_one, Nat.zero_add, Prod.snd] at h
  have hz : expIntegerTerm false b 0 = fixedScaleNat := rfl
  rw [hz] at h
  unfold expLowerSumQ
  simp_rw [expTermLowerQ_fixedQ]
  rw [fixedQ_sum, h]

theorem expPositiveUpperQ_fixedQ (b : ℤ) :
    expPositiveUpperQ (fixedQ b) =
      let p := expIntegerFold true b 80 0 fixedScaleNat fixedScaleNat
      fixedQ p.2 + roundUpQ (roundUpQ (fixedQ p.1*fixedQ b/81)/(1-fixedQ b/82)) := by
  have h := expIntegerFold_correct true b 80 0
  simp only [Finset.sum_range_one, Nat.zero_add] at h
  have hz : expIntegerTerm true b 0 = fixedScaleNat := rfl
  rw [hz] at h
  rw [h]
  unfold expPositiveUpperQ
  simp_rw [expTermUpperQ_fixedQ]
  rw [fixedQ_sum]

private theorem fixedQ_neg (n : ℤ) : fixedQ (-n) = -fixedQ n := by
  simp [fixedQ, neg_div]

private theorem roundUpQ_eq_fixedQ (x : ℚ) :
    roundUpQ x = fixedQ (-⌊-(x*roundingScale)⌋) := by
  simp [roundUpQ, fixedQ]

def integerExpUpper (x : ℚ) : ℚ :=
  let b : ℤ := -⌊-(x*roundingScale)⌋
  if fixedQ b < 0 then
    roundUpQ (1 / fixedQ (expIntegerFold false (-b) 80 0 fixedScaleNat fixedScaleNat).2)
  else
    let p := expIntegerFold true b 80 0 fixedScaleNat fixedScaleNat
    fixedQ p.2 + roundUpQ (roundUpQ (fixedQ p.1*fixedQ b/81)/(1-fixedQ b/82))

/-- Exact integer evaluation of the original rounded exponential algorithm. -/
theorem expUpperRoundedQ_eq_integer (x : ℚ) :
    expUpperRoundedQ x = integerExpUpper x := by
  unfold expUpperRoundedQ integerExpUpper
  rw [roundUpQ_eq_fixedQ]
  dsimp only
  split_ifs
  · rw [← fixedQ_neg, expLowerSumQ_fixedQ]
  · rw [expPositiveUpperQ_fixedQ]

end SingularValueBounds.KL.Certificates
