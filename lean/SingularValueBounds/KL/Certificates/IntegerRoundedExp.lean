import SingularValueBounds.KL.Certificates.IntegerFixedPoint
import Mathlib.Algebra.BigOperators.Field

/-! Exact integer evaluation of the existing fixed-point exponential algorithm.
Zero/one tails and integer remainders avoid redundant arithmetic. Every step
is proved equal to the original rational specification in Lean. -/
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

/-- Once a rounded exponential term is zero it stays zero. A positive upper
term equal to one also stays one once its next denominator dominates the input.
These exact tails preserve the original eighty-term rounding algorithm. -/
private lemma expIntegerStep_one (b : ℤ) (j : ℕ)
    (hb : 0 < b) (hsmall : b ≤ (fixedScaleNat * (j + 1) : ℕ)) :
    expIntegerStep true b j 1 = 1 := by
  simp only [expIntegerStep, ↓reduceIte, neg_one_mul]
  rw [Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by simpa using hsmall)]
  rfl

private lemma expIntegerFold_zero (upper : Bool) (b : ℤ) (n j : ℕ) (total : ℤ) :
    expIntegerFold upper b n j 0 total = (0, total) := by
  induction n generalizing j total with
  | zero => rfl
  | succ n ih =>
    simp only [expIntegerFold, expIntegerStep, zero_mul, neg_zero, Int.zero_ediv,
      ite_self, add_zero]
    exact ih _ _

private lemma expIntegerFold_one (b : ℤ) (n j : ℕ) (total : ℤ)
    (hb : 0 < b) (hsmall : b ≤ (fixedScaleNat * (j + 1) : ℕ)) :
    expIntegerFold true b n j 1 total = (1, total + n) := by
  induction n generalizing j total with
  | zero => simp only [expIntegerFold, Nat.cast_zero, add_zero]
  | succ n ih =>
    rw [expIntegerFold, expIntegerStep_one b j hb hsmall, ih]
    · simp only [Nat.cast_add, Nat.cast_one]
      congr 1
      omega
    · exact hsmall.trans (by
        exact_mod_cast Nat.mul_le_mul_left fixedScaleNat (show j + 1 ≤ j + 1 + 1 by omega))

private def expIntegerStepNatural (upper : Bool) (b : ℤ) (j : ℕ) (term : ℤ) : ℤ :=
  match b, term with
  | .ofNat b, .ofNat term =>
    if upper then
      match term*b with
      | 0 => 0
      | n+1 => ((n/(fixedScaleNat*(j+1))+1 : ℕ) : ℤ)
    else ((term*b/(fixedScaleNat*(j+1)) : ℕ) : ℤ)
  | b, term => expIntegerStep upper b j term

private theorem expIntegerStepNatural_eq (upper : Bool) (b : ℤ) (j : ℕ) (term : ℤ) :
    expIntegerStepNatural upper b j term = expIntegerStep upper b j term := by
  cases b with
  | ofNat b =>
    cases term with
    | ofNat term =>
      cases upper with
      | false => rfl
      | true =>
        have h := natCeil_cast_eq_neg_ediv (term*b) (fixedScaleNat*(j+1))
          (Nat.mul_pos (by decide) (Nat.succ_pos j))
        cases hprod : term*b <;>
          simpa only [expIntegerStepNatural, expIntegerStep, ↓reduceIte, hprod,
          Int.ofNat_eq_natCast, ←Nat.cast_mul, Int.neg_mul] using h
    | negSucc term => rfl
  | negSucc b => rfl

def expIntegerFoldSaturated (upper : Bool) (b : ℤ) : ℕ → ℕ → ℤ → ℤ → ℤ × ℤ
  | 0, _, term, total => (term, total)
  | n + 1, j, term, total =>
    if term = 0 then (0, total)
    else if upper = true ∧ term = 1 ∧ 0 < b ∧ b ≤ (fixedScaleNat * (j + 1) : ℕ) then
      (1, total + (n + 1 : ℕ))
    else
      let next := expIntegerStepNatural upper b j term
      expIntegerFoldSaturated upper b n (j+1) next (total+next)

theorem expIntegerFoldSaturated_eq (upper : Bool) (b : ℤ) (n j : ℕ) (term total : ℤ) :
    expIntegerFoldSaturated upper b n j term total = expIntegerFold upper b n j term total := by
  induction n generalizing j term total with
  | zero => rfl
  | succ n ih =>
    simp only [expIntegerFoldSaturated]
    split_ifs with hz hs
    · rw [hz, expIntegerFold_zero]
    · rcases hs with ⟨rfl, rfl, hb, hsmall⟩
      exact (expIntegerFold_one b (n + 1) j total hb hsmall).symm
    · rw [expIntegerStepNatural_eq, expIntegerFold, ih]

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

private def expCeilDiv (n d : ℤ) : ℤ := -((-n)/d)

private lemma roundUpQ_int_div (n d : ℤ) (hd : 0 < d) :
    roundUpQ ((n : ℚ)/d) = fixedQ (expCeilDiv (n*fixedScaleNat) d) := by
  have hdn : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
  have hdq : (d.toNat : ℚ) = (d : ℚ) := by exact_mod_cast hdn
  unfold roundUpQ fixedQ expCeilDiv
  have he : -((n : ℚ)/d*roundingScale) =
      ((-(n*(fixedScaleNat : ℤ)) : ℤ) : ℚ)/(d.toNat : ℚ) := by
    rw [hdq]
    simp only [Int.cast_neg, Int.cast_mul, Int.cast_natCast, roundingScale, fixedScaleNat]
    ring
  rw [he, Rat.floor_intCast_div_natCast, hdn]
  simp only [Int.cast_neg]

private lemma roundUpQ_inv_fixed (n : ℤ) (hn : 0 < n) :
    roundUpQ (1/fixedQ n) = fixedQ (expCeilDiv (fixedScaleNat^2) n) := by
  have he : 1/fixedQ n = ((fixedScaleNat : ℤ) : ℚ)/(n : ℚ) := by
    simp [fixedQ, roundingScale, fixedScaleNat, one_div]
  rw [he, roundUpQ_int_div _ n hn]
  congr 2

private lemma roundUpQ_exp_remainder (term b : ℤ)
    (hb : b < 82*(fixedScaleNat : ℤ)) :
    roundUpQ (roundUpQ (fixedQ term*fixedQ b/81)/(1-fixedQ b/82)) =
      fixedQ (expCeilDiv
        (expCeilDiv (term*b) (fixedScaleNat*81)*82*fixedScaleNat)
        (82*fixedScaleNat-b)) := by
  have hi := roundUpQ_fixed_mul_div term b 81
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hi
  rw [hi]
  let t : ℤ := expCeilDiv (term*b) (fixedScaleNat*81)
  change roundUpQ (fixedQ t/(1-fixedQ b/82)) = _
  have hd : 0 < 82*(fixedScaleNat : ℤ)-b := by omega
  have hden : 1-fixedQ b/82 =
      ((82*(fixedScaleNat : ℤ)-b : ℤ) : ℚ)/(82*roundingScale) := by
    norm_num [fixedQ, roundingScale, fixedScaleNat] ; ring
  have he : fixedQ t/(1-fixedQ b/82) =
      ((t*82 : ℤ) : ℚ)/((82*(fixedScaleNat : ℤ)-b : ℤ) : ℚ) := by
    rw [hden, div_div_eq_mul_div]
    congr 1
    norm_num [fixedQ, roundingScale, fixedScaleNat] ; ring

  rw [he, roundUpQ_int_div _ _ hd]


/-- Rational reference form used only to prove exact evaluator equivalence. -/
private def integerExpUpperReference (x : ℚ) : ℚ :=
  let b : ℤ := -⌊-(x*roundingScale)⌋
  if fixedQ b < 0 then
    roundUpQ (1 / fixedQ (expIntegerFoldSaturated false (-b) 80 0 fixedScaleNat fixedScaleNat).2)
  else
    let p := expIntegerFoldSaturated true b 80 0 fixedScaleNat fixedScaleNat
    fixedQ p.2 + roundUpQ (roundUpQ (fixedQ p.1*fixedQ b/81)/(1-fixedQ b/82))


def integerExpUpper (x : ℚ) : ℚ :=
  let b : ℤ := -⌊-(x*roundingScale)⌋
  if fixedQ b < 0 then
    let total := (expIntegerFoldSaturated false (-b) 80 0 fixedScaleNat fixedScaleNat).2
    if 0 < total then fixedQ (expCeilDiv (fixedScaleNat^2) total)
    else roundUpQ (1/fixedQ total)
  else
    let p := expIntegerFoldSaturated true b 80 0 fixedScaleNat fixedScaleNat
    if b < 82*fixedScaleNat then
      fixedQ (p.2+expCeilDiv
        (expCeilDiv (p.1*b) (fixedScaleNat*81)*82*fixedScaleNat)
        (82*fixedScaleNat-b))
    else fixedQ p.2+roundUpQ (roundUpQ (fixedQ p.1*fixedQ b/81)/(1-fixedQ b/82))

private theorem integerExpUpperReference_eq (x : ℚ) : integerExpUpperReference x = integerExpUpper x := by
  unfold integerExpUpperReference integerExpUpper
  dsimp only
  split_ifs with hneg htotal hpos
  · exact roundUpQ_inv_fixed _ htotal
  · rfl
  · rw [roundUpQ_exp_remainder _ _ hpos, fixedQ_add]
  · rfl

/-- Exact integer evaluation of the original rounded exponential algorithm. -/
theorem expUpperRoundedQ_eq_integer (x : ℚ) :
    expUpperRoundedQ x = integerExpUpper x := by
  rw [← integerExpUpperReference_eq]
  unfold expUpperRoundedQ integerExpUpperReference
  simp only [expIntegerFoldSaturated_eq]
  rw [roundUpQ_eq_fixedQ]
  split_ifs
  · rw [← fixedQ_neg, expLowerSumQ_fixedQ]
  · rw [expPositiveUpperQ_fixedQ]

end SingularValueBounds.KL.Certificates
