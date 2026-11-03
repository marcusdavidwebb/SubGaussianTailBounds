import SingularValueBounds.KL.Certificates.IntegerFixedPoint
import Mathlib.Algebra.BigOperators.Field

/-! Exact integer evaluation of fixed-point Taylor terms and arbitrary finite
sums. Saturated tails avoid redundant arithmetic; Lean proves each recurrence
and finite sum equal to its rational definition. -/
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
These exact tails apply to every finite Taylor order. -/
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

/-- Evaluate any finite lower Taylor sum with the shared integer recurrence. -/
theorem expLowerSum_fixedQ_order (N : ℕ) (b : ℤ) :
    (∑ j ∈ Finset.range (N+1), expTermLowerQ (fixedQ b) j) =
      fixedQ (expIntegerFold false b N 0 fixedScaleNat fixedScaleNat).2 := by
  have h := congrArg Prod.snd (expIntegerFold_correct false b N 0)
  simp only [Finset.sum_range_one, Nat.zero_add] at h
  change (expIntegerFold false b N 0 fixedScaleNat fixedScaleNat).2 = _ at h
  simp_rw [expTermLowerQ_fixedQ]
  rw [fixedQ_sum, h]

/-- Evaluate any finite upper Taylor sum with the shared integer recurrence. -/
theorem expUpperSum_fixedQ_order (N : ℕ) (b : ℤ) :
    (∑ j ∈ Finset.range (N+1), expTermUpperQ (fixedQ b) j) =
      fixedQ (expIntegerFold true b N 0 fixedScaleNat fixedScaleNat).2 := by
  have h := congrArg Prod.snd (expIntegerFold_correct true b N 0)
  simp only [Finset.sum_range_one, Nat.zero_add] at h
  change (expIntegerFold true b N 0 fixedScaleNat fixedScaleNat).2 = _ at h
  simp_rw [expTermUpperQ_fixedQ]
  rw [fixedQ_sum, h]

end SingularValueBounds.KL.Certificates
