import SingularValueBounds.KL.Certificates.IntegerRoundedLogEvaluation
import Mathlib.Tactic.SplitIfs

/-! Checked shared rounded logarithms.

A lookup contains proposed exact values, each certified against the unchanged
rounded logarithm. Missing arguments use its exact evaluator. Consequently the
lookup is only a proof-evaluation optimization and imposes no domain assumption.
-/
namespace SingularValueBounds.KL.Certificates

inductive RoundedLogCache where
  | empty
  | node (argument : ℚ) (numerator : ℤ) (left right : RoundedLogCache)

/-- Select either endpoint of the original integer logarithm evaluator. -/
noncomputable def integerLogComponent (upper : Bool) (x : ℚ) : ℚ :=
  if upper then (integerLogRounded x).2 else (integerLogRounded x).1

/-- Binary search with the original exact evaluator as its fallback. -/
noncomputable def RoundedLogCache.get : RoundedLogCache → Bool → ℚ → ℚ
  | .empty, upper, x => integerLogComponent upper x
  | .node argument numerator left right, upper, x =>
      if x < argument then left.get upper x
      else if x = argument then fixedQ numerator else right.get upper x

/-- Every proposed value, including every subtree, is checked in Lean. -/
noncomputable def RoundedLogCache.valid : RoundedLogCache → Bool → Bool
  | .empty, _ => true
  | .node argument numerator left right, upper =>
      decide (integerLogComponent upper argument = fixedQ numerator) &&
        (left.valid upper && right.valid upper)

theorem RoundedLogCache.get_eq (cache : RoundedLogCache) (upper : Bool)
    (h : cache.valid upper = true) (x : ℚ) :
    cache.get upper x = integerLogComponent upper x := by
  induction cache with
  | empty => rfl
  | node argument numerator left right ihl ihr =>
    have hs : integerLogComponent upper argument = fixedQ numerator ∧
        left.valid upper = true ∧ right.valid upper = true := by
      simpa only [valid, Bool.and_eq_true, decide_eq_true_eq] using h
    simp only [get]
    split_ifs with hl he
    · exact ihl hs.2.1
    · subst x
      exact hs.1.symm
    · exact ihr hs.2.2

theorem RoundedLogCache.node_valid (upper : Bool) (argument : ℚ) (numerator : ℤ)
    (left right : RoundedLogCache)
    (hvalue : integerLogComponent upper argument = fixedQ numerator)
    (hl : left.valid upper = true) (hr : right.valid upper = true) :
    (RoundedLogCache.node argument numerator left right).valid upper = true := by
  simp only [valid, hvalue, decide_true, hl, hr, Bool.and_self]

theorem integerLog_upper_eq_cache (cache : RoundedLogCache)
    (h : cache.valid true = true) (x : ℚ) : (integerLogRounded x).2 = cache.get true x := by
  simpa only [integerLogComponent, ↓reduceIte] using
    (cache.get_eq true h x).symm

theorem integerLog_lower_eq_cache (cache : RoundedLogCache)
    (h : cache.valid false = true) (x : ℚ) : (integerLogRounded x).1 = cache.get false x := by
  simpa only [integerLogComponent, Bool.false_eq_true, ↓reduceIte] using
    (cache.get_eq false h x).symm

/-- Rewrite only the upper endpoint; all original rounding steps are retained. -/
theorem roundedLog_upper_eq_cache (cache : RoundedLogCache)
    (h : cache.valid true = true) (x : ℚ) : (logRoundedQ x).2 = cache.get true x := by
  rw [logRoundedQ_eq_integer, integerLog_upper_eq_cache cache h]

end SingularValueBounds.KL.Certificates
