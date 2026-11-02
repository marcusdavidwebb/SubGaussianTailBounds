import Mathlib.Data.Real.Sqrt

/-!
Exact recorded quartets for the canonical acceptance gate. Results.lean proves
the corresponding propositions and the equalities tying them to this snapshot;
these numerical definitions alone are not mathematical evidence.

After an improvement is accepted, the trusted base revision supplies the jointly
proved quartet for each regime. CI compiles this tiny source in isolation using
only its Mathlib imports. Declarative exact Lean expressions and local supporting
definitions are allowed. The trusted syntax guard rejects tactics, metaprogramming
and namespace escapes so future comparison ceilings remain stable. Keep proof
development in the proof modules; importing them here would break isolation.
-/

namespace SubGaussian.AcceptedConstants

noncomputable def generalAlpha : ℝ := 3.84
noncomputable def generalBeta : ℝ := 1.58
noncomputable def generalGamma : ℝ := 2.35
noncomputable def generalDelta : ℝ := 1.5

noncomputable def unitAlpha : ℝ := 1.32
noncomputable def unitBeta : ℝ := 1.12
noncomputable def unitGamma : ℝ := 2.32
noncomputable def unitDelta : ℝ := 1.42

end SubGaussian.AcceptedConstants
