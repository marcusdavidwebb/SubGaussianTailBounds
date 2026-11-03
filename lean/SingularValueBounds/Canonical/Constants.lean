import Mathlib.Data.Real.Basic

/-! The two published quartets, as exact rationals. Documentation and the
verification specification read these values; numerical proof witnesses may use
other exact internal constants. -/
namespace SubGaussian.Constants

noncomputable abbrev generalAlpha : ℝ := 3.84
noncomputable abbrev generalBeta : ℝ := 1.58
noncomputable abbrev generalGamma : ℝ := 2.35
noncomputable abbrev generalDelta : ℝ := 1.50

noncomputable abbrev unitAlpha : ℝ := 1.32
noncomputable abbrev unitBeta : ℝ := 1.12
noncomputable abbrev unitGamma : ℝ := 2.32
noncomputable abbrev unitDelta : ℝ := 1.42

end SubGaussian.Constants
