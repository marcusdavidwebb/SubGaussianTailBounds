import MainTheoremStatement

/-!
# Equivalent probability-tail formulations

Under a probability measure every event has finite measure, so taking `toReal`
preserves its comparison with a nonnegative real bound. This equivalence does
not require the event to be measurable and introduces no separate finiteness
assumption.
-/

open MeasureTheory

namespace SubGaussian

universe u

/-- The real and extended-nonnegative forms of a probability bound agree. -/
theorem probability_toReal_le_iff {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) {b : ℝ} (hb : 0 ≤ b) :
    (μ s).toReal ≤ b ↔ μ s ≤ ENNReal.ofReal b :=
  (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ s) hb).symm

/-- The equivalence specialized to the exponential tail bound. -/
theorem probability_toReal_le_exp_iff {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) (t : ℝ) :
    (μ s).toReal ≤ Real.exp (-(t ^ 2) / 2) ↔
      μ s ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) :=
  probability_toReal_le_iff μ s (Real.exp_pos _).le

end SubGaussian
