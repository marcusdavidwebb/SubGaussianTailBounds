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

/-- Changing a random matrix on a null set preserves both tail probabilities. -/
theorem gaussianSingularValueTails_congr_ae {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ}
    {A B : Ω → Matrix (Fin m) (Fin n) ℝ} (hAB : A =ᵐ[μ] B)
    (lower upper t : ℝ) :
    GaussianSingularValueTails μ A lower upper t ↔
      GaussianSingularValueTails μ B lower upper t := by
  have hl : μ {ω | NLAlib.singularValues (A ω) (n - 1) ≤ lower} =
      μ {ω | NLAlib.singularValues (B ω) (n - 1) ≤ lower} :=
    measure_congr (hAB.fun_comp fun C => NLAlib.singularValues C (n - 1) ≤ lower)
  have hu : μ {ω | NLAlib.singularValues (A ω) 0 ≥ upper} =
      μ {ω | NLAlib.singularValues (B ω) 0 ≥ upper} :=
    measure_congr (hAB.fun_comp fun C => NLAlib.singularValues C 0 ≥ upper)
  simp only [GaussianSingularValueTails, hl, hu]

end SubGaussian
