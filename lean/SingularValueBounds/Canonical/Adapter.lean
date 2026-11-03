import SingularValueBounds.Canonical.Constants
import SingularValueBounds.Canonical.StatementEquivalence
import SingularValueBounds.Canonical.RowBridge

/-! Transfer the internal row estimates to the actual root propositions. -/
open MeasureTheory ProbabilityTheory
namespace SingularValueBounds.Canonical
noncomputable section
universe u

/-- Transfer the general row formulation to the exact canonical proposition. -/
theorem general_of_tailBounds
    (hbound : ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ], KL.TheoremKL μ KL.generalConstants) :
    SubGaussian.GeneralSingularValueTailBound.{u} SubGaussian.Constants.generalAlpha
      SubGaussian.Constants.generalBeta SubGaussian.Constants.generalGamma
      SubGaussian.Constants.generalDelta := by
  apply (SubGaussian.general_iff_previous _ _ _ _ (by norm_num)).mpr
  refine ⟨by norm_num, ?_⟩
  intro Ω _ μ _ m n hn A K hnm hK hm hind hc hi hsg t ht
  letI : NeZero n := ⟨by omega⟩
  have hA : Measurable A := measurable_pi_lambda _ hm
  have hiso : ∀ i, CentredIsotropic μ (fun ω => A ω i) :=
    fun i => centredIsotropic_of_coordinates (hm i) (hc i) (hi i)
  have hsub : ∀ i, SubGaussianMGF μ (fun ω => A ω i) K :=
    fun i => subGaussianMGF_of_directions (hsg i)
  obtain ⟨hl, hu⟩ := hbound Ω μ m n hnm
    (fun i ω => A ω i) K hK hind hiso hsub t ht
  constructor
  · refine ⟨measurableSet_le ((measurable_smallestSingularValue hn).comp hA)
      measurable_const, ?_⟩
    apply ennreal_bound_of_real (Real.exp_pos _).le
    convert hl using 1
    norm_num [smallestSingularValue_eq, SingularValueBounds.rowMatrix, KL.LowerThreshold,
        KL.generalConstants, ← logParameter_eq hK]
    rfl
  · refine ⟨measurableSet_le measurable_const
      ((measurable_largestSingularValue hn).comp hA), ?_⟩
    apply ennreal_bound_of_real (Real.exp_pos _).le
    convert hu using 1
    norm_num [largestSingularValue_eq, SingularValueBounds.rowMatrix, KL.UpperThreshold,
        KL.generalConstants, ← logParameter_eq hK]
    rfl

/-- Transfer the unit row formulation to the exact canonical proposition. -/
theorem unit_of_tailBounds
    (hbound : ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ], KL.TheoremKLOne μ) :
    SubGaussian.UnitSingularValueTailBound.{u} SubGaussian.Constants.unitAlpha
      SubGaussian.Constants.unitBeta SubGaussian.Constants.unitGamma
      SubGaussian.Constants.unitDelta := by
  apply (SubGaussian.unit_iff_previous _ _ _ _ (by norm_num)).mpr
  refine ⟨by norm_num, ?_⟩
  intro Ω _ μ _ m n hn A hnm hm hind hc hi hsg t ht
  letI : NeZero n := ⟨by omega⟩
  have hA : Measurable A := measurable_pi_lambda _ hm
  have hiso : ∀ i, CentredIsotropic μ (fun ω => A ω i) :=
    fun i => centredIsotropic_of_coordinates (hm i) (hc i) (hi i)
  have hsub : ∀ i, SubGaussianMGF μ (fun ω => A ω i) 1 := by
    intro i
    apply subGaussianMGF_of_directions
    simpa only [one_pow, one_mul] using hsg i
  obtain ⟨hl, hu⟩ := hbound Ω μ m n hnm
    (fun i ω => A ω i) hind hiso hsub t ht
  constructor
  · refine ⟨measurableSet_le ((measurable_smallestSingularValue hn).comp hA)
      measurable_const, ?_⟩
    apply ennreal_bound_of_real (Real.exp_pos _).le
    convert hl using 1
    norm_num [smallestSingularValue_eq, SingularValueBounds.rowMatrix, KL.LowerThreshold,
        KL.oneConstants, logParameter]
    rfl
  · refine ⟨measurableSet_le measurable_const
      ((measurable_largestSingularValue hn).comp hA), ?_⟩
    apply ennreal_bound_of_real (Real.exp_pos _).le
    convert hu using 1
    norm_num [largestSingularValue_eq, SingularValueBounds.rowMatrix, KL.UpperThreshold,
        KL.oneConstants, logParameter]
    rfl

end
end SingularValueBounds.Canonical
