import SingularValueBounds.Canonical.TailEquivalence
import SingularValueBounds.Canonical.NLARows
import SingularValueBounds.Canonical.NLASingularValues

/-!
# Equivalence with the preceding canonical statements

The two `Previous…` propositions below retain the unbundled hypotheses and
conclusions of the canonical source before the statement simplification of
30 October 2026. The equivalences check that importing the row predicates and singular values
from NLA-lib preserves both statements, for every quartet of constants
and every sample-space universe. They also account for the shared `TailBoundAt`
formulation: the general case quantifies over `K` first, and the unit case
simplifies `K = 1`, including its variance proxy and `log (exp 1) = 1`.
They assert no tail bound by themselves.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace SubGaussian

universe u

/-- The preceding general proposition, with its original unbundled hypotheses. -/
def PreviousGeneralSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hn : 1 ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ) (K : ℝ),
    n ≤ m → 1 ≤ K →
    (∀ i, Measurable (fun ω => A ω i)) →
    iIndepFun (fun i ω => A ω i) μ →
    (∀ i j,
      Integrable (fun ω => A ω i j) μ ∧ (∫ ω, A ω i j ∂μ) = 0) →
    (∀ i j k,
      Integrable (fun ω => A ω i j * A ω i k) μ ∧
      (∫ ω, A ω i j * A ω i k ∂μ) = if j = k then 1 else 0) →
    (∀ (i : Fin m) (v : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
      Integrable (fun ω => Real.exp (θ * (∑ j, A ω i j * v j))) μ ∧
      (∫ ω, Real.exp (θ * (∑ j, A ω i j * v j)) ∂μ)
        ≤ Real.exp (K ^ 2 * θ ^ 2 * ‖v‖ ^ 2 / 2)) →
    ∀ (t : ℝ), 0 ≤ t →
    let L := Real.log (Real.exp 1 * K)
    let lowerTail := {ω | Previous.smallestSingularValue hn (A ω)
      ≤ √m - K * √n - α * K * L - β * K * √L * t}
    let upperTail := {ω | Previous.largestSingularValue hn (A ω)
      ≥ √m + K * √n + γ * K * L + δ * K * √L * t}
    (MeasurableSet lowerTail ∧
      μ lowerTail ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2))) ∧
    (MeasurableSet upperTail ∧
      μ upperTail ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)))

/-- The preceding unit proposition, with its original unbundled hypotheses. -/
def PreviousUnitSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hn : 1 ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ),
    n ≤ m →
    (∀ i, Measurable (fun ω => A ω i)) →
    iIndepFun (fun i ω => A ω i) μ →
    (∀ i j,
      Integrable (fun ω => A ω i j) μ ∧ (∫ ω, A ω i j ∂μ) = 0) →
    (∀ i j k,
      Integrable (fun ω => A ω i j * A ω i k) μ ∧
      (∫ ω, A ω i j * A ω i k ∂μ) = if j = k then 1 else 0) →
    (∀ (i : Fin m) (v : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
      Integrable (fun ω => Real.exp (θ * (∑ j, A ω i j * v j))) μ ∧
      (∫ ω, Real.exp (θ * (∑ j, A ω i j * v j)) ∂μ)
        ≤ Real.exp (θ ^ 2 * ‖v‖ ^ 2 / 2)) →
    ∀ (t : ℝ), 0 ≤ t →
    let lowerTail := {ω | Previous.smallestSingularValue hn (A ω) ≤ √m - √n - α - β * t}
    let upperTail := {ω | Previous.largestSingularValue hn (A ω) ≥ √m + √n + γ + δ * t}
    (MeasurableSet lowerTail ∧
      μ lowerTail ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2))) ∧
    (MeasurableSet upperTail ∧
      μ upperTail ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)))

/-- The imported row and singular-value definitions preserve the original theorem. -/
theorem general_iff_previous (α β γ δ : ℝ) :
    GeneralSingularValueTailBound.{u} α β γ δ ↔
      PreviousGeneralSingularValueTailBound.{u} α β γ δ := by
  constructor
  · rintro ⟨hpos, h⟩
    refine ⟨hpos, ?_⟩
    intro Ω _ μ _ m n hn A K hnm hK hm hind hc hi hsg t ht
    have hsub : ∀ i, NLAlib.IsSubgaussianVector (fun ω => A ω i) ⟨K ^ 2, sq_nonneg K⟩ μ :=
      fun i => isSubgaussianVector_iff_previous.mpr (hsg i)
    have hiso : ∀ i, NLAlib.IsIsotropic (fun ω => A ω i) μ :=
      fun i => isIsotropic_of_previous (hsub i) ⟨hm i, hc i, hi i⟩
    simpa only [GaussianSingularValueTails, probability_toReal_le_exp_iff,
      Previous.smallestSingularValue_eq_nla,
      Previous.largestSingularValue_eq_nla] using
      h K hK μ m n A hn hnm hm hind hsub hiso t ht
  · rintro ⟨hpos, h⟩
    refine ⟨hpos, ?_⟩
    intro K hK Ω _ μ _ m n A hn hnm hm hind hsub hiso t ht
    have hrows := fun i => previousIsCentredIsotropic_of_nla (hm i) (hsub i) (hiso i)
    simpa only [GaussianSingularValueTails, probability_toReal_le_exp_iff,
      Previous.smallestSingularValue_eq_nla,
      Previous.largestSingularValue_eq_nla] using
      h μ m n hn A K hnm hK hm hind (fun i => (hrows i).centred)
        (fun i => (hrows i).isotropic)
        (fun i => isSubgaussianVector_iff_previous.mp (hsub i)) t ht

/-- The imported predicates with variance proxy one preserve the original unit theorem. -/
theorem unit_iff_previous (α β γ δ : ℝ) :
    UnitSingularValueTailBound.{u} α β γ δ ↔
      PreviousUnitSingularValueTailBound.{u} α β γ δ := by
  constructor
  · rintro ⟨hpos, h⟩
    refine ⟨hpos, ?_⟩
    intro Ω _ μ _ m n hn A hnm hm hind hc hi hsg t ht
    have hsub : ∀ i, NLAlib.IsSubgaussianVector (fun ω => A ω i)
        ⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ μ := by
      intro i
      apply isSubgaussianVector_iff_previous.mpr
      simpa only [PreviousIsSubgaussianVector, one_pow, one_mul] using hsg i
    have hiso : ∀ i, NLAlib.IsIsotropic (fun ω => A ω i) μ :=
      fun i => isIsotropic_of_previous (hsub i) ⟨hm i, hc i, hi i⟩
    simpa only [one_mul, mul_one, Real.log_exp, Real.sqrt_one,
      GaussianSingularValueTails, probability_toReal_le_exp_iff,
      Previous.smallestSingularValue_eq_nla,
      Previous.largestSingularValue_eq_nla] using h μ m n A hn hnm hm hind hsub hiso t ht
  · rintro ⟨hpos, h⟩
    refine ⟨hpos, ?_⟩
    intro Ω _ μ _ m n A hn hnm hm hind hsub hiso t ht
    have hrows := fun i => previousIsCentredIsotropic_of_nla (hm i) (hsub i) (hiso i)
    have hsg : ∀ (i : Fin m) (v : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
        Integrable (fun ω => Real.exp (θ * (∑ j, A ω i j * v j))) μ ∧
        (∫ ω, Real.exp (θ * (∑ j, A ω i j * v j)) ∂μ) ≤
          Real.exp (θ ^ 2 * ‖v‖ ^ 2 / 2) := by
      intro i
      simpa only [PreviousIsSubgaussianVector, one_pow, one_mul] using
        isSubgaussianVector_iff_previous.mp (hsub i)
    simpa only [one_mul, mul_one, Real.log_exp, Real.sqrt_one,
      GaussianSingularValueTails, probability_toReal_le_exp_iff,
      Previous.smallestSingularValue_eq_nla,
      Previous.largestSingularValue_eq_nla] using
      h μ m n hn A hnm hm hind (fun i => (hrows i).centred)
        (fun i => (hrows i).isotropic) hsg t ht

end SubGaussian
