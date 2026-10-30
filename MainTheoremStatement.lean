import NLAlib.Probability.SubGaussianVector.Basic
import NLAlib.Matrix.Spectral.SingularValues

/-!
# Explicit singular-value tail bounds

NLA-lib supplies the row predicates and singular values. Its sub-Gaussian
parameter is a variance proxy: use `K²` here to retain the bound
`E exp(θ ⟨X,v⟩) ≤ exp(K² θ² ‖v‖² / 2)`. Mean zero and integrability follow from
these imported predicates. Row measurability is kept explicit.

`NLAlib.singularValues A 0` is the largest singular value; index `n - 1` is the
smallest, including zeros, for an `m × n` matrix with `n ≥ 1`.

The intended proof targets, with exact constants, remain:

    GeneralSingularValueTailBound 3.84 1.58 2.35 1.5
    UnitSingularValueTailBound 1.32 1.12 2.32 (Real.sqrt 2)

These definitions name propositions; they do not assume the desired results.
-/

open MeasureTheory ProbabilityTheory

namespace SubGaussian
universe u

/-- Both non-strict tail events are measurable, and each has probability at most
`exp (-t² / 2)`. This retains the equality cases at both thresholds. -/
def SingularValueTails {Ω : Type u} [MeasurableSpace Ω] {m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (lower upper t : ℝ) : Prop :=
  let lowerTail := {ω | NLAlib.singularValues (A ω) (n - 1) ≤ lower}
  let upperTail := {ω | NLAlib.singularValues (A ω) 0 ≥ upper}
  (MeasurableSet lowerTail ∧
    (μ lowerTail).toReal ≤ Real.exp (-(t ^ 2) / 2)) ∧
  (MeasurableSet upperTail ∧
    (μ upperTail).toReal ≤ Real.exp (-(t ^ 2) / 2))

/-- General case: independent centred isotropic rows with MGF parameter `K ≥ 1`. -/
def GeneralSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hn : 1 ≤ n) (A : Ω → Matrix (Fin m) (Fin n) ℝ) (K : ℝ),
    n ≤ m → 1 ≤ K →
    (∀ i, Measurable (fun ω => A ω i)) →
    iIndepFun (fun i ω => A ω i) μ →
    (∀ i, NLAlib.IsSubgaussianVector (fun ω => A ω i) ⟨K ^ 2, sq_nonneg K⟩ μ) →
    (∀ i, NLAlib.IsIsotropic (fun ω => A ω i) μ) →
    ∀ (t : ℝ), 0 ≤ t →
    let L := Real.log (Real.exp 1 * K)
    SingularValueTails μ A
      (√m - K * √n - α * K * L - β * K * √L * t)
      (√m + K * √n + γ * K * L + δ * K * √L * t) t

/-- Unit case: the same row assumptions with MGF parameter `K = 1`. -/
def UnitSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hn : 1 ≤ n) (A : Ω → Matrix (Fin m) (Fin n) ℝ),
    n ≤ m →
    (∀ i, Measurable (fun ω => A ω i)) →
    iIndepFun (fun i ω => A ω i) μ →
    (∀ i, NLAlib.IsSubgaussianVector (fun ω => A ω i) 1 μ) →
    (∀ i, NLAlib.IsIsotropic (fun ω => A ω i) μ) →
    ∀ (t : ℝ), 0 ≤ t →
    SingularValueTails μ A
      (√m - √n - α - β * t)
      (√m + √n + γ + δ * t) t

end SubGaussian
