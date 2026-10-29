# SubGaussianTailBounds

Complete Lean proofs of explicit tail bounds for the extreme singular values of
matrices with independent sub-Gaussian rows. The two baseline results are:

```lean
SubGaussian.GeneralSingularValueTailBound 3.84 1.58 2.35 1.5
SubGaussian.UnitSingularValueTailBound 1.32 1.12 2.32 (Real.sqrt 2)
```

Both proofs cover arbitrary sample-space universes and all finite numerical
obligations. The public results are `SubGaussian.Current.general` and
`SubGaussian.Current.unit` in
[Canonical/Results.lean](lean/SingularValueBounds/Canonical/Results.lean).

## Quickstart

With the existing pinned Lean **4.19.0** and Mathlib dependencies, run:

```sh
./lean/verify.sh
```

This builds the proofs, independently replays them through Lean's kernel, and
checks the exact canonical results, constants comparisons and allowed axioms.
See [Lean setup](lean/README.md) for external storage and memory settings.
Marcus Webb runs this complete check locally before merging each PR; GitHub CI
checks repository administration only. The
[verification guide](docs/VERIFICATION.md) describes the checks and review procedure.

| Source | Purpose |
|---|---|
| [MainTheoremStatement.lean](MainTheoremStatement.lean) | Immutable authoritative statement, reproduced below |
| [lean/SingularValueBounds/](lean/SingularValueBounds/) | Maintained proofs and supporting mathematics |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Constant policy, proof contributions and research standards |
| [CONTRIBUTIONS.md](CONTRIBUTIONS.md) | Attribution and contribution history |

## Formal statement

The root statement is immutable, including its comments and imports. This is its
complete annotated source. The hypotheses and both non-strict tail bounds are
part of the propositions being proved.

<details>
<summary>Complete annotated MainTheoremStatement.lean</summary>

<!-- canonical-statement:start -->
```lean
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Explicit singular-value tail bounds

Each `def … : Prop := …` names a mathematical statement to be proved.
The positive constants are fixed before the dimensions, probability space and matrix:
`α, β` control the lower tail; `γ, δ` control the upper tail.
Neither tail theorem is proved or assumed. The intended proof targets are:

    GeneralSingularValueTailBound 3.84 1.58 2.35 1.5
    UnitSingularValueTailBound 1.32 1.12 2.32 (Real.sqrt 2)

-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace SubGaussian

/-! ## Extreme singular values

Take the minimum or maximum of the square roots of the eigenvalues of `Aᵀ A`,
including zeros. For real matrices, Mathlib's conjugate transpose `Aᴴ` is `Aᵀ`.
The evidence `hn : 1 ≤ n` guarantees that these finite sets are nonempty.
`min'` and `max'` take their minimum and maximum; the short `by` blocks supply
the nonemptiness proofs. `noncomputable` allows a mathematical definition
without requiring an executable algorithm.
-/

noncomputable def smallestSingularValue {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (Finset.univ.image (fun j =>
    √((Matrix.isHermitian_transpose_mul_self A).eigenvalues j))).min' (by
      classical
      exact ⟨_, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩)

noncomputable def largestSingularValue {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (Finset.univ.image (fun j =>
    √((Matrix.isHermitian_transpose_mul_self A).eigenvalues j))).max' (by
      classical
      exact ⟨_, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩)

/-! ## The two statements

Reading the Lean notation:

- `∀` means "for every", `∧` means "and", and `P → Q` means "if P, then Q".
  A sequence of arrows lists the assumptions leading to the conclusion.
- `Ω` is the space of outcomes, and `μ` is the probability measure.
  `[MeasurableSpace Ω]` supplies measurable sets; `[IsProbabilityMeasure μ]`
  requires total mass one. Lean passes these bracketed assumptions automatically
  when they are available.
- `Fin n` indexes the `n` columns by `0, …, n - 1`; `Fin m` indexes the rows.
  `A : Ω → Matrix (Fin m) (Fin n) ℝ` is a random real `m × n` matrix:
  `A ω i j` is its entry in row `i`, column `j`, at outcome `ω`.
- `fun ω => …` describes a function of the outcome `ω`.
  `∫ ω, f ω ∂μ` is the expectation of `f`; `Integrable f μ` requires the
  measurability needed for integration and finite expectation of `|f|`.
- `{ω | …}` is an event, `MeasurableSet` asserts its measurability, and `μ event`
  is its probability. Measures take values in `ℝ≥0∞` (nonnegative reals with ∞);
  `ENNReal.ofReal` expresses the positive exponential bound in this same type.

Rows are independent as vectors; coordinates within a row may be dependent,
and different rows may have different laws. `EuclideanSpace ℝ (Fin n)` supplies
the Euclidean norm `‖v‖`. The sum `∑ j, A ω i j * v j` is the inner product
of row `i` with `v`. MGF stands for moment-generating function.
-/

-- The universe parameter allows sample spaces Ω of any size.
universe u

/-- **General case:** the constants work for every admissible matrix and every `K ≥ 1`. -/
def GeneralSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  -- The four constants are positive.
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧

  -- For any probability space, dimensions, random matrix A, and parameter K:
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hn : 1 ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ) (K : ℝ),
    -- Assume m ≥ n ≥ 1 and K ≥ 1; hn already supplies n ≥ 1.
    n ≤ m → 1 ≤ K →

    -- Each row is measurable, and the rows are mutually independent.
    (∀ i, Measurable (fun ω => A ω i)) →
    iIndepFun (fun i ω => A ω i) μ →

    -- Centering: each coordinate has expectation zero.
    (∀ i j,
      Integrable (fun ω => A ω i j) μ ∧ (∫ ω, A ω i j ∂μ) = 0) →

    -- Isotropy: each row's second-moment matrix is the identity.
    -- The entry is 1 on the diagonal (j = k), and 0 off the diagonal.
    (∀ i j k,
      Integrable (fun ω => A ω i j * A ω i k) μ ∧
      (∫ ω, A ω i j * A ω i k ∂μ) = if j = k then 1 else 0) →

    -- Sub-Gaussian MGF bound in every direction and for every scalar θ.
    (∀ (i : Fin m) (v : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
      Integrable (fun ω => Real.exp (θ * (∑ j, A ω i j * v j))) μ ∧
      (∫ ω, Real.exp (θ * (∑ j, A ω i j * v j)) ∂μ)
        ≤ Real.exp (K ^ 2 * θ ^ 2 * ‖v‖ ^ 2 / 2)) →

    -- Conclusion: for every t ≥ 0, both tail probabilities satisfy the bounds below.
    ∀ (t : ℝ), 0 ≤ t →
    let L := Real.log (Real.exp 1 * K)  -- log(eK), with natural logarithm

    -- Lower tail: the smallest singular value is at or below this threshold.
    let lowerTail := {ω | smallestSingularValue hn (A ω)
      ≤ √m - K * √n - α * K * L - β * K * √L * t}
    -- Upper tail: the largest singular value is at or above this threshold.
    let upperTail := {ω | largestSingularValue hn (A ω)
      ≥ √m + K * √n + γ * K * L + δ * K * √L * t}

    -- Both events are measurable; each has probability at most exp(-t²/2).
    (MeasurableSet lowerTail ∧
      μ lowerTail ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2))) ∧
    (MeasurableSet upperTail ∧
      μ upperTail ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)))

/-- **Unit case:** `K = 1`, so the MGF bound and tail thresholds simplify. -/
def UnitSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  -- The four constants are positive.
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧

  -- For any probability space, dimensions, and random matrix A:
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (hn : 1 ≤ n)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ),
    -- Assume m ≥ n ≥ 1; hn already supplies n ≥ 1.
    n ≤ m →

    -- Each row is measurable, and the rows are mutually independent.
    (∀ i, Measurable (fun ω => A ω i)) →
    iIndepFun (fun i ω => A ω i) μ →

    -- Centering: each coordinate has expectation zero.
    (∀ i j,
      Integrable (fun ω => A ω i j) μ ∧ (∫ ω, A ω i j ∂μ) = 0) →

    -- Isotropy: each row's second-moment matrix is the identity.
    -- The entry is 1 on the diagonal (j = k), and 0 off the diagonal.
    (∀ i j k,
      Integrable (fun ω => A ω i j * A ω i k) μ ∧
      (∫ ω, A ω i j * A ω i k ∂μ) = if j = k then 1 else 0) →

    -- Sub-Gaussian MGF bound with K = 1, for every direction v and scalar θ.
    (∀ (i : Fin m) (v : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
      Integrable (fun ω => Real.exp (θ * (∑ j, A ω i j * v j))) μ ∧
      (∫ ω, Real.exp (θ * (∑ j, A ω i j * v j)) ∂μ)
        ≤ Real.exp (θ ^ 2 * ‖v‖ ^ 2 / 2)) →

    -- Conclusion: for every t ≥ 0, both tail probabilities satisfy the bounds below.
    ∀ (t : ℝ), 0 ≤ t →

    -- Lower tail: the smallest singular value is at or below this threshold.
    let lowerTail := {ω | smallestSingularValue hn (A ω) ≤ √m - √n - α - β * t}
    -- Upper tail: the largest singular value is at or above this threshold.
    let upperTail := {ω | largestSingularValue hn (A ω) ≥ √m + √n + γ + δ * t}

    -- Both events are measurable; each has probability at most exp(-t²/2).
    (MeasurableSet lowerTail ∧
      μ lowerTail ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2))) ∧
    (MeasurableSet upperTail ∧
      μ upperTail ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)))

end SubGaussian
```
<!-- canonical-statement:end -->

</details>

## Provenance and citation

[CONTRIBUTIONS.md](CONTRIBUTIONS.md) credits Marcus Webb's initial contribution
covering both regimes and preserves subsequent credit. See
[provenance](docs/PROVENANCE.md) for preceding human mathematics and tool roles,
and [verification history](docs/HISTORY.md) for dated evidence.

The accompanying paper remains in preparation. Cite this repository's exact
commit or release using [CITATION.cff](CITATION.cff); a repository release is
separate from paper publication. Original code, proofs and documentation use the
[MIT License](LICENSE); [LICENSING.md](LICENSING.md) records its scope and
third-party terms.
