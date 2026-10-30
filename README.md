# SubGaussianTailBounds

Complete Lean proofs of explicit tail bounds for the extreme singular values of
matrices with independent sub-Gaussian rows.

## Theorem

Let $A$ be a random real $m \times n$ matrix on any probability space, with
integer dimensions $m \ge n \ge 1$. Write $a_i \in \mathbb{R}^n$ for its rows.
Assume the rows are measurable and mutually independent. They need not have the
same distribution, and coordinates within a row may be dependent.

Each row has mean zero and identity covariance: for every row $i$ and
coordinates $j,k$,

```math
\mathbb{E}[A_{ij}] = 0,
\qquad
\mathbb{E}[A_{ij}A_{ik}] =
\begin{cases}1 & j=k,\\ 0 & j\ne k.\end{cases}
```

For a common parameter $K \ge 1$, assume every row satisfies the following
**sub-Gaussian bound**, for every $v \in \mathbb{R}^n$ and $\theta \in \mathbb{R}$:

```math
\mathbb{E}\!\left[\exp\!\left(\theta\langle a_i,v\rangle\right)\right]
\le \exp\!\left(\frac{K^2\theta^2\lVert v\rVert_2^2}{2}\right).
```

The coordinates, their pairwise products within each row, and the exponentials
above are assumed integrable. Here $\lVert\cdot\rVert_2$ is the Euclidean norm.
Let $\sigma_{\min}(A)$ and $\sigma_{\max}(A)$ denote the smallest and largest singular
values of $A$, including zero singular values, and put $L=\log(eK)$, using the
natural logarithm.

Choose the positive constants $(\alpha,\beta,\gamma,\delta)$ from the table below
for the applicable regime. Then, for every $t \ge 0$, the smallest singular value
is unlikely to fall far below $\sqrt m-K\sqrt n$, and the largest is unlikely to
lie far above $\sqrt m+K\sqrt n$. Specifically,

```math
\mathbb{P}\!\left(\sigma_{\min}(A) \le
\sqrt m-K\sqrt n-\alpha KL-\beta K\sqrt L\,t\right)
\le e^{-t^2/2},
```

```math
\mathbb{P}\!\left(\sigma_{\max}(A) \ge
\sqrt m+K\sqrt n+\gamma KL+\delta K\sqrt L\,t\right)
\le e^{-t^2/2}.
```

Each displayed tail event is measurable and has its own probability bound.
The inequalities include equality at the thresholds and apply also at $t=0$.

### Constants proved so far

| Regime | $\alpha$ | $\beta$ | $\gamma$ | $\delta$ |
|---|---:|---:|---:|---:|
| $K = 1$ | 1.32 | 1.12 | 2.32 | $\sqrt{2}$ |
| $K \gt 1$ | 3.84 | 1.58 | 2.35 | 1.5 |

Each row is one jointly proved quartet, valid for every admissible matrix in
that regime. All decimal constants are exact. The general-case quartet in the
second row also holds at $K=1$; the first row gives the sharper constants proved
for that case. When $K=1$, $L=1$, so the additional lower- and upper-tail shifts
simplify to $\alpha+\beta t$ and $\gamma+\delta t$, respectively.

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
checks repository administration only. A green CI status is not proof verification.

## Where to start

| To… | Read… |
|---|---|
| Understand the theorem | The [statement above](#theorem); [MainTheoremStatement.lean](MainTheoremStatement.lean) gives its exact formal version below |
| Follow the proof | [Canonical/Results.lean](lean/SingularValueBounds/Canonical/Results.lean), then its imports |
| Run verification | [lean/README.md](lean/README.md) for setup; [docs/VERIFICATION.md](docs/VERIFICATION.md) for what is checked and the before-merge procedure |
| Make a contribution | [CONTRIBUTING.md](CONTRIBUTING.md) for the mathematical contract, process and attribution |
| Understand the repository | [REPOSITORY_MAP.md](REPOSITORY_MAP.md) for every folder, Python helper, test file and Markdown document |

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
