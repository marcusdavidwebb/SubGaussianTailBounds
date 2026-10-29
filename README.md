# SubGaussianTailBounds

A Lean formalization project for explicit tail bounds on the extreme singular
values of matrices with independent sub-Gaussian rows. The two fixed targets are:

```lean
SubGaussian.GeneralSingularValueTailBound 3.84 1.58 2.35 1.5
SubGaussian.UnitSingularValueTailBound 1.32 1.12 2.32 (Real.sqrt 2)
```

Both baselines have complete, universe-polymorphic Lean proofs, including all
finite numerical inequalities. The public results are
[`SubGaussian.Current.general`](lean/SingularValueBounds/Canonical/Results.lean)
and [`SubGaussian.Current.unit`](lean/SingularValueBounds/Canonical/Results.lean).
There are no external certificate premises or Python mathematical checks.
See the [migration and validation record](docs/MIGRATION.md).
[MainTheoremStatement.lean](MainTheoremStatement.lean) defines the authoritative
propositions; their proofs belong in the maintained implementation.

| Find | Location |
|---|---|
| The authoritative formal statement | [MainTheoremStatement.lean](MainTheoremStatement.lean), reproduced below |
| The maintained mathematical library | [lean/SingularValueBounds/](lean/SingularValueBounds/) |
| Baseline proofs | [General.lean](lean/SingularValueBounds/Canonical/General.lean) · [Unit.lean](lean/SingularValueBounds/Canonical/Unit.lean) |
| Current results and comparisons | [Canonical/Results.lean](lean/SingularValueBounds/Canonical/Results.lean) |
| Canonical adapters | [Canonical/Adapter.lean](lean/SingularValueBounds/Canonical/Adapter.lean) |
| Setup and verification | [Quickstart](#quickstart) · [Detailed Lean setup](lean/README.md) |
| Contribute and find credit | [Contribution contract](CONTRIBUTING.md) · [Contribution history](CONTRIBUTIONS.md) |

## Theorem statement

This is Theorem S1.1 (`thm:explicit-constants`) from the historical supplement,
with its mathematical content unchanged.

There are positive universal constants $\alpha,\beta,\gamma,\delta$ with the
following property. Let $S\in\mathbb R^{m\times n}$, $m\ge n\ge1$, have
independent, centred, isotropic rows $X_i^T$, meaning
$\mathbb E X_i=0$ and $\mathbb E X_iX_i^T=I_n$. Suppose that, for some $K\ge1$,

$$
\mathbb E e^{\lambda\langle X_i,v\rangle}
\le e^{K^2\lambda^2\|v\|_2^2/2}
\qquad(\lambda\in\mathbb R,\ v\in\mathbb R^n,\ 1\le i\le m).
$$

Put $L=\log(eK)$, with natural logarithms, and let $\sigma_{\min}(S)$ and
$\sigma_{\max}(S)$ denote the smallest and largest of its $n$ singular values,
including zeros. Then, for every $t\ge0$,

$$
\mathbb P\left\{\sigma_{\min}(S)\le\sqrt m-K\sqrt n
-\alpha KL-\beta K\sqrt L\,t\right\}\le e^{-t^2/2},
$$

$$
\mathbb P\left\{\sigma_{\max}(S)\ge\sqrt m+K\sqrt n
+\gamma KL+\delta K\sqrt L\,t\right\}\le e^{-t^2/2}.
$$

For every $K\ge1$, one may take $(\alpha,\beta,\gamma,\delta)=(3.84,1.58,2.35,1.5)$.
When $K=1$, one may instead take $(1.32,1.12,2.32,\sqrt2)$.

The constants $\alpha,\gamma$ control the additive correction $KL$;
$\beta,\delta$ control the fluctuation correction $K\sqrt L\,t$. At $K=1$,
$L=1$, so the two thresholds are $\sqrt m-\sqrt n-\alpha-\beta t$ and
$\sqrt m+\sqrt n+\gamma+\delta t$. Each tail has its own failure bound
$e^{-t^2/2}$. The events are non-strict, including at $t=0$; all singular values
are included even for a rank-deficient matrix. Rows can have different laws,
and coordinates in a row need not be independent.

| Regime | Initial comparison quartet $(\alpha,\beta,\gamma,\delta)$ | Complete canonical Lean proof |
|---|---|---|
| Every $K\ge1$ | $(3.84,1.58,2.35,1.5)$ | `SubGaussian.Current.general` |
| $K=1$ | $(1.32,1.12,2.32,\sqrt2)$ | `SubGaussian.Current.unit` |

No improvement over these baselines has been accepted. Decimal constants are
exact rationals in Lean; $\sqrt2$ is exact. The baseline quartets remain
permanent ceilings and proof targets. See [CONSTANTS.md](CONSTANTS.md) for the
replacement policy and historical verification status.

## Formal statement

The root file is immutable, including its comments and imports. Its full
annotated contents appear below. This is a presentation of the authoritative
source, not a second definition to edit. The canonical propositions quantify
over arbitrary sample-space universes and explicitly require integrability,
event measurability, and probability bounds in `ℝ≥0∞`.

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

## Quickstart

Reuse Lean **4.19.0** and the exact locked dependencies; follow
[the pinned setup](lean/README.md#pinned-environment-and-storage). Keep packages,
caches and build outputs in an external workspace under `~/Lean/`. Ordinary
local verification does not install or upgrade dependencies.

```sh
./lean/verify.sh
```

This builds the actual root statement and the maintained formalization, checks
both exact canonical results and their comparison proofs, and independently
replays the maintained modules through Lean's kernel. The only permitted axioms
are `propext`, `Classical.choice` and `Quot.sound`. Python performs repository
administration only. Cold builds and replay are substantial computations; see
[parallelism and storage options](lean/README.md) and
[observed validation](docs/MIGRATION.md).

CI runs lightweight repository checks only. Marcus Webb runs the complete Lean
verification locally before merging each PR; a green CI status does not certify
the proofs. See [the manual review procedure](docs/CI.md).

For a quick source-integrity check, run
`python3 scripts/check_canonical_statement.py`. It checks the immutable bytes and
README presentation and does not establish mathematical truth.

## Contribute

Contributions update one maintained formalization. A contribution can concern
either regime alone, and a complete alternative proof with all four constants
unchanged is eligible for review. It must prove the canonical proposition and
all four comparisons against both the original baseline and the trusted current
accepted quartet. **No current constant may increase.** Marcus Webb reserves
the decision to accept or reject every PR; eligibility does not guarantee
acceptance.

For example, a general-regime proof at `(3.70, 1.58, 2.35, 1.5)` would satisfy
the initial numerical ceilings if it proves the whole canonical proposition
and its comparisons in Lean. After acceptance, a proposal at
`(3.75, 1.55, 2.35, 1.5)` would be ineligible because it increases the accepted
first constant. These numbers illustrate policy and do not assert a proved
improvement.

Submit Lean sources, concise explanation and attribution, and a history entry;
no separate prose proof, PDF proof or Python certificate submission is part of
the contract. The [contribution guide](CONTRIBUTING.md) explains where to edit
the implementation and record credit. The [Lean interface](docs/CI.md#lean-interface)
specifies the stable declarations checked by `./lean/verify.sh`. The maintainer
checks each proposed branch locally against the accepted base before merging.

## Provenance and citation

[CONTRIBUTIONS.md](CONTRIBUTIONS.md) contains one initial contribution credited
to Marcus Webb and preserves substantial credit when implementations are
superseded. [Provenance](docs/PROVENANCE.md) preserves the preceding human
mathematics, model identities, tool roles, historical validation and unresolved
attribution assessments. Verification does not establish novelty.

[supplementary.tex](supplementary.tex) and its [PDF](supplementary.pdf) are
**historical documents, pending the maintainer's later deletion**. They are not
maintained proof submissions or specifications for future Lean changes. See the
[historical notice](docs/HISTORICAL_SUPPLEMENT.md).

The accompanying paper, *Sharp tail bounds for the extreme singular values of
sub-Gaussian matrices*, by Marcus Webb and Morgan Lynch-Davies, is **in
preparation**, with no public version established here. Use [CITATION.cff](CITATION.cff)
and identify the actual repository commit or release used. Repository releases
are separate from publication of the paper; no DOI or release identifier is
invented here.

The project's original code, proofs and documentation use the [MIT License](LICENSE).
Third-party material retains its own terms and notices; see [LICENSING.md](LICENSING.md).
