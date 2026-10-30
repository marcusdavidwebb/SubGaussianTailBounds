# SubGaussianTailBounds

This repository accompanies the paper *Sharp tail bounds for the extreme singular
values of sub-Gaussian matrices*, by Marcus Webb and Morgan Lynch-Davies
(in preparation).

It contains complete Lean proofs of explicit tail bounds for the extreme singular
values of matrices with independent sub-Gaussian rows.

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

With the pinned Lean **4.33.1**, Mathlib and NLA-lib dependencies stored centrally, run:

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
part of the propositions being proved. The tail probabilities are real-valued
under the explicit probability-measure assumption.

The statement uses `NLAlib.IsSubgaussianVector`, `NLAlib.IsIsotropic` and
`NLAlib.singularValues` from the pinned
[NLA-lib dependency](https://github.com/NLA-lib/NLAlib/tree/6491e7528c1b1e68e46301cde6a76ae153e8e834).
Its variance proxy is `K²`; mean zero and the required integrability follow from
the imported predicates. Row measurability remains explicit.
[StatementEquivalence.lean](lean/SingularValueBounds/Canonical/StatementEquivalence.lean)
proves equivalence with the preceding expanded formulation for every quartet
and every sample-space universe, preserving the natural-language theorem above.
NLA-lib and all compiled dependencies live in the external Lean workspace,
not in this repository.

<details>
<summary>Complete annotated MainTheoremStatement.lean</summary>

<!-- canonical-statement:start -->
```lean
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
