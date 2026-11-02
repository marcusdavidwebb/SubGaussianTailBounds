# SubGaussianTailBounds

This repository accompanies the paper *Sharp tail bounds for the extreme singular values of sub-Gaussian matrices*, by Marcus Webb and Morgan Lynch-Davies (in preparation).

In the paper we prove that there exist universal constants $\alpha,\beta,\gamma,\delta > 0$, but provide no bounds. In this repository, we provide complete Lean proofs of some explicit values of these constants. We do not claim they are optimal, and encourage contributions according to the contribution guidelines.

## Theorem

Let $A$ be a random real $m \times n$ matrix, with $m \ge n \ge 1$. Write $a_i \in \mathbb{R}^n$ for its rows. Assume the rows are measurable and mutually independent. They need not have the same distribution, and coordinates within a row may be dependent.

Each row has mean zero and identity covariance: for every row $i$ and coordinates $j,k$,

```math
\mathbb{E}[A_{ij}] = 0,
\qquad
\mathbb{E}[A_{ij}A_{ik}] =
\begin{cases}1 & j=k,\\ 0 & j\ne k.\end{cases}
```

For a common parameter $K \ge 1$, assume every row satisfies the following **sub-Gaussian bound**, for every $v \in \mathbb{R}^n$ and $\theta \in \mathbb{R}$:

```math
\mathbb{E}\!\left[\exp\!\left(\theta\langle a_i,v\rangle\right)\right]
\le \exp\!\left(\frac{K^2\theta^2\lVert v\rVert_2^2}{2}\right).
```

The coordinates, their pairwise products within each row, and the exponentials above are assumed integrable. Let $\sigma_{\min}(A)$ and $\sigma_{\max}(A)$ denote the smallest and largest singular values of $A$, including zero singular values, and put $L=\log(eK)$, using the natural logarithm.

For either quartet $(\alpha,\beta,\gamma,\delta)$ in the table below and every $t \ge 0$, the following bounds hold in its stated regime:

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

### Admissible constants

| Regime | $\alpha$ | $\beta$ | $\gamma$ | $\delta$ |
|---|---:|---:|---:|---:|
| General: $K \ge 1$ | 3.84 | 1.58 | 2.35 | 1.50 |
| Unit: $K = 1$ | 1.32 | 1.12 | 2.32 | 1.42 |

## Formalization

The definitions in [MainTheoremStatement.lean](MainTheoremStatement.lean) are the single authoritative statement. They name propositions; they contain no proofs. `GaussianSingularValueTails` packages the two measurable events and their $e^{-t^2/2}$ bounds; “Gaussian” describes this decay rate. The rows satisfy the sub-Gaussian assumptions above.

`TailBoundAt K α β γ δ` collects the dimension requirements $m \ge n \ge 1$, common row assumptions and tail bounds at a fixed parameter. The general proposition adds positivity of the four constants and quantifies over every $K \ge 1$; the unit proposition adds the same positivity and specializes the helper to $K=1$. At that value, the variance proxy is $1$ and $L=\log(e)=1$, giving the simplified thresholds above.

[Canonical/Results.lean](lean/SingularValueBounds/Canonical/Results.lean) proves the following baseline declarations for every sample-space universe `u`:

```lean
SubGaussian.Current.general_baseline.{u} :
  SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5

SubGaussian.Current.unit_baseline.{u} :
  SubGaussian.UnitSingularValueTailBound.{u} 1.32 1.12 2.32 1.42
```

The current results are `SubGaussian.Current.general` and `SubGaussian.Current.unit`. Both regimes include all finite numerical proof obligations. The [validation history](docs/HISTORY.md) records the scope of completed checks and outstanding verification.

## Quickstart

With the pinned Lean **4.33.1**, Mathlib and NLA-lib dependencies stored centrally, check the two displayed propositions and their proof dependencies with:

```sh
./lean/check-statements.sh
```

This focused check builds the proofs and checks the two exact types and their axioms. It trusts imported compiled dependencies and elaborators and does not perform the full repository audit. For that broader check, run:

```sh
./lean/verify.sh
```

This independently replays the maintained modules through Lean's kernel and checks the canonical results, constants comparisons, source coverage and axioms. See [Lean setup](lean/README.md) for external storage and memory settings. Marcus Webb runs this complete check locally before merging each PR; GitHub CI checks repository administration only. A green CI status is not proof verification.

## Where to start

| To… | Read… |
|---|---|
| Understand the theorem | The [statement above](#theorem); [MainTheoremStatement.lean](MainTheoremStatement.lean) gives its exact formal version below |
| Read or typeset both statements | [PDF](MainTheoremStatement.pdf) and [TeX source](MainTheoremStatement.tex); see [regeneration](#tex-statement) |
| Follow the proof | [Canonical/Results.lean](lean/SingularValueBounds/Canonical/Results.lean), then its imports |
| Run verification | [lean/README.md](lean/README.md) for setup; [docs/VERIFICATION.md](docs/VERIFICATION.md) for what is checked and the before-merge procedure |
| Make a contribution | [CONTRIBUTING.md](CONTRIBUTING.md) for the mathematical contract, process and attribution |
| Find sources and tools | The [source layout](lean/README.md#source-layout) |

## Formal statement

The root statement is immutable, including its comments and imports. This is its complete annotated source. The hypotheses and both non-strict tail bounds are part of the propositions being proved. The tail probabilities are real-valued under the explicit probability-measure assumption.

The statement uses `NLAlib.IsSubgaussianVector`, `NLAlib.IsIsotropic` and `NLAlib.singularValues` from the pinned [NLA-lib dependency](https://github.com/NLA-lib/NLAlib/tree/6491e7528c1b1e68e46301cde6a76ae153e8e834). Its variance proxy is `K²`; mean zero and the required integrability follow from the imported predicates. Row measurability remains explicit. [StatementEquivalence.lean](lean/SingularValueBounds/Canonical/StatementEquivalence.lean) proves equivalence with the preceding expanded formulation for every quartet and every sample-space universe, preserving the natural-language theorem above. NLA-lib and all compiled dependencies live in the external Lean workspace, not in this repository.

<!-- canonical-statement:start -->
```lean
import NLAlib.Probability.SubGaussianVector.Basic
import NLAlib.Matrix.Spectral.SingularValues

open MeasureTheory ProbabilityTheory

namespace SubGaussian
universe u

def GaussianSingularValueTails {Ω : Type u} {m n : ℕ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (lower upper t : ℝ) : Prop :=
    (μ {ω | NLAlib.singularValues (A ω) (n-1) ≤ lower}).toReal ≤ Real.exp(-(t^2)/2))
      ∧ (μ {ω | NLAlib.singularValues (A ω) 0 ≥ upper}).toReal ≤ Real.exp(-(t^2)/2))

def TailBoundAt (K α β γ δ : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (A : Ω → Matrix (Fin m) (Fin n) ℝ),
    1 ≤ n → n ≤ m →
    (∀ i, Measurable (fun ω => A ω i)) →
    iIndepFun (fun i ω => A ω i) μ →
    (∀ i, NLAlib.IsIsotropic (fun ω => A ω i) μ) →
    (∀ i, NLAlib.IsSubgaussianVector (fun ω => A ω i) ⟨K ^ 2, sq_nonneg K⟩ μ) →
    ∀ t : ℝ, 0 ≤ t →
    let L := Real.log (Real.exp 1 * K)
    GaussianSingularValueTails μ A (√m - K * √n - α * K * L - β * K * √L * t)
      (√m + K * √n + γ * K * L + δ * K * √L * t) t

def GeneralSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧ ∀ K : ℝ, 1 ≤ K → TailBoundAt.{u} K α β γ δ

def UnitSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧ TailBoundAt.{u} 1 α β γ δ

end SubGaussian
```
<!-- canonical-statement:end -->

## TeX statement

[MainTheoremStatement.tex](MainTheoremStatement.tex) and [MainTheoremStatement.pdf](MainTheoremStatement.pdf) contain the theorem, its constants table and the complete annotated Lean statement. The Lean source is final and immutable; README prose explains that source, and the constants come from the proved results. After clarifying the README presentation, update both generated files with one command:

```sh
python3 scripts/generate_theorem_tex.py
```

The generator validates the canonical source and README, generates the TeX, and automatically compiles the PDF with XeLaTeX. Only the `.tex` and `.pdf` remain in the repository: compilation runs in a temporary directory that is removed even if the build fails. A failed compilation preserves the previous TeX and PDF. XeLaTeX, `fontspec`, `fvextra` and the DejaVu Sans Mono font are required; these are provided by the installed TeX Live distribution.

The PDF presents the theorem and constants, followed by one Lean statement section with the complete canonical source and line numbers. It includes the README's attribution and clickable repository links; the longer formalization discussion remains above. Its statement ID identifies the source content; the full SHA-256 is recorded in the TeX and PDF metadata. It is not a Git revision or a proof verification result.

For editor builds, [.latexmkrc](.latexmkrc) configures `latexmk` to use XeLaTeX, keep only the finished PDF next to the TeX, and remove temporary compilation files when it exits. To rebuild the existing TeX manually:

```sh
latexmk MainTheoremStatement.tex
```

For continuous rebuilding whenever the TeX is saved, run `latexmk -pvc -view=none MainTheoremStatement.tex`; stop it with Ctrl-C.

Edit the README rather than the generated TeX to keep the statements in sync. `python3 scripts/generate_theorem_tex.py --check` checks the TeX against the README and canonical source without writing files or invoking a compiler. Administrative CI runs this synchronization check using the trusted base's generator; it does not compile or verify the PDF or establish mathematical truth.

## Provenance and citation

[CONTRIBUTIONS.md](CONTRIBUTIONS.md) credits Marcus Webb's initial contribution covering both regimes and preserves subsequent credit. See [provenance](docs/PROVENANCE.md) for preceding human mathematics and tool roles, and [verification history](docs/HISTORY.md) for dated evidence.

The accompanying paper remains in preparation. Cite this repository's exact commit or release using [CITATION.cff](CITATION.cff); a repository release is separate from paper publication. Original code, proofs and documentation use the [MIT License](LICENSE); [LICENSING.md](LICENSING.md) records its scope and third-party terms.
