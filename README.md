# SubGaussianTailBounds

This repository accompanies the paper *Sharp tail bounds for the extreme singular values of sub-Gaussian matrices*, by Marcus Webb and Morgan Lynch-Davies (in preparation).

It supplies complete Lean proofs at explicit admissible constants. No optimality
is claimed. Contributions may improve the argument, its checking cost or the constants.

## Theorem

Let $A$ be a random real $m \times n$ matrix, with $m \ge n \ge 1$. Write $a_i \in \mathbb{R}^n$ for its rows. Assume the rows are mutually independent with mean zero and identity covariance. They need not have the same distribution, and coordinates within a row may be dependent.

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

## Formalization and checking

[MainTheoremStatement.lean](MainTheoremStatement.lean) is the authoritative root
statement. Its definitions name propositions; they contain no proofs.
[Canonical/Results.lean](lean/SingularValueBounds/Canonical/Results.lean) proves
`SubGaussian.Current.general.{u}` and `SubGaussian.Current.unit.{u}` for arbitrary
sample-space universe `u`. The eight exact rational coefficients come from
[Constants.lean](lean/SingularValueBounds/Canonical/Constants.lean); the table above
and the TeX/PDF are generated presentations of those values.

To compile the two displayed claims with Lake, install [Elan](https://github.com/leanprover/elan),
then run:

```sh
git clone https://github.com/marcusdavidwebb/SubGaussianTailBounds.git
cd SubGaussianTailBounds
lake exe cache get
lake build
```

Elan selects the pinned Lean **4.33.1** toolchain; Lake fetches the pinned
dependencies and matching Mathlib artifacts. The standard workflow stores
dependencies and build outputs in the checkout's `.lake` directory. See
[setup](lean/README.md) for prerequisites and the external-workspace alternative.

[CheckStatements.lean](lean/SingularValueBounds/CheckStatements.lean) displays
the two exact claims and applies their proofs. Its proposition definitions are in
the actual root statement linked above. The default Lake target is this module;
it can also be selected explicitly with `lake build SingularValueBounds.CheckStatements`.
Lake may reuse compiled imports and project
artifacts; a build alone does not perform the separate audits below.
Lake's own scheduler can use substantial memory. The focused audit below uses a
bounded build scheduler, with its own external setup described in the setup guide.

From the repository root, the stronger checks are:

```sh
./lean/check-statements.sh  # build and audit the two exact propositions
./lean/verify.sh            # also independently replay every maintained module
```

Both scripts build as needed and check exact types, universes, the axiom allowlist
and input identity. The full check also checks maintained-source coverage.
The focused check trusts compiled imports; the full check independently replays
maintained project modules. CI runs lightweight administration only. See
[setup](lean/README.md) and the [contribution guide](CONTRIBUTING.md).

The proof transfers one-row lower and upper estimates through the matrix barrier
argument. Exact finite certificates supply its remaining scalar and polynomial
bounds. The canonical adapters prove correspondence of NLA-lib's isotropy,
variance proxy `K²` and ordered singular values with the internal formulation,
including zero singular values. [StatementEquivalence.lean](lean/SingularValueBounds/Canonical/StatementEquivalence.lean)
also relates the current statement to the preceding expanded formulation at
positive coefficients.

## Formal statement

The complete root source is reproduced below. Its pinned imported definitions
come from [NLA-lib](https://github.com/NLA-lib/NLAlib/tree/6491e7528c1b1e68e46301cde6a76ae153e8e834).
The probability bounds are real-valued under the explicit probability-measure
assumption. Statement changes, including changes through imported definitions,
require conspicuous review. Checks use the current source, without a fixed
statement hash; a source hash alone establishes no mathematical fact.

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
    (μ {ω | NLAlib.singularValues (A ω) (n-1) ≤ lower}).toReal ≤ Real.exp (-(t^2)/2)
      ∧ (μ {ω | NLAlib.singularValues (A ω) 0 ≥ upper}).toReal ≤ Real.exp (-(t^2)/2)

def TailBoundAt (K α β γ δ : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (A : Ω → Matrix (Fin m) (Fin n) ℝ),
    1 ≤ n → n ≤ m →
    iIndepFun (fun i ω => A ω i) μ →
    (∀ i, NLAlib.IsIsotropic (fun ω => A ω i) μ) →
    (∀ i, NLAlib.IsSubgaussianVector (fun ω => A ω i) ⟨K ^ 2, sq_nonneg K⟩ μ) →
    ∀ t : ℝ, 0 ≤ t →
    let L := Real.log (Real.exp 1 * K)
    GaussianSingularValueTails μ A (√m - K * √n - α * K * L - β * K * √L * t)
      (√m + K * √n + γ * K * L + δ * K * √L * t) t

def GeneralSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  ∀ K : ℝ, 1 ≤ K → TailBoundAt.{u} K α β γ δ

def UnitSingularValueTailBound (α β γ δ : ℝ) : Prop :=
    TailBoundAt.{u} 1 α β γ δ

end SubGaussian
```
<!-- canonical-statement:end -->

## Generated statement

[TeX](MainTheoremStatement.tex) and [PDF](MainTheoremStatement.pdf) present the
README's natural-language theorem and the current full Lean source. Regenerate
them with installed XeLaTeX:

```sh
python3 scripts/generate_theorem_tex.py
```

The command also refreshes the README's Lean block from the actual root file and
its constants table from `Constants.lean`. Use `--check` to detect drift without
writing files or running XeLaTeX. Compilation files stay in a temporary external
directory. `.latexmkrc` also supports local XeLaTeX builds without retained
auxiliary files. Generating documentation does not verify the proof.

## Credit and licence

[CONTRIBUTIONS.md](CONTRIBUTIONS.md) preserves Marcus Webb's initial contribution,
preceding work with Morgan Lynch-Davies, human/model roles, historical verification
and unresolved attribution assessments. The paper remains in preparation; cite
an exact repository revision using [CITATION.cff](CITATION.cff). Original work uses
the [Apache License 2.0](LICENSE); [LICENSING.md](LICENSING.md) records prior and
third-party terms.
