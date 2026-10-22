# Admissible constants

These records use Theorem S1.1 in [the supplementary materials](supplementary.pdf).
The accompanying paper, *Sharp tail bounds for the extreme singular values of
sub-Gaussian matrices*, by Marcus Webb and Morgan Lynch-Davies, is in preparation
and has no public version yet.

## Normalization and hypotheses

Let $S\in\mathbb R^{m\times n}$, $m\ge n\ge1$, have independent,
centred isotropic rows $X_i^T$:
$\mathbb E X_i=0$ and $\mathbb E X_iX_i^T=I_n$.
For a common $K\ge1$, require

$$
\mathbb E\exp(\lambda\langle X_i,v\rangle)
\le\exp(K^2\lambda^2\|v\|_2^2/2)
\quad(\lambda\in\mathbb R,\ v\in\mathbb R^n).
$$

Rows may have different distributions; coordinates within a row may be
dependent. All logarithms are natural. Put $L=\log(eK)$. For every $t\ge0$,

$$
\mathbb P\{\sigma_{\min}(S)\le\sqrt m-K\sqrt n
 -\alpha KL-\beta K\sqrt L\,t\}\le e^{-t^2/2},
$$
$$
\mathbb P\{\sigma_{\max}(S)\ge\sqrt m+K\sqrt n
 +\gamma KL+\delta K\sqrt L\,t\}\le e^{-t^2/2}.
$$

Use all $n$ singular values, including zeros. The events are non-strict.
Preserve $n=1$, $t=0$, rank deficiency and nonpositive lower thresholds.

## Baseline results

| Record | Regime | Exact quartet $(\alpha,\beta,\gamma,\delta)$ | Evidence |
|---|---|---|---|
| [baseline-general](contributions/records/baseline-general.json) | Every $K\ge1$ | $(96/25,79/50,47/20,3/2)$ | Hybrid Lean/Python |
| [baseline-one](contributions/records/baseline-one.json) | $K=1$ | $(33/25,28/25,58/25,\sqrt2)$ | Hybrid Lean/Python |

The general quartet also applies at $K=1$. The decimal displays are
`(3.84, 1.58, 2.35, 1.5)` and `(1.32, 1.12, 2.32, sqrt(2))`.
These baseline records remain permanently. Their local verification, observed
on 20 October 2026, is documented in
[VERIFICATION_REPORT.md](lean/VERIFICATION_REPORT.md); it has no public release
identifier yet.

Lean proves the analytic theorem conditional on `FinalCertificateConditions`.
External exact Python arithmetic checks its finite conditions; it supplies no
Lean proof terms. Source hashes detect drift and do not establish semantic
correspondence by themselves. Verification does not establish novelty or priority.

## Reporting an improvement

State the entire resulting quartet and regime, identifying changed entries and
reused proofs. Preserve the hypotheses, leading terms, failure probability and
range of $t$. A different normalization or restricted theorem needs an
explicitly identified statement rather than a silent replacement of these bounds.

A smaller $\alpha$ with a larger $\beta$, or a smaller $\gamma$ with a
larger $\delta$, may be a useful tradeoff. Keep both admissible pairs and
describe their use. Do not combine the smallest coordinates from different
pairs unless their simultaneous validity is proved. The registered Lean result
and certificate evidence must justify the entire claimed quartet.

New accepted results will be added here with a contribution ID, proof and
verification links. Proposals and numerical evidence belong in issues until
the full [contribution requirements](CONTRIBUTING.md) are met.
