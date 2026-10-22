# SubGaussianTailBounds

[![Verification](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/workflows/ci.yml/badge.svg?branch=main&event=push)](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/workflows/ci.yml)

Supplementary materials for **Sharp tail bounds for the extreme singular
values of sub-Gaussian matrices**, by Marcus Webb and Morgan Lynch-Davies.
The paper is **in preparation**; no public version is currently available.

This repository contains the detailed supplementary proof, exact arithmetic
certificates and Lean sources, and provides a permanent record of substantial
contributions to improvements in the constants $\alpha,\beta,\gamma,\delta$.

| Start here | |
|---|---|
| **Read the supplement** | [View PDF](supplementary.pdf) · [Download PDF](https://github.com/marcusdavidwebb/SubGaussianTailBounds/raw/refs/heads/main/supplementary.pdf) · [LaTeX source](supplementary.tex) |
| **Understand the bounds** | [Theorem, hypotheses and exact constants](CONSTANTS.md) |
| **Reproduce the checks** | [Python quickstart](#quickstart) · [Lean setup](lean/README.md#verify) · [Hosted verification](lean/README.md#verification-on-github) |
| **Contribute** | [Contribution guide](CONTRIBUTING.md) · [Ask a question or report a problem](https://github.com/marcusdavidwebb/SubGaussianTailBounds/issues/new/choose) |

## Current results

The pair $(\alpha,\beta)$ controls the offset and tail-dependent correction
for the smallest singular value; $(\gamma,\delta)$ does the same for the
largest singular value. Smaller values give tighter bounds under the same
hypotheses. $K$ is the sub-Gaussian parameter in the stated MGF normalization.

| Regime | α | β | γ | δ |
|---|---:|---:|---:|---:|
| Every $K\ge1$ | 3.84 | 1.58 | 2.35 | 1.5 |
| $K=1$ | 1.32 | 1.12 | 2.32 | $\sqrt2$ |

See [CONSTANTS.md](CONSTANTS.md) for the tail inequalities, precise MGF
normalization and hypotheses, exact values, and treatment of tradeoffs.

Both baseline quartets have **hybrid Lean/Python verification**. Lean proves
the analytic implication conditional on explicit finite rational certificates;
Python checks those certificates externally. This is not an unconditional
kernel proof of the numerical certificate bundle. See the
[verification report](lean/VERIFICATION_REPORT.md) and
[provenance and limitations](docs/PROVENANCE.md).

## Quickstart

To check the numerical certificates, use Git and **Python 3.11 or later**.
The checkers use only the Python standard library; Lean is not needed for
this step. Leave Python assertions enabled (no `-O` or `PYTHONOPTIMIZE`).

```sh
git clone https://github.com/marcusdavidwebb/SubGaussianTailBounds.git
cd SubGaussianTailBounds
python3 --version
./lean/check_certificates.sh
```

Successful execution ends with:

```text
PASS: original exact-arithmetic checker and all eleven finite interfaces.
```

For the full hybrid verification, configure the
[pinned external Lean environment](lean/README.md#pinned-environment-and-storage),
then run:

```sh
./lean/check_hybrid.sh
```

Without an existing Lean installation, follow the
[hosted verification guide](lean/README.md#verification-on-github).
The [Actions page](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/workflows/ci.yml)
shows current runs and their downloadable logs, generated theorem targets and
built PDF. A pending or failed run is not successful verification. The badge
above tracks `main`; historical local results are recorded separately in the
[verification report](lean/VERIFICATION_REPORT.md) and
[repository preparation record](docs/REPOSITORY_VALIDATION.md).

Build the supplementary document with an existing LaTeX installation
as described in the [document build guide](docs/BUILDING.md):

```sh
./scripts/build_supplement.sh
```

Lean 4.19.0 and the locked Mathlib revision are preserved. Dependencies and
compiled Lean outputs belong in a separate workspace, outside this source
checkout. Local verification does not silently install or update dependencies.

## Contribute

Start with [CONTRIBUTING.md](CONTRIBUTING.md). Ideas, numerical searches and
questions can be discussed in [issues](https://github.com/marcusdavidwebb/SubGaussianTailBounds/issues/new/choose).
Documentation and maintenance fixes have their own route in the guide.
A pull request claiming better constants
must include the readable proof, Lean result for the claimed constants,
applicable exact certificates/checker correspondence, and history updates.
**A PDF or natural-language proof alone cannot pass the improvement gate.**
The complete hybrid regression checks run for every pull request.

Accepted substantial work is recorded in [CONTRIBUTIONS.md](CONTRIBUTIONS.md)
and the machine-readable [contribution records](contributions/records/).
Superseded results remain in the history. Mathematical credit and future
paper authorship are separate decisions.

The original supplement lists Marcus Webb as sole author and discloses that
the entire document was generated by AI without direct input from him; he takes
full responsibility. The paper authors' preceding mathematical work and the
roles and limitations of the tools are preserved in Section S2 and the
[provenance note](docs/PROVENANCE.md).

## Citation and publication

Use [CITATION.cff](CITATION.cff) for this collection. Cite the paper as
**in preparation**, by Marcus Webb and Morgan Lynch-Davies, until an actual
public version is supplied. Identify the exact repository commit or
[release](https://github.com/marcusdavidwebb/SubGaussianTailBounds/releases)
you used, together with relevant contribution IDs. For example, replace the
bracketed value in this citation with `git rev-parse HEAD` from your checkout:

> Webb, Marcus. *SubGaussianTailBounds: supplementary materials and hybrid
> verification*. GitHub, commit [full commit SHA].
> https://github.com/marcusdavidwebb/SubGaussianTailBounds

Repository releases and publication of the accompanying paper are separate.
No DOI or public paper URL has been assigned here.

The project's original code, proofs and documentation are licensed under the
[MIT License](LICENSE). Third-party material retains its own terms; see
[LICENSING.md](LICENSING.md). Maintainers can find repository settings,
verification and release procedures in the
[maintainer guide](docs/LAUNCH_CHECKLIST.md).
