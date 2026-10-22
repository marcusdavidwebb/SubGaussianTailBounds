# Completed hybrid verification

This is the historical validation record. Its commands and source inventory
describe the original paper checkout. Current portable reproduction instructions
are in [README.md](README.md); later packaging validation is recorded separately
in [REPOSITORY_VALIDATION.md](../docs/REPOSITORY_VALIDATION.md).

**Date:** 20 October 2026. **Status:** all 24 sections complete; reverified after
the approved retirement of the earlier standalone theorem.

The current supplementary theorem is proved in Lean **conditional on explicit
finite rational certificates**, checked externally by exact Python arithmetic.
Both advertised quartets are retained:

| Case | α | β | γ | δ |
|---|---:|---:|---:|---:|
| General K≥1 | 3.84 | 1.58 | 2.35 | 1.5 |
| K=1 | 1.32 | 1.12 | 2.32 | √2 |

The public API is in [KL/Theorem.lean](SingularValueBounds/KL/Theorem.lean):

- `SingularValueBounds.KL.singular_value_tails_general_of_certificates`
- `SingularValueBounds.KL.singular_value_tails_one_of_certificates`
- `SingularValueBounds.KL.theorem_explicit_constants_of_certificates`

The joint theorem proves `TheoremKL μ generalConstants ∧ TheoremKLOne μ`
from [FinalCertificateConditions](SingularValueBounds/KL/Certificates/Final.lean).
Its eleven fields contain finite rational conditions; none supplies a row
estimate, pathwise budget or other analytic assertion. All actual analytic
inputs are proved internally. The statement allows independent, nonidentically
distributed centred isotropic rows with dependent coordinates, the original
directional MGF assumption, m≥n≥1 and t≥0. Both tail events are non-strict;
all Gram singular values, including zeros, are included.

The Python programs supply no Lean proof terms. Their exact-arithmetic
execution and correspondence to the finite Lean predicates are part of the
hybrid trust boundary. Independent source reviews checked that correspondence;
source digests detect drift and are not compiler-generated proof exports.
This is not an unconditional kernel proof of the finite certificate bundle.

## Reproduction

From the paper repository, with the existing pinned central setup:

```sh
./supplementary/lean/check_hybrid.sh
```

The script rejects optimized Python execution, builds and audits Lean, executes
the unchanged original `supplementary/check_main_constants.py`, and runs all
eleven interface checkers. The field-to-checker map and proof-to-paper map are
in [FORMALISATION_PLAN.md](FORMALISATION_PLAN.md). Sources remain Git-ignored;
dependencies and compiled outputs remain outside the paper under
`~/Lean/SingularValueBounds/`. No dependency or toolchain was installed or
upgraded. The public repository and release identifiers remain placeholders.

Recorded environment:

- Lean 4.19.0, commit `6caaee842e94`, `arm64-apple-darwin23.6.0`.
- Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` (`v4.19.0`).
- Lake `5.0.0-6caaee8`.
- Python 3.14.0, with optimization disabled.

## Validation observed

The post-cleanup aggregate run began at **15:04:52 UTC** and successful exit was
observed at **15:09:47 UTC**, on 20 October 2026.

| Check | Result |
|---|---|
| All 147 KL modules and 32 shared supporting modules | Build passed |
| Complete theorem audit | 3,224 targets, 53,478 visited constants |
| Transitive axiom union | Only `propext`, `Classical.choice`, `Quot.sound` |
| Final three public results | Separate `#print axioms` reports passed |
| Retained 3,015-target checkpoint and complete KL import coverage | Passed |
| Original exact arithmetic checker | Passed, source unchanged |
| Eleven finite-interface runners | All passed |

The inventory contains all 3,200 KL theorem declarations, including generated
equations and structure facts, and 24 shared principal targets. The audit uses
Lean's unchanged transitive axiom collector with a shared visited set. Its
report parser checks completeness, the axiom allowlist, retained targets and
source/import coverage. No `sorry`, added axioms or native-oracle proofs are
used. The runner's optimization guard rejects `PYTHONOPTIMIZE=1`; it and the
parser's completeness checks are included in the current verified runner.

Original checker SHA-256:
`5eb67ea33c73efda48a19fb930345bca2990e6efce660d33960504dad5d3b974`.

Aggregate successful log SHA-256:
`f1f031e88d8cf4967938eb66ffae85f17b659cb321c61853ed2f8eeff7b92ab5`.
The log was retained locally at `/tmp/supplementary-cleanup-hybrid.log`; this
temporary path is not a published archive. The checked source inventory is
recorded in [verification_manifest.json](verification_manifest.json).

After this verification, Section S2 of the supplement was expanded on
20 October 2026 to explain the formalisation and its trust boundary. The entire
text preceding S2, the bibliography trailer, and all Lean and Python sources
are unchanged. The LaTeX document was rebuilt and the changed pages reviewed.
The manifest records this editorial update and its revised document hash
separately; the formal validation timestamp above is unchanged.

Section 2.2 of the main paper was subsequently shortened to an attributed
report of Jeong et al.'s sparse example and its elementary separate-tail
consequences. All other main-paper sections, the formal theorem and its proof,
and all Lean/Python sources are unchanged. The main paper and supplement were
rebuilt. This sharpness discussion is outside the Lean theorem's scope; the
manifest records the manuscript revision separately from formal validation.

Section 2.1 was likewise shortened to an attributed explanation of the
established selector construction, Gaussian spectral law and their elementary
consequences. The fixed-K critical-window example was retained, and the removed
proposition's sole external reference was redirected to the subsection.
All other manuscript text and all Lean/Python sources are unchanged. Both
LaTeX documents were rebuilt; the manifest records this further manuscript
update separately from formal validation.

## Approved cleanup and historical validation

The user requested retirement of the standalone earlier `n^(1/6)` theorem.
Its 16 exclusive modules and 17 audit targets were removed; its former public
results `SingularValueBounds.theorem11` and
`SingularValueBounds.singular_value_tails` are no longer exported. The 32
older modules needed by the current proof remain. All 147 KL sources,
the retained shared modules, exact checkers and dependency pins are unchanged.
Only the umbrella imports, audit inventory and target checkpoint changed.

The checkpoint now retains all 2,991 KL names and 24 shared targets from its
former 3,032 entries. Independent review confirmed that exactly the 17 retired
targets were removed. The manifest records the retired source hashes, exact
target names and preceding validation metrics; this is explicit retirement,
not silent weakening of the audit.

The original completion run at **14:50:46 UTC** audited 3,241 targets through
53,669 constants, including the earlier theorem. It also passed all exact
checkers. Those figures are historical; the current inventory is reported
above. Its aggregate log digest is preserved in the manifest's validation
history. All original measured development timings remain in the completed
plan. Obsolete planning prose and generated metadata/build debris were removed;
archived manuscript sources, PDFs and current SyncTeX remain.

## Timing and correspondence

The final P12/P24 batch ran from **14:24:48 UTC** through observed hybrid
validation at **14:50:46 UTC**: **26.0 minutes**. Three GPT-6.1 Sol Ultra workers
and the coordinator worked in parallel. These assisted measurements are not
isolated single-worker benchmarks. All projected remaining minutes are zero.
Subsequent documentation and LaTeX work are excluded from that interval.

The proof follows the supplement's argument. The mixed-cap budget uses a
clipped inverse and the Fubini/Young inverse-integral identity to justify the
calculation at profile breakpoints, without assuming inverse differentiability
there. Both strict scalar cost bounds and the one-dimensional case are proved
in Lean. No new numerical premise was required for these integrals.

The main paper, supplement and cover letter disclose the completed hybrid
scope. Their constants and hypotheses are unchanged. The archived variational
manuscript remains in `OLD/`; its standalone Lean theorem is retired.
This verification does not resolve attribution or
novelty questions retained in the original paper checkout's `LITERATURE_AUDIT.md`;
see [the public provenance note](../docs/PROVENANCE.md).
