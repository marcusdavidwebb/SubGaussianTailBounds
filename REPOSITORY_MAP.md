# Repository map

Start with the [README](README.md) for the theorem and the single verification
command. This map explains every maintained folder, Python file and Markdown
file, including GitHub's hidden configuration. It is a source inventory, not a
record of a new Lean verification run.

| Your purpose | Reading path |
|---|---|
| Understand the mathematics | [Root statement](MainTheoremStatement.lean) → [public results](lean/SingularValueBounds/Canonical/Results.lean) → their imported proofs |
| Run the complete check | [Lean setup](lean/README.md) → `./lean/verify.sh` |
| Review a PR | [Contribution contract](CONTRIBUTING.md) → [verification and review](docs/VERIFICATION.md) |
| Understand the checking tools | The workflow and Python/Lean tool tables below |
| Find credit and earlier evidence | [Contributions](CONTRIBUTIONS.md), [provenance](docs/PROVENANCE.md), [verification history](docs/HISTORY.md) |

The mathematics lives in `MainTheoremStatement.lean` and
`lean/SingularValueBounds/`. Operational Python lives in `scripts/`; Lean
checking programs and templates live in `lean/Verification/`; regression tests
live in `tests/`. Python prepares and schedules checks. Lean checks the proofs.

## How the complete check fits together

```text
lean/verify.sh
  ├─ check_canonical_statement.py   immutable source and README copy
  ├─ generate_lean_acceptance.py    trusted constants and exact checking targets
  ├─ lean/setup.sh
  │    └─ configure_lean.py         installed tools and external workspace
  ├─ build_lean_modules.py          bounded compilation, dependencies first
  └─ replay_lean_modules.py         independent kernel replay, exact types,
                                   axioms and complete report/source coverage
```

All five `.py` paths above are under `scripts/`. The sixth helper,
`check_contributions.py`, performs administrative source/history checks.
The verifier uses the Lean programs and templates in `lean/Verification/`;
generated source and compiled outputs stay in the external workspace.

GitHub CI runs contribution checks and administrative regression tests. It does
not build or replay Lean proofs. Its workflow contains small inline Python
status writers, including the final live PR head/base freshness check.
`lean/verify.sh` does not run the regression suite. Tests that invoke Lean are
opt-in locally and disabled in CI.

## Every folder

### Repository and supporting folders

| Folder | Purpose |
|---|---|
| [Repository root](.) | Canonical statement, entry-point documents, contribution and licensing records, citation metadata and agent instructions. |
| [.github/](.github/) | Review configuration, issue forms, PR template and administrative CI. |
| [.github/ISSUE_TEMPLATE/](.github/ISSUE_TEMPLATE/) | Correctness-report, improvement and question forms; `config.yml` also permits blank issues. |
| [.github/workflows/](.github/workflows/) | One administrative workflow, `ci.yml`, with isolated status-reporting jobs. |
| [docs/](docs/) | Verification policy, dated history and provenance. |
| [lean/](lean/) | Project configuration, setup/full-verification launchers, library umbrella and the two source trees below. |
| [lean/Verification/](lean/Verification/) | Three Lean checking programs and two audit templates; see their individual roles below. |
| [scripts/](scripts/) | Six operational Python helpers for setup, compilation, verification and administration. |
| [tests/](tests/) | Regression tests for those tools, including optional Lean fixtures. |

### Mathematical library folders

Paths in this table are relative to `lean/SingularValueBounds/`. Counts are
**Lean files directly in that folder**, excluding its subfolders.

| Folder | Direct files | Purpose |
|---|---:|---|
| [lean/SingularValueBounds/](lean/SingularValueBounds/) | 0 | Container for the 529 maintained mathematical modules. The complete-library umbrella is the sibling file `lean/SingularValueBounds.lean`. |
| [Canonical/](lean/SingularValueBounds/Canonical/) | 10 | The public interface: general and unit baseline proofs, adapters to the actual root statement, NLA-lib equivalence bridges, monotonicity, current results/comparisons and exact accepted constants. |
| [Concentration/](lean/SingularValueBounds/Concentration/) | 1 | Integration of a new independent random row against the preceding state, using independence and Fubini. |
| [Core/](lean/SingularValueBounds/Core/) | 5 | Shared row assumptions, constants, matrix algebra/measurability and scalar tail-to-moment estimates. |
| [KL/](lean/SingularValueBounds/KL/) | 3 | Internal statement and finite-condition interfaces, row-by-row transfer and analytic theorem assembly. Most of this proof family is in its subfolders. |
| [KL/Barrier/](lean/SingularValueBounds/KL/Barrier/) | 20 | Spectral shifts, the measurable adaptive row process, and the accumulated correction budgets used for lower and upper bounds. |
| [KL/Certificates/](lean/SingularValueBounds/KL/Certificates/) | 73 | Concrete finite numerical proofs and shared arithmetic/polynomial lemmas, plus modules assembling the families below. “Certificate” here means a Lean proof, not an external result accepted on trust. |
| [KL/Lower/](lean/SingularValueBounds/KL/Lower/) | 42 | Lower-tail/smallest-singular-value analysis: moments, covariance, spectral profiles, parameter coverage, scalar costs and the final lower-tail transfer. |
| [KL/Upper/](lean/SingularValueBounds/KL/Upper/) | 75 | Upper-tail/largest-singular-value analysis: determinant and decay-rate estimates, upper means, entropy integration, moment-generating functions and the finite-condition interfaces. |
| [KL/Weighted/](lean/SingularValueBounds/KL/Weighted/) | 4 | Weighted entropy, Gaussian determinant comparison and integration lemmas supporting the KL argument. |
| [Main/](lean/SingularValueBounds/Main/) | 3 | Shared internal singular-value notation, passage from spectral bounds to singular values, and parameter optimization. Despite the historical name, the current public results are in `Canonical/Results.lean`. |
| [QuadraticForms/](lean/SingularValueBounds/QuadraticForms/) | 6 | Integrability, means and higher moments of quadratic forms, using isotropy, sub-Gaussian assumptions and Gaussian comparison. |
| [Scalar/](lean/SingularValueBounds/Scalar/) | 4 | Reusable Cauchy–Schwarz, exponential and scalar tail/second-moment estimates. |
| [Shifts/](lean/SingularValueBounds/Shifts/) | 7 | Bounds for one-row lower/upper spectral shifts, including root constructions, determinants and rank-one matrix updates. |
| [Spectral/](lean/SingularValueBounds/Spectral/) | 4 | Resolvent and potential definitions, scalar roots, and construction/continuity of variational spectral bounds. |
| [SpectralConcentration/](lean/SingularValueBounds/SpectralConcentration/) | 2 | Row independence for Gram matrices and Chernoff optimization turning moment-generating-function bounds into tail probabilities. |

The root statement imports NLA-lib directly.
[Canonical/NLARows.lean](lean/SingularValueBounds/Canonical/NLARows.lean) relates
its predicates to the original coordinate and MGF assumptions;
[Canonical/NLASingularValues.lean](lean/SingularValueBounds/Canonical/NLASingularValues.lean)
identifies its singular values with the preceding extrema, including zeros.
[Canonical/TailEquivalence.lean](lean/SingularValueBounds/Canonical/TailEquivalence.lean)
relates the real-valued and extended-nonnegative-real probability bounds under a
probability measure.
[Canonical/StatementEquivalence.lean](lean/SingularValueBounds/Canonical/StatementEquivalence.lean)
assembles the equivalence for both canonical propositions and all sample-space
universes.

### Finite-proof subfolders

Paths here are relative to `lean/SingularValueBounds/KL/Certificates/`.
Again, counts exclude subfolders.

| Folder | Direct files | Purpose |
|---|---:|---|
| [ConcreteEndpointMeanPolynomials/](lean/SingularValueBounds/KL/Certificates/ConcreteEndpointMeanPolynomials/) | 60 | Polynomial identities and coefficient-sign proofs for the unit-case upper-mean calculation. |
| [ConcreteGeneralMeanEntropyRows/](lean/SingularValueBounds/KL/Certificates/ConcreteGeneralMeanEntropyRows/) | 19 | Entropy evaluations and error margins for the 1,330 general upper-mean witnesses, divided into blocks of 70 rows. |
| [ConcreteGeneralMeanRows/](lean/SingularValueBounds/KL/Certificates/ConcreteGeneralMeanRows/) | 19 | Polynomial identities and signs for the same general upper-mean cells. These are different obligations from the entropy checks above. |
| [ConcreteMajorants/](lean/SingularValueBounds/KL/Certificates/ConcreteMajorants/) | 6 | Polynomial upper-bound certificates for determinant estimates, with the largest family split further below. |
| [ConcreteMajorants/Row5/](lean/SingularValueBounds/KL/Certificates/ConcreteMajorants/Row5/) | 11 | Ten blocks covering 70 parameter-region certificates for majorant 5, plus their shared polynomial identity. |
| [ConcretePlateauScalars/](lean/SingularValueBounds/KL/Certificates/ConcretePlateauScalars/) | 3 | Exact scalar inequalities for concentrated-spectrum plateau cases in the lower-tail argument. |
| [ConcreteRates/](lean/SingularValueBounds/KL/Certificates/ConcreteRates/) | 15 | Polynomial certificates for the extended upper-tail decay rates. |
| [EndpointEntropyDecayRows/](lean/SingularValueBounds/KL/Certificates/EndpointEntropyDecayRows/) | 12 | Proved exponential-decay tables and weighted running sums reused in unit-case entropy evaluations. |
| [EndpointEntropyLogRows/](lean/SingularValueBounds/KL/Certificates/EndpointEntropyLogRows/) | 32 | Exact rounded-logarithm values on the shared endpoint grid, split into manageable blocks. |
| [EndpointMeanEntropyRows/](lean/SingularValueBounds/KL/Certificates/EndpointMeanEntropyRows/) | 60 | Entropy bounds for unit-case upper-mean boxes, sharing corner evaluations between adjacent boxes. These complement the separate polynomial proofs. |
| [EndpointSmallEntropyRows/](lean/SingularValueBounds/KL/Certificates/EndpointSmallEntropyRows/) | 5 | Entropy bounds for the small-shape part of the unit-case calculation. |
| [GeneralMeanDecayTables/](lean/SingularValueBounds/KL/Certificates/GeneralMeanDecayTables/) | 28 | Shared exact rounded-exponential evaluations reused by the general entropy rows, avoiding repeated arithmetic proofs. |

The numerous row/block files divide expensive exact computations into smaller
compilation and replay units. Combining them would reduce file count, but would
not automatically reduce mathematical work and could increase peak memory.
Shared logarithm and decay tables factor repeated work rather than provide
alternative versions of the same overall proof.

## Every Python file

### Six operational helpers

| File | Responsibility |
|---|---|
| [scripts/configure_lean.py](scripts/configure_lean.py) | Reuse installed Lean and exact clean dependency revisions; select this checkout's external workspace and resolve Lake configuration there. Refuse another checkout's workspace or an unrecognized existing build. Never install or download dependencies. |
| [scripts/check_canonical_statement.py](scripts/check_canonical_statement.py) | Check the immutable root digest, reject source/compiled shadows and symlinks, and compare the README's full annotated copy. Optional refresh mode updates only that copy. |
| [scripts/generate_lean_acceptance.py](scripts/generate_lean_acceptance.py) | Validate source/configuration boundaries; prepare independent constants copies, expected types and comparison obligations; fill the Lean audit templates in the external workspace. Generation alone proves nothing. |
| [scripts/build_lean_modules.py](scripts/build_lean_modules.py) | Read imports through Lean's parser, check content-based Lake traces, and compile stale modules in dependency order with bounded parallelism. |
| [scripts/replay_lean_modules.py](scripts/replay_lean_modules.py) | Schedule trusted kernel replay; check artifact hashes, independent inventories, exact canonical types, allowed axioms and complete final report/source/umbrella coverage. |
| [scripts/check_contributions.py](scripts/check_contributions.py) | Run administrative source/input checks and require contribution-history updates for proof changes. Used by CI; it does not establish correctness or novelty. |

### Regression tests

Test discovery runs these files separately from `lean/verify.sh`. An opt-in
fixture invokes the existing Lean installation only when
`SVB_LEAN_TEST_WORK_DIR` names an external workspace.

| File | What it protects | Uses Lean? |
|---|---|---|
| [tests/test_build_lean_modules.py](tests/test_build_lean_modules.py) | Dependency order, concurrency, cycle/failure handling and content-based freshness even when source size/timestamps are preserved. | Optional freshness fixture; otherwise simulated work. |
| [tests/test_canonical_statement.py](tests/test_canonical_statement.py) | Root immutability, absent/moved/symlinked sources, shadows and exact README copying. | No. |
| [tests/test_ci_boundaries.py](tests/test_ci_boundaries.py) | Administrative-only CI, status-writer isolation, trusted preflight and rejection of failed/skipped jobs or stale revisions. | No; HTTP responses are simulated. |
| [tests/test_configure.py](tests/test_configure.py) | Installed dependency reuse, pins, dirty checkouts, workspace ownership and actual root-source configuration. | No; uses local Git fixtures and simulated tool responses. |
| [tests/test_contributions.py](tests/test_contributions.py) | Source/history rules, permitted replacements, equal constants, exact base identifiers and rejection of tampered inputs. | No. |
| [tests/test_lean_acceptance.py](tests/test_lean_acceptance.py) | Generated obligations and rejection of wrong types/universes, extra premises, forged declarations, hidden axioms, substituted snapshots and regressed constants. | Administrative tests plus optional Lean fixtures. |
| [tests/test_module_replay_integration.py](tests/test_module_replay_integration.py) | Real compiled-module replay: dependencies, forged proofs, trusted-name collisions, duplicate equation theorems, unsafe premises and transitive axioms. | Opt-in Lean fixtures. |
| [tests/test_replay_lean_modules.py](tests/test_replay_lean_modules.py) | Replay scheduling, changed artifacts, allowed axioms, required targets and complete source/module/report coverage. | No; uses simulated reports and replay operations. |
| [tests/test_snapshot_source.py](tests/test_snapshot_source.py) | The pinned Lean parser's acceptance of stable constants sources and rejection of tactics, hooks, scope escapes and unstable definitions. | Opt-in Lean fixtures. |

These tests protect the verifier against regressions. Their small examples do
not prove the singular-value bounds, and consolidating test files would not
speed up the full proof check.

## Every Markdown file

| File | Purpose |
|---|---|
| [README.md](README.md) | Theorem, verification command and reading path; contains the checked full copy of the canonical statement. |
| [REPOSITORY_MAP.md](REPOSITORY_MAP.md) | This inventory: where each part lives and why it exists. |
| [AGENTS.md](AGENTS.md) | Coding-assistant instructions for immutability, mathematical requirements, verification, storage and review. |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Mathematical acceptance contract, non-increasing constants, submission process, research standards and attribution. |
| [CONTRIBUTIONS.md](CONTRIBUTIONS.md) | Credit and development history, beginning with Marcus Webb's contribution covering both regimes. Contribution preflight checks required updates. |
| [LICENSING.md](LICENSING.md) | Scope of the MIT licence and preservation of third-party terms; `LICENSE` contains the legal text. |
| [lean/README.md](lean/README.md) | How to run verification: pinned installed dependencies, external storage, environment overrides and memory/concurrency settings. |
| [docs/VERIFICATION.md](docs/VERIFICATION.md) | Before-merge procedure, 22-declaration interface, independent checking guarantees and administrative CI policy. |
| [docs/HISTORY.md](docs/HISTORY.md) | Dated validation results, resource measurements, outstanding verification and links to historical records in Git. |
| [docs/PROVENANCE.md](docs/PROVENANCE.md) | Preceding human mathematics, model/tool roles, responsibility and unresolved attribution/novelty assessments. |
| [.github/PULL_REQUEST_TEMPLATE.md](.github/PULL_REQUEST_TEMPLATE.md) | Submission prompts for scope, evidence, attribution, exact revisions and policy changes; completing it does not run checks. |

## Lean checking programs and templates

All five files live in `lean/Verification/`. They check the formalization; the
mathematical library is in the separate `lean/SingularValueBounds/` tree.

| File | Responsibility |
|---|---|
| [SourceImports.lean](lean/Verification/SourceImports.lean) | Read source import headers through Lean's parser for the build scheduler, without elaborating proof declarations. |
| [SnapshotSource.lean](lean/Verification/SnapshotSource.lean) | Restrict accepted-constants sources to stable declarative syntax using the pinned Lean/Mathlib parser. |
| [ModuleReplay.lean](lean/Verification/ModuleReplay.lean) | Independently replay compiled declarations through the kernel and produce declaration inventories and axiom reports. |
| [CanonicalAudit.lean.in](lean/Verification/CanonicalAudit.lean.in) | Template for the separate exact-type auditor: load candidate compiled data with extensions disabled and compare public results against independently prepared types and universe counts. |
| [ElaborationAudit.lean.in](lean/Verification/ElaborationAudit.lean.in) | Template for the axiom and checked-flag checks at the end of elaborating the generated acceptance obligations. It supplements the later independent audit. |

The generator fills these templates with the required target names and writes
the generated Lean sources outside the repository. The `.lean.in` files are
reviewable source templates, not separately compiled library modules.

## Other files that connect the parts

| File | Role |
|---|---|
| [MainTheoremStatement.lean](MainTheoremStatement.lean) | Authoritative target propositions. Preserve its exact root location, name and bytes, including imports, comments and universes. Never edit, delete, rename, relocate, replace or shadow it; there is no formatting or maintenance exception. |
| [lean/SingularValueBounds.lean](lean/SingularValueBounds.lean) | Umbrella importing every maintained library module for complete verification coverage. |
| [lean/verify.sh](lean/verify.sh) | Single complete local verification command coordinating the Python helpers and Lean programs. |
| [lean/setup.sh](lean/setup.sh) | Small wrapper around `scripts/configure_lean.py`; workspace setup alone does not check proofs. |
| [lean/lean-toolchain](lean/lean-toolchain) | Lean 4.33.1 pin, matching the imported NLA-lib version. |
| [lean/lakefile.toml](lean/lakefile.toml) | Lake configuration template: libraries, actual source roots and compiler settings. |
| [lean/lake-manifest.json](lean/lake-manifest.json) | Exact dependency revisions; configuration supplies the external package path. |
| [.github/workflows/ci.yml](.github/workflows/ci.yml) | Administrative checks and isolated commit-status reporting. |
| [.github/CODEOWNERS](.github/CODEOWNERS) | Names Marcus Webb as code owner; branch settings determine required review. |
| [LICENSE](LICENSE) | MIT licence text. |
| [CITATION.cff](CITATION.cff) | Citation metadata distinguishing the repository from the in-preparation paper. |
| [.gitignore](.gitignore) and [lean/.gitignore](lean/.gitignore) | Exclude caches, compiled objects and editor metadata. |

## Proof coverage and further simplification

The umbrella imports all 529 library modules. A static traversal of ordinary
source `import` lines from `SingularValueBounds.Canonical.Results` reaches 526.
The three remaining modules expose additional assemblies or helper APIs:

| Module | Present purpose |
|---|---|
| [KL/Certificates/ConcreteFinal.lean](lean/SingularValueBounds/KL/Certificates/ConcreteFinal.lean) | Bundle all eleven concrete finite-condition families as `finalCertificateConditions`. |
| [KL/Certificates/EndpointEntropySum.lean](lean/SingularValueBounds/KL/Certificates/EndpointEntropySum.lean) | Integer range-sum evaluator and proofs equating it to finite sums. |
| [KL/Lower/ProfileIntegralRegularity.lean](lean/SingularValueBounds/KL/Lower/ProfileIntegralRegularity.lean) | Additional profile-integral regularity and sine-substitution lemmas. |

This source-import survey is not declaration-level dead-code analysis or
approval to delete these files. Changes require review of their API and complete
Lean verification. The row/block splitting discussed above serves memory and
reuse; reducing file count alone does not simplify the mathematical argument.

## Outside the maintained source tree

`.git/` is Git's local database. Ignored `__pycache__/` and editor directories
are generated metadata. Neither belongs to the proof inventory.

Toolchains live in `~/.elan`. This project's Lean 4.33.1 dependencies, outputs,
generated checking modules and logs live in its own
`~/Lean/SubGaussianTailBounds/<source-path-digest>/nla-4.33.1/` workspace.
NLA-lib and Mathlib are stored under that workspace's `.lake/packages/`, with
no dependency tree or dependency symlink in this checkout. The older
`~/Lean/SingularValueBounds/.lake/packages/` tree is unchanged and not used by
this setup. The macOS Mathlib cache remains in `~/Library/Caches/mathlib`.
See [Lean setup](lean/README.md) for exact pins and current validation scope.
The removed supplement and retired tools remain accessible through Git history.
