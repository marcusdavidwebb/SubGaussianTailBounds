# Repository map

This is a guide to what is present and why, to help assess further simplification.
It describes the source tree after the Lean-only cleanup on 29 October 2026
(`c05c39c`), plus this file. It covers **all 36 source-controlled subfolders,
all 19 Python files, and all 11 Markdown files**, including hidden GitHub files.
Git's own database and external build directories are explained separately.

The repository contains four kinds of material:

- **Mathematics:** the canonical statement and 525 maintained Lean library modules.
- **Verification:** setup, controlled compilation, independent kernel replay,
  exact theorem-interface checks and report validation.
- **Regression tests:** tests of that verification machinery, separate from the
  tail-bound proofs themselves.
- **Documentation and GitHub administration:** instructions, credit, history,
  contribution forms and lightweight CI.

Python prepares and schedules checks; Lean checks the mathematical proofs.
This inventory was prepared by reading files, without running Lean verification.

## How verification uses the files

The main dependencies of the local command are:

```text
lean/verify.sh
  ├─ scripts/check_canonical_statement.py   root source and README integrity
  ├─ scripts/generate_lean_acceptance.py    inputs, constants and exact Lean targets
  ├─ lean/setup.sh → lean/configure.py     existing tools and external workspace
  ├─ Lean checking programs and generated expected-type/acceptance modules
  ├─ scripts/build_lean_modules.py         dependency-ordered compilation
  │    └─ lean/SourceImports.lean          Lean's parser reads import headers
  ├─ scripts/replay_lean_modules.py        independent dependency-ordered replay
  │    └─ lean/Acceptance/ModuleReplay.lean Lean kernel and axiom checks
  └─ lean/check_axiom_audit.py             complete report and source coverage
```

This is a dependency overview, not an exact execution transcript: some integrity
checks repeat, and `lean/Acceptance/SnapshotSource.lean` checks the standalone
constants sources before proof compilation. Generated checking modules stay in
the external workspace rather than becoming more repository files.

Administrative CI uses `scripts/ci_context.py`, `scripts/check_contributions.py`
and the administrative tests. Contribution checks reuse the Python input checks
in `generate_lean_acceptance.py`, which reuse `check_canonical_statement.py`.
CI does **not** run the proof build or replay. The workflow also contains two
small inline Python programs that announce and report its commit status; those
are in `.github/workflows/ci.yml`, not separate `.py` files.

`lean/verify.sh` does not run the regression suite. CI discovers its 112 test
methods but leaves `SVB_LEAN_TEST_WORK_DIR` empty: 76 administrative tests run,
while 36 tests that invoke Lean are skipped. Those 36 tests use small verification
fixtures; they are distinct from checking the full mathematical library.

## Every folder

### Repository and supporting folders

| Folder | What it contains and does |
|---|---|
| [Repository root](.) | The immutable canonical statement, main README, contribution and licensing documents, citation metadata, agent instructions and this map. |
| [.github/](.github/) | GitHub review configuration: `CODEOWNERS`, the PR template, issue forms and CI. This is repository administration, not mathematical proof. |
| [.github/ISSUE_TEMPLATE/](.github/ISSUE_TEMPLATE/) | Forms for correctness reports, proposed improvements and questions; `config.yml` also permits ordinary blank issues. |
| [.github/workflows/](.github/workflows/) | One workflow, `ci.yml`, for source/contribution checks and administrative tests, with separate status-reporting jobs. |
| [docs/](docs/) | Three human-facing documents: verification details, dated validation history and provenance. None is executed as a proof. |
| [lean/](lean/) | The Lean project configuration, setup and verification launchers, import parser, complete-library umbrella and the two subfolders below. Dependencies and compiled outputs are stored elsewhere. |
| [lean/Acceptance/](lean/Acceptance/) | Two Lean programs used by the verifier: constants-source syntax checking and independent compiled-module replay. They are checking machinery, rather than tail-bound proof modules. |
| [scripts/](scripts/) | Six Python helpers for building, replaying, preparing exact checks and administering source/CI checks. Each is described below. |
| [tests/](tests/) | Eleven Python regression-test files for the setup, source guards, CI, schedulers and Lean checking programs. They test the tools that verify the formalization. |

### Mathematical library folders

Paths in this table are relative to `lean/SingularValueBounds/`. Counts are
**Lean files directly in that folder**, excluding its subfolders.

| Folder | Direct files | Purpose |
|---|---:|---|
| [lean/SingularValueBounds/](lean/SingularValueBounds/) | 0 | Container for the 525 maintained mathematical modules. The complete-library umbrella is the sibling file `lean/SingularValueBounds.lean`. |
| [Canonical/](lean/SingularValueBounds/Canonical/) | 6 | The public interface: general and unit baseline proofs, adapters to the actual root statement, monotonicity, current results/comparisons and exact accepted constants. |
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

### Operational helpers

| File | What it does | Where it is used |
|---|---|---|
| [lean/configure.py](lean/configure.py) | Checks the installed Lean version and exact clean dependency revisions; selects a project-specific external workspace; writes resolved Lake configuration there. Reuses its own workspace and rejects paths owned by another checkout or unrecognized populated workspaces. It never installs or downloads dependencies. | Local verification, through `lean/setup.sh`. |
| [lean/check_axiom_audit.py](lean/check_axiom_audit.py) | Parses Lean's final audit report; rejects errors, forbidden axioms, duplicate/incomplete inventories, missing public targets and differences between source files, umbrella imports and audited modules. It validates the report, not mathematical proof terms. | End of local verification. |
| [scripts/check_canonical_statement.py](scripts/check_canonical_statement.py) | Checks the immutable root digest, rejects source/compiled shadows and symlinks, and compares the README's full annotated copy with the root. Its optional README-refresh mode changes only that copy. | Local verification and shared CI source checks; can also run alone. |
| [scripts/generate_lean_acceptance.py](scripts/generate_lean_acceptance.py) | Validates source/configuration boundaries and standalone constants; writes the expected types, comparison obligations, independent constants copies and Lean auditing program into the external workspace. Generated text alone proves nothing. | Local verification. CI imports only its Python input-checking functions. |
| [scripts/build_lean_modules.py](scripts/build_lean_modules.py) | Gets the import graph from Lean's parser, checks source-content build traces, and schedules stale builds with bounded parallelism and dependencies first. | Local verification; limits simultaneous compilation memory use. |
| [scripts/replay_lean_modules.py](scripts/replay_lean_modules.py) | Runs the trusted Lean worker to obtain inventories and the compiled import graph, schedules independent kernel replay, checks artifact hashes and report coverage, then invokes the exact canonical-type check. | Local verification; limits simultaneous replay memory use. |
| [scripts/check_contributions.py](scripts/check_contributions.py) | Reuses source/input checks, requires a real nonempty contribution history, and requires a history-file update when a diff changes maintained proof sources. It does not judge mathematical novelty or prove constants comparisons. | Administrative CI and optional manual contribution preflight. |
| [scripts/ci_context.py](scripts/ci_context.py) | Reads the GitHub event, checks the current PR head/base through the GitHub API, and supplies the exact comparison base to preflight. It does not compile Lean or post success statuses. | Administrative CI only. |

All eight operational helpers have current callers. The build and replay
schedulers cover different phases; the final report parser checks completion
and coverage after the Lean worker has performed the mathematical checks.

### Regression-test files

All of these are used by test discovery, not by `lean/verify.sh`. “Opt-in” means
the test invokes the installed Lean environment only when
`SVB_LEAN_TEST_WORK_DIR` is set to an existing external workspace.

| File | What it tests | Invokes Lean? |
|---|---|---|
| [tests/test_axiom_audit.py](tests/test_axiom_audit.py) | Final-report completeness, required declarations, permitted axioms and source/compiled-module coverage. | No. |
| [tests/test_build_lean_modules.py](tests/test_build_lean_modules.py) | Build dependency ordering, concurrency limits, cycles, failures and missing imports; one fixture checks that Lake detects source changes even when size and timestamps are preserved. | One opt-in test; other tests use simulated work. |
| [tests/test_canonical_statement.py](tests/test_canonical_statement.py) | Root immutability, missing/moved/symlinked sources, shadow modules and exact README copying/refresh. | No. |
| [tests/test_ci_boundaries.py](tests/test_ci_boundaries.py) | Administrative-only CI, status-writer permissions, trusted preflight, honest status wording, and rejection of failed/skipped jobs or stale revisions. Reporter HTTP requests are mocked. | No. |
| [tests/test_ci_context.py](tests/test_ci_context.py) | PR head/base freshness and input validation, using simulated GitHub responses. | No. |
| [tests/test_configure.py](tests/test_configure.py) | Existing dependency reuse, pin/dirty-checkout rejection, absence of installation mode, separate workspace ownership and configuration of the actual root source. Uses tiny local Git fixtures and mocks. | No. |
| [tests/test_contributions.py](tests/test_contributions.py) | Source/history requirements, permitted proof replacement, equal-constant submissions, exact base identifiers and rejection of tampered or incomplete inputs. | No. |
| [tests/test_lean_acceptance.py](tests/test_lean_acceptance.py) | Input checks and generated obligations, plus positive and adversarial Lean fixtures: wrong types/universes, extra premises, forged declarations, hidden axioms, snapshot substitutions and loss of accepted improvements. | Mixed: 14 administrative tests and 18 opt-in Lean tests. |
| [tests/test_module_replay_integration.py](tests/test_module_replay_integration.py) | Actual compiled-module replay: valid dependency chains, forged proofs, trusted-name collisions, legitimate duplicate equation theorems, unsafe premises and transitive axioms. | All nine tests are opt-in Lean fixtures. |
| [tests/test_replay_lean_modules.py](tests/test_replay_lean_modules.py) | Replay scheduling, changed artifacts, malformed inventories/reports and complete aggregation, using simulated replay operations. | No. |
| [tests/test_snapshot_source.py](tests/test_snapshot_source.py) | The actual Lean parser's restrictions on accepted-constants sources: declarative terms pass; tactics, context-sensitive hooks, scope escapes and unstable definitions fail. | All eight tests are opt-in Lean fixtures. |

Deleting or merging test files does not speed up the full theorem-verification
command, because it does not execute this suite. Tests protect against future
mistakes in the verifier; successful synthetic fixtures are not proofs of the
singular-value bounds.

## Every Markdown file

| File | Purpose and audience | Relationship to the tools |
|---|---|---|
| [README.md](README.md) | Main entry point: what is proved, the verification command, proof locations and the complete annotated canonical statement. | The canonical checker verifies its marked statement copy. The rest is reader-facing documentation. |
| [REPOSITORY_MAP.md](REPOSITORY_MAP.md) | This inventory, intended to support a simplification review. | Descriptive documentation only; no verification step depends on it. |
| [AGENTS.md](AGENTS.md) | Instructions for coding assistants: immutable source, mathematical requirements, verification, storage and review boundaries. | Read by agents; not executed or imported by Lean. |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Contributor contract: acceptable replacements, non-increasing constants, complete Lean evidence, submission process, research standards and attribution. | Human policy; its requirements are implemented in the source and Lean checks where applicable, not parsed from this Markdown. |
| [CONTRIBUTIONS.md](CONTRIBUTIONS.md) | Credit and development history, including Marcus Webb's initial contribution, assistance, superseded work and subsequent changes. | Contribution preflight requires this file to exist and be nonempty, and checks that proof-changing submissions update it. |
| [LICENSING.md](LICENSING.md) | Explains the MIT licence's scope and preservation of third-party terms. | Legal/context documentation; the actual licence text is in `LICENSE`. |
| [lean/README.md](lean/README.md) | Practical setup: existing toolchain/dependency locations, external workspaces, environment variables, RAM/concurrency settings and proof layout. | User guide for `verify.sh`, `setup.sh` and configuration; not a second verifier. |
| [docs/VERIFICATION.md](docs/VERIFICATION.md) | Maintainer reference for the manual PR check, 22-declaration interface, exact verification checks, administrative CI and review/release settings. | Explains the contract implemented by the verifier and workflow. No Markdown claim can make a failed check succeed. |
| [docs/HISTORY.md](docs/HISTORY.md) | Dated validation results, limits of earlier runs, cleanup status and links to detailed historical records in Git. | Evidence/history, not a cache of proof success. Records that full verification of the latest cleanup was deferred. |
| [docs/PROVENANCE.md](docs/PROVENANCE.md) | Preceding human work, model/tool roles, responsibility, historical hybrid verification and unresolved attribution/novelty questions. | Context and credit; it does not supply theorem assumptions or proof certificates. |
| [.github/PULL_REQUEST_TEMPLATE.md](.github/PULL_REQUEST_TEMPLATE.md) | Prompts a submitter for scope, Lean evidence, attribution, checked revisions and policy changes. | GitHub displays it when composing a PR. Ticking its boxes does not run verification. |

## Other files that explain the layout

These are not Python or Markdown, but they connect the folders above.

| File | Role |
|---|---|
| [MainTheoremStatement.lean](MainTheoremStatement.lean) | The authoritative definitions of the two target propositions. Its exact root location, name and bytes—including imports, comments and universes—are immutable. It must not be edited, deleted, renamed, relocated, replaced or shadowed; there is no formatting or maintenance exception. |
| [lean/SingularValueBounds.lean](lean/SingularValueBounds.lean) | Umbrella importing every maintained library module so the verifier can require complete coverage. |
| [lean/verify.sh](lean/verify.sh) | The single complete local verification entry point; coordinates the Python helpers and Lean checking programs. |
| [lean/setup.sh](lean/setup.sh) | A small shell wrapper around `configure.py`, used by verification and workspace inspection. It does not verify theorems. |
| [lean/SourceImports.lean](lean/SourceImports.lean) | Reads import headers with Lean's parser for the build scheduler, without elaborating proof declarations. |
| [lean/Acceptance/SnapshotSource.lean](lean/Acceptance/SnapshotSource.lean) | Restricts accepted-constants sources to stable declarative syntax, using the pinned Lean/Mathlib parser. |
| [lean/Acceptance/ModuleReplay.lean](lean/Acceptance/ModuleReplay.lean) | Implements the actual independent kernel replay, inventories and axiom checks requested by the Python scheduler. |
| [lean/lean-toolchain](lean/lean-toolchain) | Pins Lean 4.19.0. |
| [lean/lakefile.toml](lean/lakefile.toml) | Small Lake template specifying the libraries, actual source roots and compiler settings. Configuration resolves its external-storage placeholders. |
| [lean/lake-manifest.json](lean/lake-manifest.json) | Exact dependency revisions, including Mathlib; configuration supplies the external package path. |
| [.github/workflows/ci.yml](.github/workflows/ci.yml) | The administrative CI workflow described above. |
| [.github/CODEOWNERS](.github/CODEOWNERS) | Names Marcus Webb as code owner; GitHub branch settings determine whether that review is required. |
| [LICENSE](LICENSE) | The actual MIT licence text. |
| [CITATION.cff](CITATION.cff) | Machine-readable citation metadata and the distinction between this repository and the in-preparation paper. |
| [.gitignore](.gitignore) and [lean/.gitignore](lean/.gitignore) | Exclude local caches, compiled objects and editor metadata from version control. |

There are 530 checked-in Lean files: 525 library modules, the root statement,
the umbrella, and three Lean checking helpers. The ordinary source build has
527 targets: the library, root statement and umbrella. The 528-module replay
graph instead contains the library, umbrella, generated acceptance module and
independently compiled candidate-constants module. The root statement is checked
separately through the trusted expected types and is excluded from that replay
plan. These counts describe different sets of files.

## Concrete points to consider in a simplification review

- **Documentation overlap:** README, the Lean setup guide and verification guide
  describe different depths of the same workflow. Contribution history,
  verification history and provenance also overlap in dates, but respectively
  record credit, measured checks and responsibility. They could be consolidated
  further while retaining those distinctions and the checked README statement copy.
- **Helper placement:** operational Python lives in both `lean/` and `scripts/`.
  A single tools folder could make navigation simpler; imports, callers, tests
  and setup-path checks would need updating. There is no unreferenced operational
  Python helper in the present inventory.
- **Test organization:** similarly named tests distinguish administrative mocks
  from real Lean integration fixtures. Combining files could reduce the file
  list, but does not remove their separate responsibilities or speed up proof replay.
- **Proof-file granularity:** the numerical row/block files and shared evaluation
  tables are the main source of file count. They also control memory and repeated
  work, so fewer files is not necessarily a cheaper or simpler formal proof.

A static traversal of ordinary source `import` lines from
`SingularValueBounds.Canonical.Results` reaches **522 of the 525** library
modules. These three are not reached by that traversal, although the complete
umbrella still imports and checks them:

| Module to review | Present purpose |
|---|---|
| [KL/Certificates/ConcreteFinal.lean](lean/SingularValueBounds/KL/Certificates/ConcreteFinal.lean) | Bundles all eleven concrete finite-condition families as `finalCertificateConditions`; a public convenience assembly. |
| [KL/Certificates/EndpointEntropySum.lean](lean/SingularValueBounds/KL/Certificates/EndpointEntropySum.lean) | A generic integer range-sum evaluator with proofs equating it to finite sums. |
| [KL/Lower/ProfileIntegralRegularity.lean](lean/SingularValueBounds/KL/Lower/ProfileIntegralRegularity.lean) | Additional profile-integral regularity and sine-substitution lemmas. |

This is an import-graph observation, not declaration-level dead-code analysis or
proof that the files can be deleted. It does not inspect unused declarations
inside reached modules, and a module may intentionally expose an additional API.

## Files outside the maintained source inventory

`.git/` is Git's local history/index/object database; its internal directories
are managed by Git, not part of the formalization. Ignored `__pycache__/` and
editor folders may exist locally but are generated metadata rather than source.

Lean toolchains live in `~/.elan`; compatible dependencies in
`~/Lean/SingularValueBounds/.lake/packages/`; this project's build outputs,
generated checking modules, logs and validation records in its own
`~/Lean/SubGaussianTailBounds/<source-path-digest>/` workspace; and the macOS
Mathlib cache in `~/Library/Caches/mathlib`. These external directories are not
additional proof implementations. The removed supplement and retired tooling
remain accessible through Git history, not active repository files.
