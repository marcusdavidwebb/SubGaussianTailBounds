# Singular-value bounds: Lean formalisation

The current supplementary theorem has **completed hybrid verification** with
both quartets: general `(3.84, 1.58, 2.35, 1.5)` and K=1
`(1.32, 1.12, 2.32, sqrt 2)`. All **24 sections** are complete.
Lean proves the analytic theorem conditional on explicit finite rational
certificates; exact Python programs check those certificates externally.

## Current theorem and scope

[KL/Theorem.lean](SingularValueBounds/KL/Theorem.lean) exposes:

- `SingularValueBounds.KL.singular_value_tails_general_of_certificates`
- `SingularValueBounds.KL.singular_value_tails_one_of_certificates`
- `SingularValueBounds.KL.theorem_explicit_constants_of_certificates`

The joint result proves `TheoremKL μ generalConstants ∧ TheoremKLOne μ`.
Apart from [FinalCertificateConditions](SingularValueBounds/KL/Certificates/Final.lean),
its assumptions are the original ones: independent centred isotropic rows,
the directional sub-Gaussian MGF bound, m≥n≥1, K≥1 and t≥0. Rows may have
different laws and dependent coordinates. Both tail events are non-strict;
all Gram singular values, including zeros, are included. No row estimate,
pathwise budget or other analytic claim survives as an extra premise.

The eleven certificate fields contain only finite rational conditions.
Python supplies no Lean proof term; its execution and correspondence to those
predicates are part of the hybrid trust boundary. Source digests detect drift
and are not proof exports. This is not an unconditional kernel proof of the
finite certificate bundle.

## Verify

From the public repository root:

```sh
./lean/check_certificates.sh   # Python only: original checker and eleven interfaces
./lean/check.sh                # Lean build and complete axiom/import audit
./lean/check_hybrid.sh         # Registry, claimed theorem targets, Lean and certificates
```

In the paper working tree, prefix those commands with `./supplementary/`
instead of `./`. Each script resolves its own location and also works when
called from another directory. Python 3.11 or later is required; CI selects
Python 3.14. All certificate checks reject optimized Python execution.
The checkers use only the Python standard library.

For Lean, first make the existing pinned Elan toolchain and dependency tree
available as described below. The launchers inspect them and report missing
requirements; ordinary verification does not install, clone, upgrade, or
fetch anything. `./lean/setup.sh` prints the configured external workspace.
Run the wrappers rather than invoking Lake inside this source folder.

The hybrid command first validates every contribution record, including any
additional exact rational certificate data. It generates the claimed theorem
types in the external workspace's `.lake/contribution-ci/` directory, checks
those exact types and their axioms after the main Lean audit, then runs all
certificate checkers. This reproduces the current registry's complete checks.
The standalone Lean command checks the library and its main audit; passing
`SVB_EXTRA_LEAN` additionally checks a separately generated contribution-audit
file. Pull-request comparisons and commit-specific maintainer authorizations
are enforced separately by CI.

The current library contains **147 KL modules** and **32 shared supporting
modules**. Its audit targets **3,224 declarations** (3,200 KL and 24 shared
principal targets), allowing only `propext`, `Classical.choice` and `Quot.sound`.
The final three public results also have individual `#print axioms` reports.
The retained checkpoint has 3,015 targets after removal of 17 retired targets;
full KL source/import coverage remains enforced. The latest measured run is
recorded in the verification report. No `sorry`, added axioms or native-oracle
proofs are used.

- [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md): run, environment, validation and trust scope.
- [FORMALISATION_PLAN.md](FORMALISATION_PLAN.md): all 24 completed sections,
  dependencies, paper/module correspondence, finite field/checker map,
  reuse assessment and measured assisted timings. Obsolete planning prose
  has been removed; measured evidence is retained.
- [verification_manifest.json](verification_manifest.json): checked source inventory and drift guards.

## Current proof map

The 147 KL modules are under `SingularValueBounds/KL/` and imported by
[SingularValueBounds.lean](SingularValueBounds.lean). The plan gives the full
P01–P24 map and numerical conditions for each package.

| Sections | Sources | Role |
|---|---|---|
| P01–P04 | [Statement.lean](SingularValueBounds/KL/Statement.lean), [Barrier/](SingularValueBounds/KL/Barrier), [Transfer.lean](SingularValueBounds/KL/Transfer.lean) | Targets, exact roots, measurable corrections, deterministic budgets and independent-row transfer |
| P05–P08 | [Weighted/](SingularValueBounds/KL/Weighted), [Certificates/](SingularValueBounds/KL/Certificates) | Gaussian/entropy tools, analytic enclosure rules and polynomial/coverage implications |
| P09–P14 | [Lower/](SingularValueBounds/KL/Lower), [Barrier/MixedPathwise.lean](SingularValueBounds/KL/Barrier/MixedPathwise.lean) | Lower Laplace bounds, both profiles/covariance refinements, mixed-cap budgets and scalar integrals |
| P15–P20 | [Upper/](SingularValueBounds/KL/Upper) | Exact upper tails, extended rates, determinant comparisons and both mean bounds |
| P21–P23 | [Upper/TailMoments.lean](SingularValueBounds/KL/Upper/TailMoments.lean), [EndpointFullApplication.lean](SingularValueBounds/KL/Upper/EndpointFullApplication.lean), [GeneralApplication.lean](SingularValueBounds/KL/Upper/GeneralApplication.lean) | Tail-to-moment bounds and both full upper MGFs |
| P24 | [Theorem.lean](SingularValueBounds/KL/Theorem.lean), [Certificates/Final.lean](SingularValueBounds/KL/Certificates/Final.lean) | Final assembly from original row assumptions and only finite certificates |

`Audit.lean` enumerates every imported KL theorem, including generated
equations and structure facts, and retains 24 shared principal targets.
`check_axiom_audit.py` enforces the three-axiom allowlist, target checkpoint,
final theorem targets and complete source/import coverage. Some supporting
modules retain harmless linter warnings.

## Retired theorem and retained shared code

The earlier variational theorem in the historical manuscript,
with its n^(1/6) correction, has been retired from this Lean library.
Its former public results `SingularValueBounds.theorem11` and
`SingularValueBounds.singular_value_tails` are no longer exported. Sixteen
modules exclusive to that theorem were removed after completion of the KL proof.

The 32 supporting modules still required by KL remain: matrix/spectral algebra
in `Core/` and `Spectral/`, Gaussian/quadratic tools in `QuadraticForms/`, exact
upper roots in `Shifts/`, and probability/optimization tools in `Concentration/`,
`SpectralConcentration/` and `Main/`. The plan preserves the historical
declaration-level reuse assessment and measured timings; it marks retired
source references as historical paths. Shared supporting code is part of the
current proof, not obsolete build debris.

## Pinned environment and storage

Lean **4.19.0** and Mathlib **v4.19.0** are pinned by `lean-toolchain` and
`lake-manifest.json` (Mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`). Every transitive dependency is
locked to a full commit digest. Routine verification preserves all these
revisions and rejects tracked changes in the dependency working trees.

The checked-in `lakefile.toml` and `lake-manifest.json` are portable templates.
[configure.py](configure.py), called by [setup.sh](setup.sh), resolves their
path tokens into **absolute** source, build, and package paths in an external
workspace. The dependency entries remain unchanged. Lake runs there, using
the single editable source tree here. No dependencies, compiled outputs, or
configuration caches are placed in the source checkout or OneDrive.

| Setting | Purpose |
|---|---|
| `SVB_WORK_DIR` | Optional absolute external workspace; each checkout must have its own build directory |
| `SVB_PACKAGES_DIR` | Optional absolute directory containing the existing exact pinned dependency checkouts |
| `SVB_ELAN_BIN` | Optional existing Elan executable; otherwise `~/.elan/bin/elan`, then PATH |
| `MATHLIB_CACHE_DIR` | Existing external Mathlib download cache; defaults to `~/Library/Caches/mathlib` on macOS and `~/.cache/mathlib` elsewhere |
| `SVB_EXTRA_LEAN` | Optional absolute generated contribution-audit file, checked after the main Lean audit |

For example, given an existing compatible installation:

```sh
SVB_WORK_DIR="$HOME/Lean/SubGaussianTailBounds/my-checkout" \
SVB_PACKAGES_DIR="$HOME/Lean/existing-project/.lake/packages" \
./lean/check.sh
```

Otherwise the default workspace is
`~/Lean/SubGaussianTailBounds/<source-path-digest>/`. That digest prevents
independent source checkouts from sharing project build outputs. Existing
matching dependencies at `~/Lean/SingularValueBounds/.lake/packages/` are
reused when available. On the author's original working tree, the existing
central source links identify `~/Lean/SingularValueBounds/` as its workspace;
that project retains its own `.lake/build/`. A workspace marker rejects
reuse by a different checkout. Explicit paths inside the checkout or OneDrive
are rejected.

The original central proof-source links are preserved. Central configuration
and manifest links are replaced atomically with resolved regular files, so
portable templates never become live unresolved Lake configuration. The
central toolchain link continues selecting the same version. There is no
second editable copy of the proof sources.

Load `~/.elan/env` if needed. The launcher checks the installed toolchain
inventory before invoking Lean and uses `elan run` without its installation
flag. Missing installations or incompatible dependencies are diagnostics,
not requests to reinstall anything.

## Continuous integration

`./lean/setup.sh --ci` is an explicit bootstrap restricted to disposable
GitHub-hosted Linux runners (`GITHUB_ACTIONS=true`,
`RUNNER_ENVIRONMENT=github-hosted`). The workflow provides a pinned existing
Elan executable; this step installs the exact Lean toolchain if needed,
fetches only the locked dependency commits into its external workspace, and
retrieves Mathlib's compiled cache. It never runs as part of ordinary local
verification. CI then uses the same certificate and Lean audit commands as
contributors. The Python certificate checks remain external to Lean's
kernel; CI does not change that trust boundary.

The public repository is intended for
<https://github.com/marcusdavidwebb/SubGaussianTailBounds>. Preparing these
files does not assert that it has been created or released. The paper is in
preparation. Historical verification dates and manifests describe their
recorded source snapshots; they are not automatically refreshed by setup.
