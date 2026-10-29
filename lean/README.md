# Building the Lean formalization

The immutable [root statement](../MainTheoremStatement.lean) is compiled from
its actual root location. Proofs and supporting mathematics are maintained
under [SingularValueBounds/](SingularValueBounds/). See the
[migration and validation record](../docs/MIGRATION.md) for the actual proof
status and observed checks.

## Verify

From the repository root, run:

```sh
./lean/verify.sh
```

This is the complete canonical check. It requires both results at arbitrary
sample-space universe `u`, their baseline corollaries, exact componentwise
comparisons with the original baselines and trusted accepted quartets, and
equalities tying the recorded constants to those proved. A missing or conditional
result cannot pass. The [public interface](../docs/CI.md#lean-interface) has
22 stable theorem declarations in `SubGaussian.Current`.

The command checks the actual root source and the full README copy, builds the
maintained sources, and independently replays every maintained module through
Lean's kernel in dependency order. Each module's safe declarations receive an
axiom audit in that same process. The verifier combines the reports only after
all modules pass with unchanged artifacts, checks complete source/import
coverage, and checks the exact canonical types. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed.
Python performs administration only; numerical inequalities are Lean obligations.

Local self-comparison is a preflight. Before merging a PR, the maintainer checks
out its branch and runs the complete command locally against an existing
checkout of the current accepted base:

```sh
SVB_TRUSTED_ROOT="/absolute/path/to/accepted-checkout" ./lean/verify.sh
```

Record both commit IDs and the completed verification log. Repeat the check if
the PR or accepted base changes. See the
[manual procedure](../docs/CI.md#manual-verification-before-merge), including
initial framework adoption. Candidate code executed locally has the permissions
of the local user, so the local command is not a hostile-code sandbox.

GitHub CI performs administrative checks only. It does not run Lean, and a green
`CI required` status does not establish mathematical verification.

Cold builds and independent replay involve large exact rational computations.
The [validation record](../docs/MIGRATION.md) records measured local runs and
the earlier hosted attempts separately.

For development, `./lean/check.sh` builds and independently replays the entire
supporting library in one process. The complete command uses the module-based
verifier and avoids an additional whole-library diagnostic or replay.
`python3 scripts/check_canonical_statement.py` is a fast source-integrity check,
not mathematical verification.

## Proof entry points

- [Canonical/Results.lean](SingularValueBounds/Canonical/Results.lean) supplies
  the public current results, baseline corollaries and comparison interface.
- [Canonical/General.lean](SingularValueBounds/Canonical/General.lean) supplies
  `SingularValueBounds.Canonical.general_baseline`.
- [Canonical/Unit.lean](SingularValueBounds/Canonical/Unit.lean) supplies
  `SingularValueBounds.Canonical.unit_baseline`.
- [Canonical/Adapter.lean](SingularValueBounds/Canonical/Adapter.lean) proves
  correspondence with the root definitions, including zero singular values,
  row hypotheses, norms, logarithms, event measurability and `ℝ≥0∞` bounds.
- [Canonical/Monotonicity.lean](SingularValueBounds/Canonical/Monotonicity.lean)
  proves componentwise weakening, allowing baseline corollaries of a stronger
  jointly proved quartet.

The existing analytic assembly in [KL/Theorem.lean](SingularValueBounds/KL/Theorem.lean)
remains reusable. Concrete finite instances are supplied by Lean proofs under
`KL/Certificates/`; an accepted canonical result cannot leave such an instance
as a premise. A replacement can change this architecture and remove superseded
modules. Historical internal declaration names are not frozen acceptance targets.
There is one maintained formalization and one [contribution history](../CONTRIBUTIONS.md).

`TrustedAudit.lean` loads implementation modules without environment extensions
and supports full replay or the whole-library diagnostic. `Audit.lean` is a
source diagnostic. The canonical acceptance auditor is generated from trusted
policy before candidate modules are loaded, and checks types independently of
candidate syntax and elaborators. Its kernel replay rejects forged declarations
as well as forbidden axioms.

## Pinned environment and storage

Reuse Lean **4.19.0** and the exact locked dependencies. Mathlib remains at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`; all transitive revisions in
[lake-manifest.json](lake-manifest.json) are preserved. Ordinary local verification
never installs, clones, fetches or upgrades dependencies.

Inspect the installed toolchains before invoking Lean:

```sh
if [ -f "$HOME/.elan/env" ]; then
  . "$HOME/.elan/env"
fi
"$HOME/.elan/bin/elan" toolchain list
```

The inventory must contain `leanprover/lean4:v4.19.0`. Then run:

```sh
./lean/setup.sh
./lean/verify.sh
```

The launcher reuses compatible exact dependency checkouts at
`~/Lean/SingularValueBounds/.lake/packages/`. This checkout's default workspace
is `~/Lean/SubGaussianTailBounds/<source-path-digest>/`, with its own outputs.
It does not borrow `SingularValueBounds/.lake/build/`. An ownership marker
prevents a different checkout from sharing its build directory.

| Environment variable | Purpose |
|---|---|
| `SVB_WORK_DIR` | Optional absolute external workspace belonging to this checkout |
| `SVB_PACKAGES_DIR` | Optional existing exact pinned dependency directory |
| `SVB_ELAN_BIN` | Existing Elan executable; otherwise central `~/.elan/bin/elan`, then PATH |
| `MATHLIB_CACHE_DIR` | External Mathlib cache; defaults to `~/Library/Caches/mathlib` on macOS |
| `SVB_TRUSTED_ROOT` | Accepted base checkout for comparison; self-comparison is only a preflight |
| `SVB_BUILD_JOBS` | Maximum simultaneous module builds; defaults to 1 |
| `SVB_REPLAY_JOBS` | Maximum simultaneous independent kernel replay workers; defaults to 1 |

Increase parallelism only to fit the machine's CPU and memory. Some finite proof
modules use several gigabytes per worker. The build scheduler reads import
headers with Lean and starts a module only after its project dependencies finish.
For an unchanged workspace, Lake first checks every target's source-content trace
with `--no-build`; stale targets use the bounded scheduler. This avoids repeated Lake
startups on warm builds and does not skip any subsequent kernel replay.
The replay scheduler independently checks dependencies and artifact hashes; an
imported module becomes a trusted replay seed only after it passes in that run.

The finite proofs share uniform bounds and exact evaluation lemmas under
`KL/Certificates/`: `UniformEndpointPrefactors`, `MomentCellSideConditions`,
`GeneralSecondSideConditions`, `IntegerMomentEvaluation`,
`IntegerCoefficientStages` and `IntegerCoefficientStages8`.
`ExactMomentEvaluation` supplies the sum identities
used to prove the integer recurrences. These are ordinary kernel-checked Lean
proofs. The original rational specifications, truncations and required margins
remain the definitions being certified. Moment and second-moment decisions use
private blocks of at most 32 cells within their existing modules. Endpoint
polynomials use smaller proved degree bounds, and shared Bernstein weights are proved
once. See [the measurements](../docs/MIGRATION.md) for the scope and limits of
observed memory reductions.

The entropy proofs also share repeated decay evaluations and adjacent endpoint
corner bounds. `IntegerRoundedLogEvaluation` and `EndpointPrefactorEvaluation`
prove exact equalities with the original rounded algorithms, so numerical proofs
can use integer arithmetic without changing any rounding step.
`PlateauPolynomialIdentity` replaces expanded high-degree identities with proved
degree bounds and enough exact evaluations to establish polynomial equality.
The larger numerical modules elaborate declarations sequentially to limit retained
proof contexts. This changes scheduling, not kernel checking or the axiom policy.

For an explicit workspace and compatible installed packages:

```sh
export SVB_WORK_DIR="$HOME/Lean/SubGaussianTailBounds/my-checkout"
export SVB_PACKAGES_DIR="$HOME/Lean/SingularValueBounds/.lake/packages"
export MATHLIB_CACHE_DIR="$HOME/Library/Caches/mathlib"
./lean/setup.sh
```

`./lean/setup.sh --print-work-dir` prints the chosen workspace without configuring
it. Missing paths, incompatible revisions, tracked dependency changes and missing
toolchains are reported. Diagnose these before changing an installation.

The checked-in Lake configuration and manifest are small portable templates.
`configure.py` resolves paths in the external workspace. The two Lake libraries
use the actual root `MainTheoremStatement.lean` and the editable `lean/` sources.
Do not create another authoritative statement copy, bulky dependency symlink,
cache or compiled output in this source tree or in OneDrive.

## CI and historical records

The [CI policy](../docs/CI.md) keeps trusted source/contribution checks and
separate status reporting on GitHub. The maintainer performs the complete
mathematical verification locally before merging. Candidate workflow edits do
not change the policy already installed on the target branch. Changes to the
verification policy require explicit maintainer review.

The [historical verification report](VERIFICATION_REPORT.md) and
[formalization record](FORMALISATION_PLAN.md) preserve earlier dates, timings and
scope. Retired checker paths and manifests are historical references in Git
history. The [supplement](../docs/HISTORICAL_SUPPLEMENT.md) is historical and is
not an input to the canonical build or a required contribution check.
