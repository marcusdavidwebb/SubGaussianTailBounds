# Verification and review

`./lean/check-statements.sh` checks the two displayed propositions and their
proof dependencies. `./lean/verify.sh` is the broader repository acceptance
check, including independent replay and contribution-policy comparisons.
Marcus Webb runs the complete check locally before merging each PR. GitHub CI checks source integrity and
repository administration; its green status does not certify a Lean proof.

The focused command builds the proof dependency closure, checks the exact types
for arbitrary sample-space universes and audits their transitive axioms. It
trusts imported compiled artifacts and elaborators; hostile imported syntax can
affect its source-level type checks. It does not replace the independent replay,
separate exact-type audit, full source coverage or accepted-base comparisons in
the complete check.

This guide explains the acceptance contract and review procedure. Use
[lean/README.md](../lean/README.md) for setup and memory settings, or the
[source layout](../lean/README.md#source-layout) to find the proof and checking code.

## Manual verification before merge

Use the [pinned external setup](../lean/README.md). Check out the current PR
branch and keep a separate existing checkout of the accepted target branch.
Record both commit IDs and run from the candidate repository root:

```sh
SVB_TRUSTED_ROOT="/absolute/path/to/accepted-checkout" ./lean/verify.sh
```

Replace the path with the accepted checkout's actual absolute path. It supplies
the trusted policy and current constants. An unset `SVB_TRUSTED_ROOT` compares
the checkout with itself and is only a preflight.

The separate checkout can be an ordinary Git worktree of the accepted branch.
Its purpose is to keep a candidate from choosing the checks or comparison
ceilings used to assess that same candidate. When the accepted branch predates a
deliberate statement or verifier migration, the maintainer must first review and
adopt that migration; an old checkout cannot certify the new policy by itself.

Require successful completion of the full replay and axiom audit, including
`CANONICAL_ACCEPTANCE_COMPLETE 22 targets` and the final
`PASS: complete canonical Lean targets, comparisons, and axiom audits.`
Keep the command, full log and both commit IDs outside the source checkout.
Confirm that neither revision changed before merging; rerun if either changed.
An interrupted run or compilation alone is insufficient.

For initial formalization or framework adoption, an older accepted checkout may
lack the required canonical source, snapshot or compatible verifier. Record the
maintainer's reviewed adoption of the policy and baseline; do not call
self-comparison an independent accepted-base check. Candidate Lean metaprograms
run with the local user's permissions, so review setup and verification changes
before executing them. The local command is not a hostile-code sandbox.

The 30 October 2026 NLA-lib migration changes the canonical source and the
pinned toolchain/dependencies with the maintainer's authorization. Its verifier
compatibility changes require review as part of that adoption: the constants
parser handles Lean 4.33's syntax while rejecting module/import modifiers, and
the axiom auditors traverse actual checked types and proof bodies instead of
Lean's new cached axiom summaries. Pinned dependencies load their private proof
bodies with extensions disabled. Split project artifacts are rejected because
the current scheduler hashes one artifact per project module. The exact-type,
universe, source-coverage, replay and axiom requirements are retained.
Compilation and selected checks during this migration do not constitute a
complete verification run; the maintainer explicitly deferred kernel replay.

The separately authorized real-probability statement revision also changes the
canonical source digest and the exact expected tail types. Its equivalence to
the preceding `ENNReal` bounds is proved in
[TailEquivalence.lean](../lean/SingularValueBounds/Canonical/TailEquivalence.lean)
under a probability measure. The maintainer’s authorization of this precise
statement change does not waive independent replay or authorize later canonical
changes; an accepted checkout with the earlier digest will reject this revision
until the reviewed policy is adopted. A later explicitly requested helper and
import simplification likewise changes the canonical digest without waiving any
of these checks.

The maintainer's 2 November 2026 refactor factors both propositions through
`TailBoundAt`, moving the general parameter quantifier before the sample-space
arguments and specializing the unit case at `K = 1`. The existing
[statement equivalences](../lean/SingularValueBounds/Canonical/StatementEquivalence.lean)
connect these definitions to the expanded hypotheses and bounds. The source pin
changes, while all 22 public obligations and the exact-type, universe, replay,
source-coverage and axiom requirements remain. An older trusted source pin still
rejects this revision until reviewed adoption; focused checks do not waive the
complete before-merge run, which the maintainer has deferred for this task.

The final source supplied later that day names the tail helper
`GaussianSingularValueTails` and places `1 ≤ n → n ≤ m` after the matrix argument
in `TailBoundAt`. Its protected digest and proof bridge are synchronized with
those final bytes. The general/unit propositions and all 22 obligations retain
their mathematical requirements. See the
[final synchronization record](HISTORY.md#final-statement-synchronization--2-november-2026)
for the checks performed; an older trusted pin still requires reviewed adoption.

## Lean interface

<a id="prepared-complete-lean-acceptance"></a>

`SingularValueBounds.Canonical.Results` exposes the following declarations in
`SubGaussian.Current`:

| Declaration | Required type or role |
| --- | --- |
| `generalAlpha`, `generalBeta`, `generalGamma`, `generalDelta` | One jointly proved general quartet of exact Lean real expressions |
| `unitAlpha`, `unitBeta`, `unitGamma`, `unitDelta` | One jointly proved unit quartet of exact Lean real expressions |
| `general.{u}`, `unit.{u}` | The respective canonical proposition at that quartet, for arbitrary universe `u` |
| `general_baseline.{u}`, `unit_baseline.{u}` | The canonical propositions at the baseline quartets in [CONTRIBUTING.md](../CONTRIBUTING.md#mathematical-contract) |
| `general_baseline_alpha` through `general_baseline_delta`, and `unit_baseline_*` | Each component is at most its corresponding baseline component |
| `general_current_alpha` through `general_current_delta`, and `unit_current_*` | Each component is at most its trusted currently accepted counterpart |
| `general_recorded`, `unit_recorded` | The current quartet equals the corresponding candidate `AcceptedConstants` quartet |

The 22 obligations are the two current results, two baseline theorems,
sixteen componentwise comparisons and two recorded-tuple equalities. Results
must cover arbitrary sample-space universe `u` and the complete canonical
propositions. The [contribution contract](../CONTRIBUTING.md#mathematical-contract)
defines the baseline and accepted-constant policy.

The candidate's standalone `Canonical/AcceptedConstants.lean` snapshot is
compiled separately from its proof implementation. Recorded equalities connect
it to the proved quartet. The comparison ceiling comes from the trusted
accepted base's snapshot. Snapshots support ordinary exact Lean terms and local
definitions, with explicit Mathlib imports; tactics, macros, initialization,
attributes and scope escapes are rejected. Current comparisons may use a
recorded or definitional equality fallback when a proposed constant equals the
trusted ceiling; strict improvements still require their comparison proofs.

## What the complete verifier checks

The launcher is [lean/verify.sh](../lean/verify.sh). All operational Python is in
`scripts/`; the Lean checking programs and templates are in
[lean/Verification/](../lean/Verification/). The mathematical proof modules
remain in the separate `lean/SingularValueBounds/` tree.

The actual immutable root statement and its README presentation are checked for
byte identity. Trusted constants, expected-type templates and verification
programs are prepared before candidate results. With a separate trusted base,
setup files, Lake configuration, dependency manifest and toolchain must match
that base. Framework changes require explicit review; the canonical source
remains immutable.

The generator prepares the exact expected types and comparison obligations in
the external workspace. `SnapshotSource.lean` checks the constants sources;
`SourceImports.lean` reads imports for bounded compilation. The generated
obligations include the `ElaborationAudit.lean.in` template's axiom and checked-flag
checks. These are followed by the independent verification below; successfully
generating or elaborating obligations is not the final acceptance check.

The auditor loads compiled candidate `.olean` data with environment extensions
disabled, without executing candidate syntax, native plugins or initializers.
It derives the compiled import graph and a fresh inventory of pinned declarations,
rejects protected-name collisions, and requires complete source/module coverage.
Each module is independently replayed through Lean's kernel after its project
ancestors pass. Artifact hashes are checked throughout; an ancestor is a trusted
seed only after its replay and axiom audit succeed in this run. Compiled checked
flags and earlier runs cannot substitute for this verification.

The proposed launcher also snapshots the paths, contents and executable bits of
candidate and trusted source/configuration inputs at the start and checks them
again before reporting success. This detects a final checkout that differs from
the starting inputs, including same-size edits with restored timestamps. It does
not detect changes fully reverted between checks and is not a sandbox. This
verification-policy change requires separate review and adoption.

The pinned declaration inventory comes from `Mathlib` and
`CanonicalAcceptanceExpected`; NLA-lib is covered through the modules imported
by the canonical statement. Pinning NLA-lib does not automatically add all of
its modules to that inventory. An additional split NLA-lib module outside this
import closure is rejected by the single-artifact replay guard. Supporting such
an import requires a separately reviewed inventory expansion or support for
hashing and replaying every artifact part, with the complete replay and axiom
requirements preserved.

All fresh safe declarations, including private theorems and ordinary definitions,
receive a transitive axiom audit. Unsafe implementation stubs cannot be logical
premises. New axioms are rejected even when unused; the only allowed axioms are
`propext`, `Classical.choice` and `Quot.sound`. After the full graph passes, the
auditor compares compiled public results and generated obligations against
independently elaborated exact types and universe counts. A misleading wrapper
cannot hide an incorrectly typed public result. Source hashes and Python
administration establish no mathematical truth.

`ModuleReplay.lean` implements the independent kernel and axiom checks;
`CanonicalAudit.lean.in` supplies the separate exact-type auditor. The
`replay_lean_modules.py` scheduler combines their reports and validates complete
source, umbrella and module coverage before it prints acceptance output.
Generated Lean sources, compiled checkers and logs stay outside the repository.

## Administrative CI and repository settings

The trusted-base `pull_request_target` workflow checks the exact PR head merged
with the event's base. Its three jobs announce a pending status, run trusted
source/contribution checks and administrative tests, then report `CI required`.
The final reporter rejects failed or skipped jobs and stale head/base revisions.
Preflight has read-only permissions and does not run candidate Lean or setup
scripts. Only the isolated static status writers can write statuses; they never
check out candidate code. Candidate workflow edits cannot replace the policy
already checking that PR.

Protect `main` with pull requests, up-to-date branches and `CI required` from
GitHub Actions, including for administrators; disallow force pushes and deletion.
Require Marcus Webb's codeowner approval for contributors. His separate
review-only bypass for his own PRs does not waive administrative CI or local
mathematical verification. GitHub does not enforce completion of the local run.
The maintainer reviews and merges; agents must not merge or enable auto-merge.

For a release, verify its exact commit, retain the successful local log and
canonical targets, and record the commit, actual version/date and attribution.
Publish only with explicit maintainer approval. Repository releases are separate
from paper publication; do not invent publication metadata.

[Dated verification history](HISTORY.md) records earlier checks and resource
measurements. Keep those results distinct from a new run's outcome.
