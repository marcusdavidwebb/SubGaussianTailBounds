# Verification and review

`./lean/verify.sh` is the single complete mathematical check. Marcus Webb runs
it locally before merging each PR. GitHub CI checks source integrity and
repository administration; its green status does not certify a Lean proof.

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

## Lean interface

<a id="prepared-complete-lean-acceptance"></a>

`SingularValueBounds.Canonical.Results` exposes the following declarations in
`SubGaussian.Current`:

| Declaration | Required type or role |
| --- | --- |
| `generalAlpha`, `generalBeta`, `generalGamma`, `generalDelta` | One jointly proved general quartet of exact Lean real expressions |
| `unitAlpha`, `unitBeta`, `unitGamma`, `unitDelta` | One jointly proved unit quartet of exact Lean real expressions |
| `general.{u}`, `unit.{u}` | The respective canonical proposition at that quartet, for arbitrary universe `u` |
| `general_baseline.{u}`, `unit_baseline.{u}` | The canonical propositions at the original baseline quartets |
| `general_baseline_alpha` through `general_baseline_delta`, and `unit_baseline_*` | Each component is at most its original baseline |
| `general_current_alpha` through `general_current_delta`, and `unit_current_*` | Each component is at most its trusted currently accepted counterpart |
| `general_recorded`, `unit_recorded` | The current quartet equals the corresponding candidate `AcceptedConstants` quartet |

The 22 obligations are the two current results, two baseline corollaries,
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

The actual immutable root statement and its README presentation are checked for
byte identity. Trusted constants, expected-type templates and verification
programs are prepared before candidate results. With a separate trusted base,
setup files, Lake configuration, dependency manifest and toolchain must match
that base. Framework changes require explicit review; the canonical source
remains immutable.

The auditor loads compiled candidate `.olean` data with environment extensions
disabled, without executing candidate syntax, native plugins or initializers.
It derives the compiled import graph and a fresh inventory of pinned declarations,
rejects protected-name collisions, and requires complete source/module coverage.
Each module is independently replayed through Lean's kernel after its project
ancestors pass. Artifact hashes are checked throughout; an ancestor is a trusted
seed only after its replay and axiom audit succeed in this run. Compiled checked
flags and earlier runs cannot substitute for this verification.

All fresh safe declarations, including private theorems and ordinary definitions,
receive a transitive axiom audit. Unsafe implementation stubs cannot be logical
premises. New axioms are rejected even when unused; the only allowed axioms are
`propext`, `Classical.choice` and `Quot.sound`. After the full graph passes, the
auditor compares compiled public results and generated obligations against
independently elaborated exact types and universe counts. A misleading wrapper
cannot hide an incorrectly typed public result. Source hashes and Python
administration establish no mathematical truth.

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
