# Verification policy and CI

`./lean/verify.sh` is the complete mathematical gate. It compiles the maintained
Lean implementation, audits source/import coverage and axioms, independently
replays compiled declarations through Lean's kernel, and checks the exact
canonical results and all componentwise comparisons. Python performs
administration, integrity checks and scheduling; it supplies no mathematical
certificate or proof term. Compilation or generated obligations alone are
insufficient. See [MIGRATION.md](MIGRATION.md) for recorded implementation and
validation status.

GitHub CI performs source-integrity, contribution-history and administrative
checks only. It does not install Lean, compile proofs or perform kernel replay.
**A green `CI required` status is not a Lean verification result.** Marcus Webb
runs the complete local gate on the PR branch before deciding whether to merge.

The root `MainTheoremStatement.lean` is immutable. The old prose-proof registry,
strict-improvement requirement, tradeoff route and maintenance exemptions have
no role in the new gate. Either regime may be replaced, equality is allowed in
every comparison, and the other regime must remain proved. Marcus Webb decides
whether to accept every eligible PR.

## Lean interface

<a id="prepared-complete-lean-acceptance"></a>

`SingularValueBounds.Canonical.Results` exposes these declarations in
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

Run the complete local gate using the existing external Lean workspace:

```sh
./lean/verify.sh
```

The generated 22 obligations comprise both canonical results, both baseline
corollaries, sixteen comparisons and two recorded-tuple equalities. Conditional
results, certificate assumptions, restricted universes and partial conclusions
cannot satisfy them. The original quartets are `(3.84, 1.58, 2.35, 1.5)` and
`(1.32, 1.12, 2.32, Real.sqrt 2)`.

The current ceiling comes from
`lean/SingularValueBounds/Canonical/AcceptedConstants.lean` in the **trusted
base**, never from a candidate-selected predecessor or README value. It records
one jointly proved quartet per regime. Exact Lean expressions and local helper
definitions are permitted. This standalone module imports explicit installed
Mathlib modules, one import per line in the initial block. A trusted parser uses
that exact pinned import environment and accepts only ordinary term forms and plain or
noncomputable definitions with local names inside `SubGaussian.AcceptedConstants`.
Applications, numerals, arithmetic, type annotations, lambdas, lets and local
helper definitions support exact expressions such as `Real.sqrt 2` and `Real.log x`.
Tactics, macros, evaluation hooks, attributes, options, initialization, wrapper
references and namespace escapes are rejected. Wrapping preserves the source
body's bytes and line boundaries, including inside comments. Thus elaboration cannot select a
different ceiling according to its namespace, time or environment. Proof bodies
elsewhere remain unrestricted verified Lean; arbitrary theorem constants may be
related to this stable snapshot by the proved recorded equalities.

The candidate's next snapshot is compiled separately from its proof implementation.
The recorded equalities are checked against that independent snapshot. A PR
cannot prove an improvement while retaining a weaker snapshot for the next
contributor. Both original-baseline and trusted-current comparisons are required
component by component; no component may increase.

Generated current-comparison obligations first use the named comparison proof.
They may also use definitional equality or the recorded-tuple equality when the
proposed constant equals the trusted ceiling. This preserves unchanged regimes
and lets an accepted improvement pass again after it becomes the new trusted
snapshot; it never waives a strict candidate-versus-current comparison.

Record a concise explanation and attribution in `CONTRIBUTIONS.md`. Trusted
administrative preflight requires a history change when proof sources change.
There is no JSON claim registry, separate readable-proof package, numerical
checker mapping, or restriction to appended proof modules.

## Independent kernel verification

Expected-type templates, trusted constants and verification programs are compiled
before candidate results. The independent auditor imports candidate `.olean`
data with environment extensions disabled. It never executes candidate source,
native libraries, syntax extensions or initializers.

The trusted worker reads the actual compiled import graph. The scheduler replays
each module only after all its project ancestors have passed. Ancestor hashes
must match the exact bytes verified in the same run. Hashes are checked before
and after each worker, after the entire graph, and after the final exact-type
check. Collisions with trusted constants and conflicting declarations are rejected.
Lean's repeated lazy equation theorems are allowed only when their entire theorem
records match structurally, including proof terms, types and universes. Each is
replayed unless an identical theorem was already verified in an ancestor module.
There are no cross-run success caches or candidate-provided checked flags.
Local verification starts fresh and requires every maintained module to pass.

Each worker uses Lean's `Environment.replay`: safe definitions and proofs are
sent to the kernel; constructors and recursors must match those generated by
the kernel. Unsafe or partial compiler implementation stubs are not logical
evidence. A safe declaration referring to such a stub is rejected, including
when the stub came from a verified ancestor. No unsafe exception expands the
accepted axiom list.

The trusted worker derives a fresh inventory of pinned module and declaration
names in a separate process. Structural name encoding distinguishes string and
numeric name components. The scheduler validates and hashes the inventory;
the planner uses the full declaration inventory to reject every protected-name
collision. Workers receive only its small module-name inventory and derive the
pinned declarations they actually import from those modules' constant records.
Candidate origin flags and auxiliary name metadata cannot establish that trust.
Neither inventory contains verification receipts, and neither is reused between
runs. The planner reuses module data already loaded by Lean instead of reading
the compiled library a second time.

Each module also audits every fresh safe, nonpartial declaration, including
ordinary definitions and private theorems. Dependency traversal follows fresh
and pinned declarations completely. It stops at a project ancestor only after
that ancestor has passed replay and the same axiom audit, with its artifact
hashes unchanged. The scheduler combines reports from every module in this
run, rejects missing, extra or duplicate reports, and checks the complete source
and theorem inventories. This is induction over the checked dependency graph,
not reliance on candidate declaration-origin or checked flags.

After the module graph passes, the auditor checks actual compiled types against
independently elaborated templates using `Kernel.isDefEqGuarded` and exact
universe-parameter counts. The module audits cover transitive axioms of all
accepted obligations and all fresh safe/nonpartial library declarations. The only
permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The theorem
inventory includes private declarations and other namespaces. New logical
axioms are rejected even if unused. The trusted parser requires all 22 maintained
theorem names and exact coverage of present project source modules by the
compiled umbrella.

The public `SubGaussian.Current` results, baseline corollaries, baseline
comparisons and recorded equalities are checked directly as theorem declarations
with the specified types and universes, as well as through the generated
wrappers. A valid alternate wrapper cannot hide an incorrectly typed submitted
theorem. Current comparison witnesses retain only the equality fallback described
above for unchanged accepted constants.

Imported notation can spoof a source-level generated statement, and
`Environment.addDeclCore` with checking disabled can export an invalid theorem
without adding an axiom. Source-level `#print axioms`, candidate build output and
compiled checked flags therefore cannot replace independent replay. Regressions
cover these attacks, incorrect types/universes, forbidden axioms, changed
snapshots, stale comparisons, artifact substitution and scheduler failures.
Synthetic successful fixtures test gate mechanics, not the tail theorems.

`lean/check_acceptance.sh` is the canonical entry point. Its build and snapshot
modes produce data artifacts, not success. Its private audit continuation follows
successful module replay; invoking that continuation alone is not verification.
`lean/check.sh` retains optional whole-library replay for diagnostics. The common
gate avoids repeating the whole-library diagnostic or replay. Standalone
acceptance-auditor invocation retains its complete replay and axiom audit; the
small final continuation is available only inside the trusted scheduler's
successful same-run verification path.

## Manual verification before merge

The maintainer checks the PR branch locally before merging it on GitHub:

1. Fetch the current PR branch and accepted target branch. Use clean source
   checkouts and record both commit IDs. Include any required target-branch
   updates in the candidate being verified.
2. Review changes to the verification policy and setup. Use a separate existing
   checkout of the current accepted base as `SVB_TRUSTED_ROOT`; its policy and
   accepted constants supply the independent comparison ceiling.
3. From the candidate repository root, run the complete gate with the existing
   [pinned external Lean setup](../lean/README.md#pinned-environment-and-storage):

   ```sh
   SVB_TRUSTED_ROOT="/absolute/path/to/accepted-checkout" ./lean/verify.sh
   ```

   Replace the path with the accepted checkout's actual absolute path. Keep it
   fixed at the accepted-base revision being reviewed. An unset
   `SVB_TRUSTED_ROOT` compares the checkout with itself and is only a preflight.
4. Require successful command completion, the full module and axiom audit, and
   `CANONICAL_ACCEPTANCE_COMPLETE 22 targets`. The final launcher message is
   `PASS: complete canonical Lean targets, comparisons, and axiom audits.`
   An interrupted build, compilation alone or generated obligations are not a
   completed check. Preserve the command, full log and both commit IDs outside
   the source checkout.
5. Confirm that the PR head and accepted target branch still match those checked.
   Repeat verification after either changes. Review the administrative CI result
   separately, then merge only when the complete local proof check and review
   are satisfactory.

For the initial formalization or a verification-framework transition, an older
accepted checkout may not contain the required canonical source, snapshot or
compatible verifier. Record that limitation and the maintainer's explicit
reviewed adoption of the new policy and baseline. Do not describe a
self-comparison as an independent accepted-base comparison or silently choose
an older, weaker accepted quartet. The immutable canonical source and full
mathematical obligations still apply.

Local verification executes Lean metaprograms with the local user's permissions.
The auditor independently checks the resulting declarations, but the overall
local command is not an operating-system sandbox for candidate code. Review the
candidate's setup and verification changes before executing them. Hashes detect
artifact drift; they are not mathematical evidence or protection against a
process that can rewrite the verifier itself.

## Trusted administrative workflow

The `pull_request_target` workflow comes from the trusted base. Its source
preflight checks the exact PR head merged with the event's base revision.
Candidate workflow edits cannot replace the policy already checking that PR.

The workflow has three jobs:

1. **Start required status** marks the exact candidate commit pending.
2. **Source and contribution preflight** runs trusted source-integrity,
   contribution-history, revision-freshness and administrative tests. It reads
   candidate files without executing candidate Lean or setup scripts. Tests
   that require an installed Lean environment are not run by this CI.
3. **Report required status** posts `CI required` only after the required
   administrative jobs succeed. Failed, cancelled or skipped jobs are not
   success. It rechecks the PR head and target base before posting success.

The two status writers execute static Python, never check out candidate code,
and are the only jobs with `statuses: write`. Preflight uses read-only
permissions, no repository secrets and no persisted checkout credentials.
There are no CI proof builds, constants-compilation jobs, kernel-audit jobs,
Lean dependency installations, proof artifacts or replay checkpoints.

GitHub branch protection enforces this administrative status. It does not
record or enforce completion of the maintainer's local Lean run. A green
status therefore does not replace the manual pre-merge verification above.

## Canonical source and framework protection

`python3 scripts/check_canonical_statement.py` checks the fixed root SHA-256,
rejects source/compiled shadows and symlinks, and checks its marked README copy
byte for byte. Refresh only that presentation with
`python3 scripts/check_canonical_statement.py --write-readme`.

The validator imports its own trusted integrity policy. Editing both a candidate
statement and its candidate digest cannot evade it. The actual root is compiled
independently; its identity check is not a proof of either proposition.

When candidate and trusted roots differ, `lean/setup.sh`, `lean/configure.py`,
`lean/lakefile.toml`, `lean/lake-manifest.json` and `lean/lean-toolchain` must match
the trusted base. This prevents compiler/dependency changes and source-directory
redirection. Maintained proof modules may be replaced, reorganized or deleted
if all canonical results, comparisons and current source audits pass.

Intentional framework changes need a separately reviewed trusted-policy
transition. The initial replacement of the older registry/certificate workflow
also must be installed as reviewed trusted policy; a maintenance comment cannot
override the old base workflow. The canonical source remains immutable.

## Resources, records and repository settings

Cold local builds and independent replay can take hours and use several
gigabytes per worker. `SVB_BUILD_JOBS` and `SVB_REPLAY_JOBS` bound local
parallelism; choose values that fit the available CPU and RAM. Reuse the
installed pinned toolchain and dependencies, and keep build outputs, caches and
verification logs outside the source checkout. See the
[Lean setup guide](../lean/README.md) and measured resource use in
[MIGRATION.md](MIGRATION.md). That record preserves the previous hosted runs
and staged-workflow history; they are not the current CI procedure.

Open **Actions → Repository checks** to inspect the administrative run for the exact
commit and base. Preserve the successful local verification log and its
candidate/base commit IDs separately. CI logs and green status indicators
establish no mathematical claim.

The optional manual **Supplement build** workflow rebuilds the historical
document only. It is outside canonical verification and never reports
`CI required`. A separate PDF or prose proof is not a contribution requirement.

Default-branch protection should require **CI required**, GitHub Actions as its
expected source, up-to-date branches and pull requests, including for the
maintainer. Marcus Webb's approval is required for contributor PRs. His
review-only bypass for his own PRs does not waive administrative CI or the
manual mathematical check. Files cannot activate repository settings; see the
[maintainer guide](LAUNCH_CHECKLIST.md#github-settings). No PR is created,
merged or published by these local tools.
