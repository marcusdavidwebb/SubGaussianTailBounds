# CI policy and trust boundaries

`./lean/verify.sh` is the complete mathematical gate. It compiles the maintained
Lean implementation, audits source/import coverage and axioms, independently
replays compiled declarations through Lean's kernel, and checks the exact
canonical results and all componentwise comparisons. Python performs
administration, integrity checks and scheduling; it supplies no mathematical
certificate or proof term. Compilation or generated obligations alone are
insufficient. See [MIGRATION.md](MIGRATION.md) for recorded implementation and
validation status; local results do not establish a successful hosted run.

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
There are no cached success receipts or candidate-provided checked flags.

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

## Trusted workflow and candidate execution

The `pull_request_target` workflow comes from the trusted base. It tests the
exact PR head merged with the event's base revision. Candidate workflow edits
cannot replace the policy already checking that PR.

The workflow separates these roles:

1. **Source and contribution preflight** runs trusted integrity, history,
   freshness checks and administrative tests.
2. **Isolated candidate compilation** runs candidate Lean source in a disposable
   read-only-permission job and exports permitted `.olean` data.
3. **Isolated next-constants compilation** compiles only the standalone candidate
   constants source in a separate job. The proof build cannot replace this snapshot.
4. **Trusted canonical kernel audit** uses a fresh job and independent pinned
   dependencies. It downloads the two exact immutable artifact IDs, admits only
   expected `.olean` paths, replays the graph and checks the canonical interface.
   It never runs candidate code.
5. **Start required status** and **Report required status** are isolated status
   writers. They execute static Python, never check out candidate code, and are
   the only jobs with status-write permission.

Candidate-code jobs receive no repository secrets, persisted checkout credentials
or reusable Actions caches. Audit staging rejects native libraries, symlinks,
source files, protected-policy files and Mathlib or canonical-module shadows.
Only permitted compiled project modules and the independent snapshot cross the
boundary. Candidate code cannot edit the compiler, root or templates in the
separate audit job.

The final reporter succeeds only if every required job succeeds. Failed,
cancelled or skipped jobs are not success. It rechecks both PR head and target
base after the long proof checks. If either advances, verification must rerun
against the new trusted base and current constants.

Local verification runs local Lean metaprograms in the user's environment; it
is not an operating-system sandbox for hostile code. Separate hosted jobs provide
that boundary for untrusted contributions. Hashes are integrity checks, not
mathematical evidence or protection against a concurrent malicious local process
that can rewrite the verifier itself.

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

## Resources, logs and repository settings

Cold builds and independent replay can take hours. The earlier 26 October measurements
in [MIGRATION.md](MIGRATION.md#efficiency-revision--26-october-2026) distinguish
compiled artifact size from process memory: revised acceptance fixtures peaked
at 6.96 GiB, large polynomial compilations were sampled near 7.8 GiB, and
general entropy compilations exceeded 9 GiB per process. During complete replay,
the moment-cell worker was sampled at 21.12 GiB and the endpoint-prefactor
worker at 11.59 GiB. Those are prior-revision baselines; see the subsequent
[latest proof simplification measurements](MIGRATION.md#further-proof-evaluation-simplification--27-october-2026)
for the revised proofs and remaining resource limits.
These are local observations, not upper bounds or hosted-run measurements.
GitHub's [standard private Linux runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)
advertise 8 GB RAM. The revision therefore does not establish that the complete
build and audit fit those runners; process RSS also excludes other job overhead.
Build and replay use bounded dependency scheduling.
`SVB_BUILD_JOBS` and `SVB_REPLAY_JOBS` control local
parallelism. CI repository variables `LEAN_BUILD_JOBS` and `LEAN_REPLAY_JOBS`
select trusted concurrency, defaulting to one. Set `LEAN_RUNNER` to a suitably
sized **GitHub-hosted Linux** runner label when needed. Dependency installation
rejects self-hosted runners. Build and audit have 360-minute limits; a timeout
fails the gate. A cold serial run may exceed that limit, so rollout requires
appropriately sized hosted runners, memory-aware concurrency and an actual
hosted validation run. The default Ubuntu runner's capacity and runtime have
not been established by local tests. CI logs runner memory and disk availability,
each build target's start and completion, and aggregate build/audit resource use.

Open **Actions → Verification** and inspect the exact commit and job conclusions.
Artifacts include `canonical-proof-modules-<run_id>`,
`canonical-next-constants-<run_id>`, `candidate-build-log-<run_id>` and
`canonical-audit-<run_id>`. Artifacts may come from failed runs; they alone are not
evidence of success. The authoritative log includes module replay, source
coverage, axiom checks and the final 22-target acceptance marker.

The optional manual **Supplement build** workflow rebuilds the historical
document only. It is outside canonical verification and never reports
`CI required`. A separate PDF or prose proof is not a contribution requirement.

Default-branch protection should require **CI required**, GitHub Actions as its
expected source, up-to-date branches and pull requests, including for the
maintainer. Marcus Webb's approval is required for contributor PRs. His review-only
bypass for his own PRs does not waive CI or mathematics. Files cannot activate
repository settings; see the [maintainer guide](LAUNCH_CHECKLIST.md#github-settings).
No PR is created, merged or published by these local tools.
