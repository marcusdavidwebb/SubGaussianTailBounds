# Canonical Lean migration and validation

The maintained formalization now supplies both exact canonical baseline proofs,
including every finite numerical condition. The Python mathematical certificate
pipeline and its contribution registry have been retired. There is one evolving
Lean implementation and one [contribution history](../CONTRIBUTIONS.md).

## Source and workflow map

| Area | Maintained role |
|---|---|
| Authoritative statement | Root `MainTheoremStatement.lean`, preserved byte for byte and compiled at its actual location. |
| General baseline | `Canonical/General.lean`: `SingularValueBounds.Canonical.general_baseline`. |
| Unit baseline | `Canonical/Unit.lean`: `SingularValueBounds.Canonical.unit_baseline`. |
| Public interface | `Canonical/Results.lean`: `SubGaussian.Current.general`, `unit`, baseline corollaries, recorded-quartet equalities and comparisons. |
| Correspondence and monotonicity | `Canonical/Adapter.lean` connects the existing matrix/probability library to the root definitions; `Canonical/Monotonicity.lean` proves componentwise weakening. |
| Exact constants | `Canonical/AcceptedConstants.lean` records declarative exact expressions. Independent Lean obligations tie these to the proved quartet and the trusted preceding ceiling. |
| Supporting mathematics | `lean/SingularValueBounds/`, including all concrete finite proofs under `KL/Certificates/`. Supporting modules can be replaced or removed after a replacement passes. |
| Verification | `./lean/verify.sh`: immutable source check, bounded build, whole-source coverage, independent module kernel replay, exact public/acceptance types, and the standard axiom allowlist. |
| Contribution policy | Either regime may be replaced, including at unchanged constants. No component can increase against either its baseline or trusted accepted quartet. There is no maintenance exemption. |
| Credit | One initial contribution credited to Marcus Webb in `CONTRIBUTIONS.md`; substantial preceding credit, tool roles and superseded evidence are preserved. |
| Historical exception | `supplementary.tex` and its PDF remain temporary historical documents, outside mathematical acceptance. Their optional manual build is separate. |

The permanent targets retain arbitrary sample-space universe `u`:

```lean
SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5
SubGaussian.UnitSingularValueTailBound.{u} 1.32 1.12 2.32 (Real.sqrt 2)
```

The public results leave no certificate or analytic premise unproved. Positivity,
all admissible dimensions and probability spaces, directional MGF normalization,
non-strict measurable tail events, endpoints, zero singular values and `ℝ≥0∞`
probability bounds remain those of the immutable source. The adapters and
monotonicity were separately reviewed against that source.

## Reused mathematics and completed finite obligations

The analytic library's conditional lemmas remain useful components. Their eleven
concrete fields are now supplied by Lean proofs, assembled by
[`finalCertificateConditions`](../lean/SingularValueBounds/KL/Certificates/ConcreteFinal.lean).
The two canonical proofs use the corresponding regime-specific components.

| Field | Concrete Lean coverage |
|---|---|
| `generalLower` | 681 indexed moment cells and their separate endpoint, three plateau scalar families and both plateau-cost intervals. |
| `endpointLowerTable` | All eight boxes. |
| `endpointLowerFar` | All five intervals. |
| `majorant` | Six exact factorizations and all 165 boxes. The largest row's 70 independent leaves are split into ten build/replay blocks. |
| `normDeterminant` | All prescribed determinant inequalities. |
| `rate` | All 15 upper-rate rows and 83 leaves. |
| `generalMeanCells` | Partition, 2,016 clipped covers and scalar domains, and 1,330 polynomial row certificates. |
| `generalMeanEntropy` | Small range and 1,330 rows, each with 121 exact error nodes and 120 critical margins. |
| `endpointMean` | Grid/domain/rate/prefactor conditions, 50 small-range entropy bounds, 3,348 active corner bounds, and all 837 polynomial boxes. |
| `endpointLogratio` | All prescribed logarithmic-ratio inequalities. |
| `generalSecond` | Small range and 334 cells, including 1,002 moment margins. |

Integer recurrences, exact rounding bounds, polynomial coefficient identities,
affine changes of coordinates and Bernstein reconstruction are proved in Lean.
Generated rational data is accepted only after kernel-checked identities and
inequalities. Python arithmetic, source hashes and table presence establish no
mathematical fact. No generator or executable copy of the retired mathematical
pipeline is kept in the working tree.

Retired files include `check_main_constants.py`, the numerical/interface checkers
under `lean/`, `check_certificates.sh`, `check_hybrid.sh`, their checker mapping
and verification manifest, the old declaration checkpoint, and the JSON registry
and proof-package templates. Git history and the historical reports preserve
what they checked. Remaining Python tools perform administration or document
support only.

## Immutable statement and instruction inventory

The initial and final root SHA-256 are:

```text
eb24daadaf9c0aaac3bea45128a08b81ba5492183bcbb6eb03b62c3245c2701c
```

The file was initially untracked and was preserved rather than reset to HEAD.
The canonical source guard rejects shadows and checks the complete README
presentation. CI uses the guard and expected digest from trusted policy, so a
candidate cannot evade protection by changing its own expected hash. The digest
checks immutability, not mathematical truth.

The instruction inventory included hidden, ignored and editor-specific paths
with `rg --files --hidden --no-ignore -g '!.git/**'`. Only root `AGENTS.md` and
the user-supplied `restructure_prompt.md` were instruction sources. Both prohibit
editing, deleting, renaming, moving, replacing or shadowing the root source,
including for formatting, compatibility or maintenance. No nested AGENTS,
CLAUDE, GEMINI, Copilot, Cursor, Windsurf, `.agents` or `.codex` instructions were
present. Future instruction files must preserve the same prohibition.

## Trusted-policy transition

The preceding trusted gate required strict improvement, allowed certain
tradeoffs, froze baseline implementation paths, and required the old registry
and prose/certificate package. Candidate workflow edits do not alter that policy
already installed on a target branch. The maintainer has selected the new gate
as the intended policy; the retired checks do not determine its mathematical
requirements. The transition is under review in
[PR #2](https://github.com/marcusdavidwebb/SubGaussianTailBounds/pull/2).
This does not claim that the default-branch transition has been activated.

The new policy isolates candidate compilation, independently compiles the stable
next-constants snapshot, and loads only compiled module data into a fresh trusted
kernel audit. Modules become replay seeds only after their ancestors pass and
artifact hashes remain unchanged in that run. The audit checks exact canonical
types and universes, public theorem declarations and all mathematical dependencies.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Separate privileged
jobs report status and recheck the current base/head; candidate jobs receive no
write credentials or secrets. See [CI.md](CI.md).

Hosted runner sizing, runtime and branch-protection rollout remain validation
and configuration steps. No successful hosted run, merge or remote configuration
change is asserted here. Local builds reused Lean 4.19.0, Mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b` and the existing pinned central packages;
no dependency or toolchain was installed, upgraded or replaced. All generated
configuration, caches and compiled outputs stayed outside the source checkout.

## Further proof evaluation simplification — 27 October 2026

This revision starts from `313a88d` and preserves the canonical statement,
constants, polynomial coefficients, finite inequalities and rounding algorithms.
It reuses standard polynomial uniqueness and the existing proved integer
recurrences. It claims no new mathematical result or novelty. Dependencies and
verification policy are unchanged.

The plateau proofs now establish their large polynomial identities from degree
bounds and exact evaluations: 101 integer points for the degree-100 cost
polynomials and 100 points for the degree-99 scalar numerators. The scalar proof
then cancels the same nonzero factor `X²`. Integer affine and Bernstein transforms
certify the original interval coefficients and signs. All **28 existing theorem
headers**, including the five public statements, and **29 rational coefficient
vectors** remain text-identical. The five modules and both aggregate modules
compiled; the new helper and all five modules passed fresh compact kernel
replay with only `propext`, `Classical.choice` and `Quot.sound`.

Matched direct compilations used the same pinned Lean compiler, `-j2`, saved
sources and already-built dependencies:

| Representative module | Original/revised user CPU seconds | Original/revised peak RSS | Original/revised `.olean` bytes |
|---|---:|---:|---:|
| Plateau cost 0 | 105.89 / 33.46 | 6.21 / 3.48 GiB | 139,824,680 / 1,187,368 |
| Plateau scalar row 0 | 152.38 / 75.76 | 5.57 / 3.75 GiB | 66,745,272 / 1,167,568 |

Matched compact replay measurements were **67.64 / 28.59 CPU seconds** and
**6.37 / 4.26 GiB** for cost 0, and **122.04 / 68.63 CPU seconds** and
**5.75 / 4.24 GiB** for scalar row 0. The revised direct pilots include their
helper declarations locally; the maintained implementation shares one helper.
The five maintained source files plus that helper grow by **32,726 bytes
(4.78%)**. Their compiled artifacts shrink from **423,276,016 to 4,368,192 bytes (98.97%)**,
including the new shared helper. The original total comes from the preceding
complete run's artifact manifest; its five source hashes match `313a88d`.

The general polynomial modules now set `Elab.async false`, serializing proof
elaboration while retaining the same kernel checks. Removing that single added
line reproduces every byte of each of the nineteen original blocks. In the
matched complete 70-cell Block15 pilot, peak RSS fell from **5.52 to 3.62 GiB**,
user CPU time from **373.18 to 314.84 seconds**, and elapsed time from **324.87 to
318.84 seconds**. This is a polynomial block, not an entropy block.

All **19 general polynomial blocks** compiled in a six-worker queue, taking
**1,261.36 seconds elapsed** and **6,792.51 summed user CPU seconds**. Individual
maximum child RSS ranged from **3.16 to 3.76 GiB**. Source hashes remained stable
during those builds; the final artifacts total **192,945,648 bytes**. This family
was fully drained before whole-project verification.

Endpoint corner bounds now follow uniformly from the spectral grid and 43
scalar endpoints. The endpoint joint-prefactor domain checks and the general
prefactor domains use exact whole-function integer logarithm rewrites. These
preserve the original reduction fuel, 18 logarithm terms, remainder, base-two
constants and rounding steps. The measured compilation comparisons are:

| Module | Original/revised user CPU seconds | Original/revised peak RSS |
|---|---:|---:|
| Endpoint mean corner bounds | 31.89 / 2.06 | 5.69 / 2.41 GiB |
| Joint prefactor domains | 465.21 / 152.93 | 5.87 / 3.06 GiB |
| General prefactor domains | 121.54 / 42.37 | 4.13 / 2.86 GiB |

General entropy proofs share exact exponential nodes for 440 repeated slopes;
291 singleton slopes retain direct evaluation. Each shared table proves equality
to the original rounded exponential at all 121 grid nodes. Balanced integer
lookups and noncomputable proof-only tables avoid unnecessary lookup and
executable-code work. The existing 10,650 theorem headers and 160,930 stored error
integers are preserved.

All **19 general entropy blocks**, **28 shared-table modules** and the lookup
helper compiled. The original complete 70-row Block00 used **1,115.98 user CPU
seconds and 12.73 GiB peak RSS**. The final sequential production Block00 used
**573.54 CPU seconds and 5.506 GiB**; charging all 48 first-use sequences and the
new helper gives **723.99 CPU seconds**, a **35.1% reduction**. The earlier
asynchronous shared pilot used less CPU but retained much more memory, so the
sequential form was selected. The other production row commands peaked below
4.10 GiB; the conservative maximum for the complete family remains 5.506 GiB.
The original and asynchronous scratch pilots used direct Lean with `-j1`;
the final production command used Lake's pinned `-j2` configuration and the
separately verified helper/import changes. The final comparison therefore
measures that implementation combination, not an isolated scheduling experiment.

The general entropy artifacts shrink from **365,232,424 to 209,800,592 bytes
(42.6%)**, including every new table and helper. Explicit lookup tables and
smaller proof declarations increase source from **6,680,995 to 12,505,545 bytes
(87.2%)**. The production Block00 also passed independent compact kernel replay:
**473.33 user CPU seconds**, **4.282 GiB peak RSS**, and 1,118 theorem declarations
checked, with only the three standard axioms. All family builds and probes
finished before the complete verification run.

Endpoint entropy proofs split corner evaluations into small lemmas and reuse
**1,532 of 3,348** evaluations from adjacent boxes. Exact rate-inclusion and
value-equality proofs justify each reuse; the eleven interior boxes without the
required inclusion retain direct checks. All **837 box and 60 row public
statements**, and all **5,859 numerical data definitions**, remain identical.
The rounded-logarithm helpers were extracted from `ConcreteGeneralMeanSmall`;
32 endpoint log modules and five small-range entropy blocks now import that
small helper directly, avoiding an
unrelated general-certificate dependency. The obsolete rational evaluator is
superseded by the exact shared integer rewrite.

A matched complete endpoint Row28 compilation fell from **491.56 to 337.85 user
CPU seconds** and **8.094 to 3.799 GiB peak RSS**. That revised scratch pilot
includes its shared helper declarations locally. The maintained production row,
which imports the helper, separately passed at **361.01 CPU seconds and
3.814 GiB** under concurrent family builds.

All **60 endpoint entropy rows** compiled, including the eleven rate-extension
exceptions. The 12-worker family build took **19 minutes 4 seconds**, with
**13,196.28 summed user CPU seconds** and **3.814 GiB maximum child RSS**.
The smaller explicit proofs increase these rows' source from **15,151,373 to
17,232,298 bytes** and their compiled artifacts from **99,158,200 to
117,659,760 bytes (18.7%)**. The two shared helpers add **194,472 artifact bytes**.
This is a measured memory/CPU saving with a storage cost, not an artifact-size
reduction. The simpler corner-only pilot had a larger artifact expansion and
was not adopted.

All 32 log modules, five small-range blocks, both helpers and the endpoint
entropy aggregate also compiled. The production Row28 passed independent
compact kernel replay: **335.23 user CPU seconds**, **4.463 GiB peak RSS**, and
413 theorem declarations checked, with only the three standard axioms. All
endpoint workers finished before the complete verification run.

All RSS figures are **individual maximum child-process values**, not aggregate
machine memory. Concurrent workload prevents treating these wall times as an
isolated throughput comparison or a cold whole-project timing. Compact module
probes do not replace complete source coverage, same-run artifact checks,
independent replay and exact canonical acceptance. Local measurements alone do
not establish that the complete gate fits a particular hosted runner.

The superseded `FastRoundedLog` source and its umbrella import were removed after
the integer replacement built. The canonical integrity guard and all 75
administrative tests passed (111 tests discovered; the 36 Lean fixtures were
intentionally skipped and are not claimed as rerun).

The preceding new-policy [hosted run at `313a88d`](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/runs/40376509656)
passed preflight and the constants snapshot, then lost contact with its runner
during candidate compilation. GitHub's annotation lists CPU/memory starvation
and network interference as possible causes; it does not establish an
out-of-memory failure or a rejected Lean proof. Independent auditing did not run.

A read-only check on 27 October found no repository Actions variable overrides.
The maintained workflow specifies defaults of one build worker, one replay
worker and an `ubuntu-24.04` runner. The parallel local measurements do not
establish cold serial hosted runtime or memory capacity. No runner settings,
timeouts or verification requirements were changed in this proof revision.

The unchanged complete command passed with exit code **0** on **27 October
2026, 14:56:45–15:30:57 UTC**:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONOPTIMIZE= SVB_BUILD_JOBS=28 SVB_REPLAY_JOBS=32 ./lean/verify.sh
```

The run checked **527 build targets**, freshly replayed **all 528 modules**,
and accepted **all 22 canonical targets**. Its final axiom audit covered
**75,610 targets and 135,921 visited constants**, with only `propext`,
`Classical.choice` and `Quot.sound`. All **553 recorded proof/setup/source
hashes** remained unchanged throughout verification. The canonical source and
full README presentation still match the fixed digest.

Elapsed time was **2,051.85 seconds**; accumulated child CPU time
(user plus system) was **14.10 hours**. Maximum child-process RSS was
**6,805,012,480 bytes (6.338 GiB)**. This is not aggregate concurrent
memory. Most numerical modules were built during development; the final command
checked their traces and rebuilt affected dependants before fresh complete
replay. It is not a cold whole-project timing or a hosted-run measurement.

Active project/acceptance artifacts, including all new helpers, total
**1,117,065,312 bytes across 528 modules**, compared with
**1,677,737,528 bytes across 497 modules** in the preceding
complete run: **33.42% fewer bytes**. This measures active `.olean` files,
not total disk use, caches or archived validation records.

The log, source hashes, individual measurements, preserved benchmark sources and
artifact identities are retained outside the checkout under
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/validation/20261027T145645Z-entropy-plateau-simplification/`.


## Efficiency revision — 26 October 2026

The revision reduces memory use without changing the canonical statements,
baseline quartets or dependency pins. Shared polynomial identities and separable
coefficient checks replace expanded algebra proofs in the majorant and rate
certificates. All **248 original leaf statements and their original coefficient
vectors** remain byte-for-byte identical. The mathematical implementation now
uses explicit Mathlib imports. The dependency environment induced by those
imports falls from **7,944 to 4,260 imported modules**, and from **1,171,624 to
771,620 declarations**, including their Lean/Std and other transitive dependencies.
The import-only changes preserve their proof bodies.

Measured compiled proof sizes after rebuilding the affected families are:

| Compiled artifacts | Before | After | Reduction |
|---|---:|---:|---:|
| Complete majorant family, including aggregates | 2,373,155,920 bytes | 45,982,984 bytes | 98.06% |
| Fifteen rate rows | 591,326,912 bytes | 68,889,320 bytes | 88.35% |

These are artifact sizes, not peak process memory. The small general-mean
certificate also reuses 121 exact node values, verified through the existing
integer exponential/logarithm algorithms. Its ten public theorem statements
remain unchanged. The original compilation was sampled above **13.4 GiB RSS**;
the complete revised-module pilot measured **3.82 GiB peak RSS**, with an artifact
increase from 350,152 to 741,008 bytes. Its 40.57-second pilot and the original
363.2-second build ran under different concurrent loads and are not a controlled
speed comparison.

The verifier derives one independent protected-name inventory, reuses already
loaded module data in its planner, and loads only actual imports in workers.
The full inventory remains responsible for global collision checks. Workers use
a small module-name inventory and genuine pinned constant records. Each module
audits every fresh safe, nonpartial declaration before independent kernel replay;
the scheduler combines complete same-run reports. The final continuation checks
exact types and universes without repeating the full-library axiom traversal.
Standalone auditing retains its complete checks. The common gate and CI build
also avoid a duplicate whole-library diagnostic. See [CI.md](CI.md) for the
unchanged trust requirements and the compositional audit argument.

The independently generated full inventory was 84,081,714 bytes; the worker
module inventory was 385,759 bytes. A representative `Core.Constants` worker's
measured peak fell from **2.85 to 2.52 GiB** with identical report sets. Inventory
generation itself measured **4.81 GiB peak RSS**. These scoped measurements do
not establish a complete hosted run or an upper bound for every worker.

After the complete rebuild, the exact **490-module** replay plan contained
**1,727,305,024 compiled artifact bytes (1.61 GiB)**. Fresh resource probes
measured **4.80 GiB** for independent inventory generation, **4.07 GiB** for
planning and **3.65 GiB** for the final type-checking continuation. The earlier
final-auditor probe measured 14.50 GiB. These measurements reflect both the
smaller proof artifacts and verifier changes; they are not an isolated benchmark
of either change. A continuation probe measures resources only and cannot
substitute for the full scheduler's kernel replay and axiom audit.

Sampling active workers during the complete replay revealed remaining numerical
proof bottlenecks: **21.12 GiB RSS** for `ConcreteMomentCells` and **11.59 GiB**
for `ConcreteEndpointPrefactors`. These are point-in-time observations, not
lifetime maxima. They make the whole-job limitation explicit: smaller planner
and final-checker phases do not establish that all compilation or replay fits
an 8 GB hosted runner. These tables were addressed in the subsequent
[proof simplification](#proof-simplification--26-october-2026) recorded below.

All **111 unique regression tests** passed against this revision: 75
administrative tests and 36 actual Lean fixtures (18 acceptance, nine module
replay, eight stable-snapshot and one source-freshness case). The administrative
discovery's 36 intentional skips are accounted for by those separate Lean runs.
The final acceptance suite took 571.54 seconds and measured **6.96 GiB maximum
child RSS**; the module-replay suite took 558.89 seconds and measured **4.92 GiB**.
Synthetic fixture imports were narrowed, and actual Lean worker concurrency in
those fixtures is one. Lightweight scheduler tests retain concurrent-DAG
coverage. Propositions and hostile cases are unchanged; private declarations,
unused native-oracle definitions and quoted helper names are covered.

### Complete validation of the efficiency revision

After rebuilding the affected dependency chains, the full common verification
command passed with exit code **0**:

```sh
PYTHONDONTWRITEBYTECODE=1 SVB_BUILD_JOBS=28 SVB_REPLAY_JOBS=32 ./lean/verify.sh
```

The run started at **11:48:36 UTC** and finished at **12:35:36 UTC** on
26 October 2026, taking **2,819.35 seconds (46 minutes 59.35 seconds)**.
Lake checked all **489 module source traces** without requiring recompilation;
all **490 compiled modules** then passed fresh independent kernel replay. Exact
types, universes and comparisons passed for all **22 acceptance targets**. The
axiom audit covered **53,214 targets and 112,553 visited constants**, permitting
only `propext`, `Classical.choice` and `Quot.sound`. Recorded source hashes were
unchanged throughout the run.

The measured maximum child-process RSS was **23,617,683,456 bytes (22.00 GiB)**;
this is not the sum of simultaneous workers. Total child CPU time was about
**21.66 hours**. These measurements confirm that further work is needed for a
small hosted runner, despite the smaller audit infrastructure and proof
artifacts. This was a warm build followed by complete fresh verification, not a
cold build. The different replay concurrency and audit coverage also prevent a
controlled runtime comparison with 25 October.

The complete log, validation result, source hashes and supporting measurements
are retained outside the checkout in the project workspace under
`validation/20261026T114836Z-efficiency/`. They are evidence of this run, not
cached authorization to skip any later verification step. The historical
validation below remains a separate record.

## Proof simplification — 26 October 2026

This subsequent revision changes the finite proof construction, with the canonical
statements, quartets, approximation definitions, truncation orders and required
margins unchanged. It uses the existing Taylor enclosures, rounding inequalities
and Bernstein reconstruction; it makes no new theorem or novelty claim.

- `UniformEndpointPrefactors` proves a coarse uniform bound for the actual rounded
  logarithm and both outer rounding operations. The bound supplies all **1,150**
  small endpoint-prefactor conditions without individual numerical evaluations.
- `MomentCellSideConditions` derives eight of each moment certificate's eleven
  fields from its grid and existing analytic enclosures. Only the domain, shape
  and entropy margins require cell-specific arithmetic. All **681 indexed cells**
  and the separate endpoint remain proved.
- `GeneralSecondSideConditions` similarly derives six grid, domain and exponential
  sign fields for all **334 second-moment cells**. The fourth-moment exclusions
  and all **1,002 moment margins** remain required.
- The **837 endpoint polynomial boxes** use smaller proved degree bounds: **787** use
  `(6,15)` and **50** use `(4,1)`, replacing the uniform `(8,16)` padding. The
  internal certificate records sufficient degree bounds; its consumer still uses
  the same polynomial nonnegativity theorem. Box choices and rectangles are
  unchanged.
- `IntegerCoefficientStages` and its degree-eight specialization convert rational
  affine and Bernstein transforms
  into exact integer identities with positive common denominators. It supplies
  the 787 larger endpoint boxes and **1,286 general polynomial certificates**;
  the 50 small endpoint and 44 small general norm certificates retain simpler
  rational checks. The general certificates include 1,054 degree-`(6,15)` and
  232 degree-`(8,15)` boxes. Degree-six, degree-eight and degree-fifteen Bernstein
  weight identities are shared. Every coefficient identity and final sign remains kernel checked.
- `IntegerMomentEvaluation` evaluates exponential, logarithm and moment sums by
  exact integer recurrences. `ExactMomentEvaluation` proves the finite-sum
  identities used to establish equivalence with the original rational formulas,
  including their original remainder expressions. No floating-point arithmetic
  or external proof oracle supplies a mathematical fact.

The remaining moment and second-moment decisions are split into **22** and
**11 private theorem blocks**, each covering at most 32 cells within the existing
source modules. Quotient and remainder lemmas prove complete coverage; the final
partial blocks exclude only padding entries. Separate theorem declarations bound
Lean's temporary checking caches. The unchanged replay gate checks every new
private theorem as well as every public result.

Fresh module builds against already-built pinned dependencies measured:

| Module | Original peak child RSS | Revised peak child RSS | Reduction |
|---|---:|---:|---:|
| `ConcreteMomentCells` | 22,751,117,312 bytes (21.19 GiB) | 4,096,638,976 bytes (3.82 GiB) | 82.0% |
| `ConcreteGeneralSecondCells` | 19,526,959,104 bytes (18.19 GiB) | 3,426,566,144 bytes (3.19 GiB) | 82.5% |

Baselines invoked `lake env lean -j2` on saved original sources; revised builds
used `lake build` with the same two compiler threads. The original and revised
moment builds used **402.89** and **93.68 user CPU seconds** respectively. They ran under different concurrent loads; their
454.11- and 233.43-second wall times are not an isolated speed comparison. A
uniform-prefactor module build measured **2.36 GiB** peak with its helper already
built; there is no matched original module-build measurement for that family.
These are scoped compilation measurements, not a full-job memory bound. The
combined savings include both generic proofs and changed evaluation/checking
structure; they cannot be attributed to integer arithmetic alone. Some compiled
artifacts grow because explicit reusable proofs replace expensive reductions.
The endpoint polynomial source shrinks from **14,684,449 to 10,973,427 bytes**.
The general polynomial source grows from **9,417,168 to 18,922,104 bytes** because
four explicit integer stages replace a single rational table; combined row/block
source size grows **24.0%**, excluding shared helpers. These tables discharge
smaller, shared algebraic obligations.

All sixty rebuilt endpoint polynomial row artifacts total **173,165,712 bytes**,
down from **203,821,824 bytes** (15.04%). Their largest measured compilation
child RSS is **3,609,968,640 bytes (3.36 GiB)**. The shared endpoint coefficient
identity artifact shrinks from **32,170,360 to 20,624,408 bytes** after removing
unused padded coefficients and identities. These artifact totals exclude shared
helper modules and are separate from process-memory measurements. All nineteen
general polynomial modules compiled too, with a maximum child RSS of
**6,114,164,736 bytes (5.69 GiB)**. Their artifacts total **196,685,024 bytes**,
down from **210,087,448 bytes** in the preceding full replay plan (6.38%).

Fresh target kernel-and-axiom replays using the compact worker path measured
**4,279,812,096 bytes (3.99 GiB)** for moment cells and **3,891,740,672 bytes
(3.62 GiB)** for second-moment cells. Both passed with only the three standard
axioms. Their protected module inventory was derived afresh beforehand; that
separate inventory phase measured **4.81 GiB**. Standalone checks that construct
the full inventory inside the same process instead measured **8.17** and
**7.82 GiB**. These target probes do not replace the full scheduler's ancestor,
coverage, artifact-hash and exact-type obligations.

The same verification scripts, CI workflow, protected statement and dependency
pins are retained. The **75 administrative regression tests** passed again;
the 36 actual Lean verifier fixtures were last run for the preceding efficiency
revision, and are not counted as rerun here.

Complete `./lean/verify.sh` validation passed on **26 October 2026**, from
**16:04:13 to 17:02:03 UTC** (3,470.24 seconds). The run checked all **496 build
targets**, freshly replayed **497 modules**, and accepted all **22 canonical
targets**. The axiom audit covered **78,699 targets and 138,068 visited constants**,
with only `propext`, `Classical.choice` and `Quot.sound`. All **522 recorded source
and setup hashes** remained unchanged. Build and replay concurrency were 28 and
32 respectively; stale affected modules were rebuilt, so this is neither a cold
whole-project build nor a warm-build timing comparison.

Maximum child-process RSS was **16,068,165,632 bytes (14.97 GiB)**, excluding the
sum of simultaneous workers. Total child CPU time was **24.62 hours**. The
unchanged `ConcreteGeneralSecondBounds` worker reached that peak in replay;
unchanged endpoint entropy compilations were sampled near **7.94 GiB**. Thus this
revision does not establish that complete verification fits an 8 GB runner.
The log, source hashes, resource record and supporting measurements are retained
outside the checkout under
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/validation/20261026T160413Z-proof-simplification/`.
The earlier validation records remain separate historical evidence.

## Further finite-proof simplification — 26 October 2026

The follow-up keeps the same mathematical statements, grid data, coverage trees,
rounding definitions and numerical margins. It changes three existing proof
modules and leaves the verifier and dependency pins unchanged.

- `ConcreteGeneralSecondBounds` reuses the proved integer exponential recurrence
  and eleven private blocks of at most 32 cells. All **334 × 3 upper margins**
  remain required. The final block covers 14 actual cells; quotient and remainder
  lemmas recover every original index without using padding as a substitute.
- `ConcreteEndpointMeanGeometry` proves the box-domain conditions uniformly from
  the grid definitions, replacing **2,520 indexed checks**, and proves the small
  total bound uniformly instead of checking 50 values. The remaining joint-grid
  cutoff and selected-majorant lookup checks use twelve bounded clauses; the
  small one-dimensional grid checks are retained. All nine original public
  propositions are unchanged.
- `ConcreteGeneralMeanGeometry` checks the same **2,016 clipped-tree witnesses**
  in twelve blocks and the same **1,330 row domains** in 42 blocks. The original
  decidability procedures, partition proof and three public propositions are
  unchanged. The last domain block has 18 real entries and 14 guarded padding
  entries.

Matched direct compilations used the same pinned `lake env lean -j2` command on
saved original and revised sources, with already-built dependencies:

| Module | Original peak RSS | Revised peak RSS | Original/revised user CPU seconds |
|---|---:|---:|---:|
| Second-moment upper bounds | 14.11 GiB | 3.19 GiB | 78.67 / 26.27 |
| Endpoint geometry | 7.07 GiB | 3.41 GiB | 62.43 / 31.28 |
| General geometry | 8.05 GiB | 5.39 GiB | 49.75 / 45.08 |

These are individual process peaks, not aggregate machine-memory bounds.
Explicit private proofs increase source and artifact size in exchange for
smaller checking tasks. Compact replays passed at **3.71 GiB** for second-moment
upper bounds,
**3.77 GiB** for endpoint geometry and **4.54 GiB** for general geometry, with
only the three standard axioms. These probes do not replace the full gate.

A separate rounded-logarithm recurrence prototype proved exact but did not show
sufficient resource savings: one general-row sample changed from 3.78 to
3.78 GiB and an endpoint sample from 4.99 to 4.90 GiB, with slightly larger
artifacts. It was not added to the maintained sources. No new mathematical
result or novelty is claimed.

Complete `./lean/verify.sh` passed on **26 October 2026**, from **17:13:59 to
18:16:52 UTC** (3,773.12 seconds): **496 build targets**, **497 fresh
module replays**, and all **22 canonical targets**. The audit checked
**78,871 targets and 138,245 visited constants**, with only `propext`,
`Classical.choice` and `Quot.sound`. All **522 source/setup hashes** remained
unchanged. The **75 administrative tests** also passed; the 36 separate actual
Lean verifier fixtures were not rerun for these proof-only changes.

The maximum child-process RSS was **8,662,745,088 bytes (8.07 GiB)** and total
child CPU time was **27.22 hours**, with 28 build and 32 replay workers.
This is not aggregate concurrent memory. Dependent numerical modules were rebuilt,
but this was not a cold build of every source and dependency. Unchanged endpoint
entropy compilation was sampled above **8 GiB**; fitting the complete job on an
8 GiB hosted runner remains unestablished. The unchanged general entropy modules
also retain their earlier cold-compilation resource concerns.

Logs, source hashes, artifact identities and supporting measurements are retained
outside the checkout under
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/validation/20261026T171359Z-continued-proof-simplification/`.

## Completion validation — 25 October 2026

Both canonical theorem assemblies and the public `Canonical.Results` interface
compiled successfully. Separate exact-type and axiom checks passed for the
completed endpoint finite families. The full common verification command then
passed with exit code **0**:

```sh
PYTHONDONTWRITEBYTECODE=1 SVB_BUILD_JOBS=28 SVB_REPLAY_JOBS=28 ./lean/verify.sh
```

The run started at **17:19:10 UTC** and finished at **18:10:39 UTC** on
25 October 2026. Its measured elapsed time was **3,088.52 seconds**
(51 minutes 28.52 seconds). Both build passes checked all **489 module source
traces** without requiring recompilation. This is a warm-build timing followed
by a fresh, complete independent replay, not a cold-build timing.

All **490 compiled modules** passed independent kernel replay. The exact-type,
universe and comparison checks passed for all **22 acceptance targets**. The
final axiom audit covered **52,596 targets and 112,111 visited constants** and
reported only `propext`, `Classical.choice` and `Quot.sound`. The command ended
with `PASS: complete canonical Lean targets, comparisons, and axiom audits.`
The earlier whole-source audit in the same run separately checked 52,573
targets and 112,071 visited constants before the generated acceptance module.
The complete logs and Lean source hashes are retained in this checkout's external
Lean workspace under `validation/20261025T171910Z/`. These historical records are
not used to skip any future verification step.

The completed regression coverage comprises **104 unique tests**: 71 repository
administration tests and 33 Lean fixtures (17 acceptance, eight stable-snapshot,
seven compiled-module replay and one Lake freshness test). They cover either-regime
and unchanged
replacements, preservation of accepted improvements, missing comparisons,
conditional/wrong/universe-restricted targets, forged compiled declarations,
namespace/syntax attacks, unused forbidden axioms and native-oracle dependencies,
artifact integrity, source-copying discrepancies, and source changes with preserved
file size and timestamps. All passed. The final
administrative discovery intentionally skipped the 33 separately executed Lean
fixtures; those skips are not counted as successful Lean executions.

The first full run passed both builds and the whole-library axiom audit, then
stopped because its duplicate-declaration guard rejected Lean's lazily generated
equation theorems. Inspection found 530 structurally identical duplicate theorem
records. The corrected guard compares every theorem field, including the proof
expression and universes; it still rejects every trusted-base collision and every
conflicting declaration. Sibling copies replay independently; a copy in a verified
ancestor can reuse only that identical, already replayed theorem. The new positive
and adversarial fixtures exercise these cases. The corrected plan was followed
by the complete 490-module kernel replay and final acceptance checks reported above.

Warm build checks now use Lake's normal source-content traces and `--no-build`;
stale targets still use the bounded compiler scheduler. Independent kernel replay
is never cached or skipped. A preliminary global `--rehash` probe changed a cached
ProofWidgets hash; that change was restored, the global rehash option was removed,
and the shared dependency checkout was confirmed unchanged. No installation or
dependency replacement was used to resolve it.

Final source hygiene checked **487 maintained modules**, exactly 487 direct
umbrella imports, and **147 relative documentation links**, with no missing
targets or anchors. Canonical immutability and README correspondence, shell
syntax, workflow validation with the existing `actionlint` 1.7.7, contribution
preflight and `git diff --check` passed. No compiled outputs,
dependency trees, caches or retired checker/registry files remain in the source
checkout. The historical supplement, dependency pins and licence are unchanged.

## Earlier migration session — 23 October 2026

The following records the state at the end of that earlier session, before the
unit proof was completed. It is separate from the completed hybrid validation
on 20 October 2026 and the completion run above.

These observations are separate from the earlier hybrid validation:

- The actual immutable root module, full maintained library,
  `Canonical.General`, and `Certificates.ConcreteFinal` compiled with the pinned
  Lean 4.19.0 environment. The general theorem was applied at arbitrary universe
  `u` to the exact canonical baseline type, without a certificate premise.
- The general theorem's transitive axiom report contains only `propext`,
  `Classical.choice`, and `Quot.sound`. The compiled source audit covers
  **17,359 targets and 86,886 visited constants**, preserves the earlier
  checkpoint, and confirms complete KL/canonical import coverage with the same
  allowlist. This source audit is distinct from the independent kernel replay
  required by the hardened verification command.
- All **55 Python regression tests** passed. The **13 Lean acceptance tests**
  were exercised by the full suite and targeted reruns, including exact-type
  syntax attacks and forged compiled declarations. One initial 120-second
  compilation timeout under concurrent proof load passed on rerun with the
  increased fixture timeout; no assertion failure remained.
- Both generated legacy contribution targets compiled and their two-target
  audit completed. These remain historical conditional obligations.
- The original exact arithmetic checker and **all eleven finite interfaces**
  passed. Their result was external evidence for the then-unfinished unit
  obligations, not a Lean proof of them.
- The canonical byte/README check, local documentation links, shell syntax and
  `git diff --check` passed. A clean source export passed the same canonical
  byte/README guard. No Lean compiled outputs, dependency trees or
  Python bytecode remain in the source checkout. The historical supplement,
  dependency pins and license files were not changed.

The full `./lean/check_hybrid.sh` build succeeded. Its new independent kernel
replay was stopped after approximately **15 minutes** to stay within the
requested two-hour task limit. It had produced no rejection, but no completed
replay report either. The full end-to-end hybrid run therefore **did not pass**
during that session; the component checks above are reported separately.
Completing kernel replay and validating hosted runtime were still outstanding.
At that time, `./lean/verify.sh` exited unsuccessfully as intended because the
complete unit result and combined `Canonical/Results.lean` acceptance entry point
were absent. No PR was created or published.

## Further efficiency options

These are unimplemented proposals, not promises of total runtime savings.
They apply to the maintained complete Lean gate and must preserve exact pins,
source coverage, trusted isolation, independent kernel replay, axiom auditing
and canonical type checks. General decay caching and plateau simplification
are implemented above and are no longer future recommendations.

A source-import review found that `Canonical.Results` reaches **522 of 525**
maintained modules, including every numerical family and canonical maintenance
interface. The three outside that closure total only **977,496 artifact bytes**:
`ProfileIntegralRegularity`, `EndpointEntropySum` and the documented public
`ConcreteFinal` bundle. Whole-module pruning therefore offers little demonstrated
storage benefit, and reachability alone does not authorize retiring public APIs
or imply RAM/runtime savings.

- **Share repeated general critical-log evaluations.** Two independent exact
  recounts find 159,600 occurrences but 31,185 distinct rational arguments:
  15,101 arguments repeat and 16,084 occur once. A checked shared table could
  avoid 128,415 repeat reductions (80.46% of this subcalculation). These are
  operation counts, not measured runtime savings; benchmark table size and
  proof/import overhead first.
- **Share endpoint logarithms across the scalar parameter.** The remaining
  direct corner proofs contain 121,148 distinct-rate-per-corner inputs but only
  3,880 exact logarithm arguments. Their exponential prefactors would still need
  checking. Benchmark checked tables and their import costs before adoption.
- **Factor the endpoint corner-transfer proof.** The 766 eligible adjacent boxes
  each have two similar transfer arguments. A generic lemma and one shared
  rate-inclusion witness per box could reduce duplication and the current
  endpoint artifact growth. This has not been benchmarked.
- **Measure the remaining large workers before changing module boundaries.**
  Use the new complete run to identify any residual compiler or replay peak.
  Smaller independent declarations or modules may help those specific cases,
  but older rational-proof and entropy measurements do not describe the revised
  implementation. Account for additional imports, startup and audit work.
- **Batch dependency-ready build targets.** Pinned Lake 4.19 accepts several
  targets in one invocation, sharing setup and dependency traversal. It has no
  CLI cap on simultaneous module builds; `-j2` limits compiler threads instead.
  Keep bounded outer batches and measure idle time behind slow targets.
- **Fetch only needed disposable CI caches.** Snapshot and compilation jobs
  could fetch the locked import closures they actually need. Trusted auditing
  still requires full Mathlib for its independent protected-name inventory.
  Candidate-produced artifacts must not become trusted dependency caches.
- **Prebuild the trusted replay executable.** Compiling the trusted verifier
  once could reduce repeated worker startup. Candidate modules must still be
  loaded only as data and receive the same kernel, axiom and type checks.
  Measure startup, memory and total-run effects before adoption.
- **Cancel remaining build processes promptly after failure.** The scheduler
  could stop only its own active subprocesses when a required target fails,
  preserving failure logs and the failed result. This saves failed-run work,
  not successful-run mathematical checking.
- **Continue separating generic helpers from concrete certificates where
  imports justify it.** The shared logarithm evaluator already moves the
  logarithm-fuel helpers. Further extraction should follow actual remaining
  dependencies; its principal benefit is avoiding unrelated rebuilds.
- **Shard CI across isolated jobs.** Compilation or replay could be distributed
  with complete coverage and immutable artifact identities. Replay shards must
  establish that all imported project ancestors passed verification in the same
  run. Include transfer costs and duplicated trusted setup in any speed claim.

## Hosted CI timeout and staged verification — 28 October 2026

The new-policy [run 40532161924](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/runs/40532161924)
at `44787105a898a45cb98fb7c3c3812f8d72502204` did not finish. GitHub's job
annotation explicitly reports that candidate compilation exceeded **six hours**.
The build log shows **311 of 527 modules completed**, followed by general entropy
Block10 still running at cancellation. Blocks00–09 each completed in
**768–813 seconds**. The runner reported **7.8 GiB RAM** and **3 GiB swap**;
only one build worker was configured. No Lean proof error was reported before
the timeout. Preflight and standalone constants compilation succeeded; the
independent kernel audit was skipped. This is a failed verification run, not
mathematical acceptance, and the failure has no demonstrated connection to the
retired base workflow's checks.

The maintainer selected splitting work across standard runners. Compilation
and independent replay now each have eight dependency stages, with up to eight
one-worker shards per stage. A deterministic planner partitions depth bands,
keeps dependent modules within a band together, and balances components using
source or compiled artifact sizes. These sizes guide scheduling only. All
modules must occur exactly once, all earlier dependencies must have completed,
and same-stage dependencies cannot cross shards. The final compilation checks
all Lake source traces and builds the exact acceptance obligations.

Audit stages use independent pinned environments and only data-only candidate
modules. A checkpoint binds the exact run and attempt, head/base/policy revision,
complete compiled graph and hashes, completed modules and accumulated axiom and
declaration reports. Each stage requires all eight exact producer artifact IDs;
no candidate artifact or name-selected receipt can establish prior replay.
Active shards derive fresh inventories and plans and check artifact identity
before and after replay. The final fresh audit requires all modules before
checking the exact 22 canonical obligations and full source/axiom coverage.
The ordinary local gate still performs complete fresh replay without checkpoints.
Use **Re-run all jobs** after a hosted failure: mixing attempts is rejected.

Administrative regressions cover omitted or repeated modules, backward and
cross-shard dependencies, wrong attempts/revisions, modified artifacts, incomplete
checkpoints and missing/duplicate shard reports. A real installed-Lean build
fixture restores only preceding-stage artifacts into empty build directories
for all 64 shard invocations; Lake confirms all earlier targets remain current,
including their source traces. Actual kernel fixtures accept valid parent/child
continuations and reject a forged child after its legitimate parent passed.
These synthetic fixtures test gate mechanics; they do not prove the tail bounds.

The canonical statement, both proof implementations, quartets, Lean 4.19.0 and
locked Mathlib/dependencies are unchanged. Checkpoint transfer adds storage,
setup and network overhead. Applying the actual compiled-module partition to the previous local replay
log gives a largest shard of **35.3 minutes** of recorded module durations.
This projection excludes fresh setup and transfer work and is not a measurement
or runtime bound for the revised hosted workflow. A complete successful hosted run is still required.

The complete local `./lean/verify.sh` rerun on **28 October 2026** passed in
**1,674.25 seconds**. Lake confirmed all **527 source traces** current; the gate
then freshly replayed **528 modules** and accepted all **22 canonical targets**.
The audit covered **75,610 targets / 135,921 visited constants**, with only
`propext`, `Classical.choice` and `Quot.sound`. This was a warm compilation check
plus complete fresh replay, using 28 build and 32 replay workers while separate
fixtures and a resource probe also ran. It is not a cold hosted performance
measurement. The final staged-audit implementation separately passed both real
Lean continuation/rejection fixtures; its obsolete interrupted development run
is not counted as validation.

A separate optional resource probe compiled the unchanged trusted replay worker
as a native executable, using the existing Lean installation. Parsed reports
matched for three valid modules, and the fresh pinned inventories matched.
General entropy Block00 used **4.341 / 2.999 GiB** peak RSS in interpreted/native
runs; endpoint Row28 used **4.528 / 3.222 GiB**. These are approximately **31%** and
**29%** reductions for those processes. Concurrent verification affects timing
comparisons. Native execution is **not included in this repair**: these positive
probes do not replace a complete native canonical run and adversarial fixtures.
It remains a further memory-saving option to validate separately.

The full regression suite passed **146 tests**, including all **39 installed-Lean
fixtures**, in **2,027.85 seconds**. The two staged-audit fixtures were additionally
rerun successfully after the final inventory-memory adjustment. The new
`audit-prepare` shell path was exercised in a separate external workspace using
the full project artifacts and existing pinned dependencies; it staged the data
and planned all 528 modules successfully, without claiming completed replay.
Canonical integrity, contribution preflight, workflow boundary tests, YAML and
shell syntax, changed documentation links and `git diff --check` also passed.
All logs and planning/probe evidence are retained outside the source checkout in
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/validation/20261028T001959Z-ci-stages/`.
These local checks do not assert that the new hosted run has completed.

GitHub rejected the first dispatch of the staged workflow before creating a run:
`runner.temp` is unavailable in job-level `env`, even though the YAML parses.
Workspace paths now enter `GITHUB_ENV` from setup steps, matching the original
workflow's approach. All **10 workflow boundary tests** passed after this
correction, including executing the build/audit path-selection shell code and
rejecting runner-context expressions in job-level environments. The proof
sources and verifier logic were unchanged by this workflow-expression fix.
