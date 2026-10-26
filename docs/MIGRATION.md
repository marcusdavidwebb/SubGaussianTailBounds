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
| `generalLower` | 681 moment cells, three plateau scalar families and both plateau-cost intervals. |
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
already installed on a target branch. This local change prepares its reviewed
replacement; it does not claim the hosted transition has been activated.

The new policy isolates candidate compilation, independently compiles the stable
next-constants snapshot, and loads only compiled module data into a fresh trusted
kernel audit. Modules become replay seeds only after their ancestors pass and
artifact hashes remain unchanged in that run. The audit checks exact canonical
types and universes, public theorem declarations and all mathematical dependencies.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Separate privileged
jobs report status and recheck the current base/head; candidate jobs receive no
write credentials or secrets. See [CI.md](CI.md).

Hosted runner sizing, runtime and branch-protection rollout remain maintainer
configuration and validation steps. No hosted run, PR publication, merge or remote
configuration change is asserted here. Local builds reused Lean 4.19.0, Mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b` and the existing pinned central packages;
no dependency or toolchain was installed, upgraded or replaced. All generated
configuration, caches and compiled outputs stayed outside the source checkout.

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
