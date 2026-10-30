# Verification history

The project maintains complete Lean proofs of both baseline propositions in
the immutable root `MainTheoremStatement.lean`. No improved quartet has been
accepted. Current setup is in [lean/README.md](../lean/README.md), the checked
interface in [VERIFICATION.md](VERIFICATION.md), and credit in
[CONTRIBUTIONS.md](../CONTRIBUTIONS.md) and [PROVENANCE.md](PROVENANCE.md).

## Recorded checks

| Date | Scope and result |
|---|---|
| 20 October 2026 | Historical hybrid verification: 147 KL and 32 shared modules, 3,224 audited declarations, plus external Python arithmetic. This did not prove either complete canonical baseline in Lean. |
| 23 October 2026 | The general canonical theorem was completed. The unit theorem remained unfinished, and an interrupted replay was not counted as success. |
| 25 October 2026 | Both canonical theorems completed. Full verification passed: 490 replayed modules, 22 targets, 52,596 audited declarations / 112,111 visited constants; 3,088.52 seconds with 28 build/replay workers. All 104 then-current regression tests passed. |
| 26–27 October 2026 | Uniform bounds, shared integer evaluations, bounded proof blocks and polynomial degree/evaluation arguments simplified the finite proofs without changing constants or numerical specifications. Detailed measurements and limitations remain in the archived record below. |
| 28 October 2026 | Full local verification passed: 528 replayed modules, 22 targets, 75,610 audited declarations / 135,921 visited constants; 1,674.25 seconds with 28 build / 32 replay workers. All 146 then-current tests passed, including 39 Lean fixtures. |
| 29 October 2026 | Lean checking moved out of CI at the maintainer's request. A fresh full local run passed on revision `73aa7fe4db3d982d446e292d82a34b6af784238b`: the same 528 modules and 22 targets, in 1,656.75 seconds with 28 build / 32 replay workers. Administrative CI also passed. |

These full local timings use current compiled source traces followed by fresh
independent replay. They are not cold-build measurements or runtime bounds.
Only `propext`, `Classical.choice` and `Quot.sound` were permitted. Historical
results never skip a later check. The initial policy-adoption runs used
self-comparison; later contributions must compare with the accepted base.

The hosted six-hour timeout and subsequent staged-CI attempt were unsuccessful
verification runs. Hosted Lean checking is retired; green CI now means only
administrative checks passed.

## Lean-only cleanup — 29 October 2026

At the maintainer's request, the supplement, PDF, bibliography and paper-build
tools were removed. Retired CI installation, sharding and artifact-transfer
scripts and duplicate whole-library diagnostics were removed as well.
`./lean/verify.sh` is the single complete verification entry point. Proof declarations,
constants, the canonical source, Lean 4.19.0 and locked dependency revisions
remain unchanged. Current documentation is consolidated around setup,
contributing and verification.

Lightweight validation passed: 76 administrative tests, with the 36 installed-Lean
fixtures skipped, plus canonical integrity, documentation links, shell/YAML syntax
and whitespace checks. The complete replay and installed-Lean regression run
were stopped at the maintainer's request. Neither is recorded as successful;
full verification of the simplified entry point is deferred.

## Reading and navigation cleanup — 29 October 2026

The six operational Python tools now live together in `scripts/`. Replay also
validates its final report, replacing the separate report-checker script. CI
uses the event's comparison base directly and checks the live head/base once,
before reporting success. Its duplicate early API helper was removed.

Lean checking programs and two readable Lean templates are grouped under
`lean/Verification/`. The templates replace long Python string literals; all
nine compared generated-source variants and all three relocated Lean checking
programs are byte-for-byte identical to their predecessors. Mathematical
sources, canonical bytes and dependency pins are unchanged. README and the
repository map provide the reading path and describe each remaining part.

The administrative suite passed: 78 tests, with 36 installed-Lean fixtures
skipped. Source guards, the external workspace path, syntax and documentation
links were checked separately. Full Lean compilation and replay remain
deferred at the maintainer's request; these refactoring checks do not replace them.

## Historical sources

These immutable Git links preserve the original detail without maintaining
obsolete instructions alongside the formalization:

- [Full migration, proof changes, measurements and validation logs](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/docs/MIGRATION.md)
- [20 October hybrid verification report](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/lean/VERIFICATION_REPORT.md)
- [Historical formalization plan](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/lean/FORMALISATION_PLAN.md)
- [Repository preparation and original inventory](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/docs/REPOSITORY_VALIDATION.md)
- [Historical supplement source, including Section S2's disclosure](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/supplementary.tex)

Local verification logs remain outside the source checkout, under the project's
`~/Lean/SubGaussianTailBounds/<source-path-digest>/validation/` directory.

## Canonical source and instructions

At the maintainer's explicit request on 30 October 2026, the preceding
byte-preservation restriction was revoked for a canonical statement rewrite.
The subsequent clarification required equivalence with the natural-language
theorem in the README, retaining both sharp regimes, exact constants, arbitrary
sample-space universes, measurability and non-strict tail events.

The first rewrite bundled the original row assumptions and tail conclusions
using local definitions. Lean 4.19.0 compiled that intermediate root, its two
equivalence proofs, the adapters and public general/unit results. Administrative
checks passed 78 tests, with 36 optional Lean fixtures skipped. The complete
`./lean/verify.sh` run was stopped during compilation at the maintainer's request;
independent kernel replay was deferred. These historical logs remain in the
older external workspace's `validation/statement-simplification-20261030.log`
and `validation/statement-public-results-20261030.log`.

The maintainer then clarified that “import” meant an actual NLA-lib dependency,
and authorized the compatible Lean/Mathlib upgrade. The current 80-line source
imports NLA-lib's row predicates and singular values directly. Its variance proxy
is `K²`, and its singular-value indices retain zero singular values. The new
`Canonical/NLARows.lean` and `Canonical/NLASingularValues.lean` bridge these imported
definitions to the original assumptions and extrema. `StatementEquivalence.lean`
proves equivalence with both preceding expanded propositions for arbitrary
quartets and sample-space universes. Existing proof modules receive API
compatibility changes for Mathlib 4.33.1.

Lean 4.33.1 is installed through central Elan. NLA-lib commit
`6491e7528c1b1e68e46301cde6a76ae153e8e834`, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` and their locked dependencies live under
`~/Lean/SubGaussianTailBounds/<source-path-digest>/nla-4.33.1/.lake/packages/`.
The prior Lean 4.19.0 environment and the SingularValueBounds dependency tree
remain separate. No dependency sources, compiled outputs or bulky dependency
symlinks are stored in this repository. Routine setup still reuses installed,
exactly pinned dependencies and never installs or updates them.

The original root SHA-256 was
`eb24daadaf9c0aaac3bea45128a08b81ba5492183bcbb6eb03b62c3245c2701c`.
The intermediate local-definition rewrite had SHA-256
`8527f13f9a79531eb226f1ce276b000fa780955a54b91d352a0e5845ed8aa760`.
The imported canonical root SHA-256 before the probability-bound revision was
`e62053135682c168816033858a78828abbf34fe47c3b2f9e9db44f6d6fb828b5`.
The digest detects drift; it is not mathematical evidence. Its complete
annotated README presentation is checked against the root bytes.
The executable source guard is repinned to these explicitly requested new
bytes; its shadow checks and the kernel, axiom, exact-type and universe
requirements remain in force. A trusted checkout with the previous digest or
dependency pins intentionally rejects this revision until the maintainer adopts
the updated statement and setup policy.

The Lean 4.33.1 compatibility migration is complete. The following checks passed
on 30 October 2026:

- All 530 Lean source modules compiled, including all 487 KL modules, both sharp
  canonical theorems and the umbrella module. The official bounded build tool
  subsequently checked every source trace and reported all 530 targets current.
- Both full statement equivalences compiled for arbitrary quartets and
  sample-space universes. Their axiom reports contain only `propext`,
  `Classical.choice` and `Quot.sound`.
- All 22 generated canonical acceptance obligations compiled and passed the
  supplemental audit of actual checked proof bodies against the same axiom
  allowlist.
- The default administrative test run passed 78 cases, with 40 opt-in Lean
  fixtures skipped. Separately, all nine constants-source parser fixtures,
  two split-import elaboration-audit fixtures and one plan-only rejection of
  split project artifacts passed. The canonical source guard and whitespace
  checks also passed.

The proof port changes imports, API spellings, coercions and tactics while
preserving the numerical certificate data, hypotheses and sharp bounds.
Build outputs and retained logs are in the central workspace; the validation
directory is `validation/nla-imports-20261030/`. The three selected split-module
fixture results were recorded in the tool transcript rather than saved logs.
Independent kernel replay and the complete `./lean/verify.sh` run were deferred
at the maintainer's request. These compilation and regression checks therefore
do not constitute a completed verification run under the repository policy.

The 29 October instruction inventory included hidden, ignored and editor paths.
After retirement of the one-off `restructure_prompt.md`, only root `AGENTS.md`
remains. No nested AGENTS, CLAUDE, GEMINI, Copilot, Cursor, Windsurf, `.agents` or
`.codex` instruction files were present. The root canonical file must never be
edited, deleted, renamed, relocated, replaced or shadowed; future instructions
must repeat that prohibition without an exception.

The 30 October inventory again included hidden and ignored/editor paths and
found only root `AGENTS.md`. Its observed digest now identifies the revised
canonical source; its protection applies to that revised source.

## Real-valued probability bounds — 30 October 2026

At Marcus Webb's explicit request and authorization for this change,
`SingularValueTails` now takes an `IsProbabilityMeasure μ` instance and states
each probability bound using `(μ event).toReal`. No separate finite-measure
assumption is added: the probability-measure instance supplies it. A separate
[Lean equivalence](../lean/SingularValueBounds/Canonical/TailEquivalence.lean)
connects these real inequalities with the preceding `ENNReal.ofReal` inequalities
under that instance. Both measurable non-strict
events, thresholds, constants and arbitrary sample-space universes remain.

The probability-bound revision initially had canonical root SHA-256
`7f2bef4ec5acf22cb8898fc6552e68c8a64901a944e4526ca952af08ffbee906`.
This digest detects byte drift, not mathematical correctness. The earlier
compilation and audits above apply to the earlier source, not this revision;
they do not establish complete verification of either revision. This one
explicit authorization does not permit future unauthorized changes to the root.

## Canonical helper simplification — 30 October 2026

Marcus Webb subsequently removed the unused `open scoped ENNReal` and an
explanatory comment from the canonical source. At his request, Codex then
removed the unused `SingularValueTails` proof argument and its two call-site
arguments, retaining the `1 ≤ n` hypothesis in both full theorem statements.
The direct `Isotropic` import was also removed because the pinned sub-Gaussian
import supplies it transitively. The helper's Lean API changes; the theorem
hypotheses, tail bounds and arbitrary sample-space universes do not. A temporary
Lean variant established equivalence of the prior and simplified helper and
both full propositions by `Iff.rfl`.

The maintainer-edited intermediate source had SHA-256
`509c3f4dedb627edb14c2d43801be99ef9b8a43c8dbb4244420176c1c5d65193`.
The simplified root has SHA-256
`be2804e4ca5ef33015df07e84f0544540f36c69f1be7bb4503c3363cb105f3a3`.
The authorization is specific to these changes; the prohibition on future
unauthorized canonical changes remains in force. The interrupted full verifier
from before the maintainer edit did not complete independent kernel replay.

For the simplified source, Lean 4.33.1 compiled the canonical statement,
probability and statement equivalences, adapters and public results. The
canonical source guard and the Python regression suite passed (118 tests run,
40 skipped). The complete verifier was started and stopped at the maintainer’s
request before independent kernel replay. The preceding trusted checkout rejects
the new digest, so the policy change still requires separate adoption.
