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

The canonical root SHA-256 remains
`eb24daadaf9c0aaac3bea45128a08b81ba5492183bcbb6eb03b62c3245c2701c`.
The digest detects drift; it is not mathematical evidence. Its complete
annotated README presentation is checked against the root bytes.

The 29 October instruction inventory included hidden, ignored and editor paths.
After retirement of the one-off `restructure_prompt.md`, only root `AGENTS.md`
remains. No nested AGENTS, CLAUDE, GEMINI, Copilot, Cursor, Windsurf, `.agents` or
`.codex` instruction files were present. The root canonical file must never be
edited, deleted, renamed, relocated, replaced or shadowed; future instructions
must repeat that prohibition without an exception.
