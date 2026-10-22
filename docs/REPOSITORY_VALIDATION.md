# Repository preparation validation — 21 October 2026

> Historical record: this describes the preparation before the repository was
> uploaded. The repository now exists on GitHub. Statements below about its
> creation, licensing and pending hosted checks describe their recorded dates.
> For current hosted results, see [Actions](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/workflows/ci.yml);
> for ongoing operations, see the [maintainer guide](LAUNCH_CHECKLIST.md).

This records validation of the portable repository preparation. It does not
replace the historical verification observed on 20 October 2026 or assert that
the GitHub repository, a public paper version, or a release exists.

## Mathematical sources and dependency pins

All 181 historical Lean source files (179 proof modules, the umbrella module
and the audit) match their recorded SHA-256 hashes. The original arithmetic
checker and eleven finite-interface Python sources are unchanged. Both
constant quartets and all theorem hypotheses are preserved. All nine locked
dependency records and revisions are unchanged; only their resolved storage
configuration is now generated externally.

The existing Elan installation and central pinned dependencies were reused.
Only the central Lake configuration and manifest symlinks were replaced with
resolved regular files; proof-source links and the existing project build
directory were preserved. No Lean toolchain or dependency was downloaded,
installed, upgraded, or replaced locally.

## Checks observed

- The portable Lean wrapper built the library and passed the complete audit:
  **3,224 targets**, **53,478 visited constants**, only `propext`,
  `Classical.choice` and `Quot.sound`, with checkpoint and import coverage.
- The original exact arithmetic checker and **all eleven** interface runners
  passed through `lean/check_certificates.sh`.
- Generated contribution obligations compiled for both exact baseline quartets
  under the original row assumptions and explicit finite certificate premises.
  The final end-to-end `./lean/check_hybrid.sh` run also passed: registry and
  exact claimed theorem checks, complete analytic audit, original arithmetic
  checker and all eleven interfaces.
- An actual negative Lean check changed the claimed general alpha from `96/25`
  to `19/5` while reusing the old theorem. Lean rejected the mismatched bound;
  the dependency audit also rejected the resulting `sorryAx` from error recovery.
- **23 unit tests** passed, covering missing evidence, PDF-only records, false
  certificates, changed assumptions, source/control changes, immutable history,
  and exact-head maintenance authorization.
- A complete exported tree was initialized as a temporary local Git repository
  outside the paper checkout. All 181 Lean sources and hidden GitHub workflow
  files were trackable; generated caches and editor artifacts were absent.
  A proof-only PR simulation failed the completeness gate. An explicitly
  authorized unchanged maintenance simulation passed. This temporary commit
  is not public history and is not included in an export.
- The workflow passed `actionlint` 1.7.7. Referenced action commits and the
  checksum-pinned Elan installer were checked against their upstream releases.
- The prescribed main-then-supplement LaTeX build passed. A clean standalone
  export also built successfully: **33 pages**, resolved references/citations,
  and no box warnings. The first page, final disclosure page and bibliography
  page were inspected. The distributed reading PDF is the standalone build,
  with no links to an absent `main.pdf`.
- The bibliography snapshot matches the shared parent bibliography exactly;
  the five paper-label numbers come from the actual built manuscript.

Local logs remained outside the source repository. The current source inventory
is [repository-inventory.json](repository-inventory.json); its hashes are drift
guards, not mathematical proofs or compiler-generated certificate exports.

## Hosted checks still to activate

The repository has not yet been created. Consequently the GitHub-hosted Linux
bootstrap, permissions/API status posting and branch-protection settings have
not been exercised live. Follow [LAUNCH_CHECKLIST.md](LAUNCH_CHECKLIST.md),
observe the initial hosted run, and require the exact-head commit status
**CI required** before accepting pull requests. See [CI.md](CI.md) for the
trusted base workflow and separation of read-only candidate execution from
isolated status writers.

Licensing was undecided at this validation on 21 October 2026. No release
identifier or publication date was invented. The existing external-Python
certificate correspondence and
human scholarly-review boundaries remain explicit.

## Main-paper repository reference update

Later on 21 October 2026, the main manuscript's repository placeholder was
replaced with the supplied planned URL and a description of the contribution
guidelines and credited history of verified constant improvements. The
manuscript remains 11 pages. Both the main-then-supplement build and refreshed
standalone supplement build passed with resolved references/citations and no
box warnings. Main-paper page 2 was visually inspected. The five reference
numbers are unchanged; their source digest has been refreshed. No mathematical
statement, proof source, certificate or dependency pin changed, and no new
formal-verification run is claimed by this editorial update.

## Main-paper Leiden disclosure

A short tool and computational resource disclosure was added before the main
paper's bibliography, following the Leiden Declaration's tool-disclosure
recommendations. It preserves the account of preceding human mathematical
work, identifies Codex as GPT-6 as reported by the authors, distinguishes
Lean's conditional analytic proof from external Python certificate checks,
and retains human responsibility for correctness and attribution. The full
disclosure remains in supplementary Section S2. Main-then-supplement and
standalone supplementary builds passed with resolved references/citations
and no box warnings. The main paper is now 12 pages, within the recorded
15-page limit; the supplement remains 33 pages. Main-paper page 11 was
visually inspected. Reference numbers are unchanged, and their source digest
has been refreshed. No mathematical or formal-verification source changed.

## MIT licensing — 22 October 2026

The maintainer selected the MIT License for the supplementary repository.
`LICENSE`, the licensing guide, citation metadata, contribution terms and
repository instructions now record that decision. Third-party material retains
its applicable terms. The source inventory includes the licence and refreshed
hashes for these documentation changes. No mathematical source or verification
setup changed; this entry does not claim a new Lean, arithmetic or LaTeX run.
