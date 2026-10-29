# Instructions for work on this repository

Read [README.md](README.md), [CONTRIBUTING.md](CONTRIBUTING.md),
[CONSTANTS.md](CONSTANTS.md) and [lean/README.md](lean/README.md) before changing
the proof or verification setup.

## Immutable canonical statement

- `MainTheoremStatement.lean` is the single authoritative statement. Preserve
  its exact root location, name and bytes, including imports, comments,
  definitions and universe parameters. Do not edit, delete, rename, relocate,
  replace or shadow it. There is no exception for formatting, compatibility,
  proof development or maintenance; future instruction files must repeat
  this prohibition without granting an exception.
- Put proofs and adapters in other modules that import the actual root file.
  Report mathematical or compatibility problems precisely without changing
  the canonical source or weakening the required theorem.
- The observed SHA-256 is
  `eb24daadaf9c0aaac3bea45128a08b81ba5492183bcbb6eb03b62c3245c2701c`.
  Compare bytes before and after work. A digest detects drift; it is not a
  mathematical proof. The README copy must match the full annotated source.
- Inventory repository-local AI instructions, including hidden/editor files,
  when introducing or changing instructions. The current inventory is in
  [docs/MIGRATION.md](docs/MIGRATION.md).

## Mathematical claims

- Preserve baseline quartets, hypotheses, MGF normalization, non-strict tail
  events and endpoints. Do not silently change the theorem.
- The target is one maintained formalization with complete universe-polymorphic
  Lean proofs of both canonical baseline propositions. Contributions may
  replace either regime at componentwise no larger constants than both its
  baseline and trusted current accepted quartet. Equality in all entries is
  allowed, subject to Marcus Webb's acceptance decision. No current component
  may increase; preserve the other regime and every accepted improvement.
- Contributions consist of Lean sources, checked comparison proofs, concise
  explanation and attribution, and Markdown history. Do not maintain or accept
  separate natural-language proofs, PDF proofs or Python certificate packages
  as the new contribution route. `supplementary.tex` and its PDF are temporary
  historical exceptions, not documents to update with future Lean changes.
- Never weaken canonical type, kernel or axiom verification, add unsupported
  theorem assumptions, substitute the baseline for a new target, or change CI
  to admit incomplete work. Conditional helper theorems are not accepted results.
- No contributor or maintenance route can exempt mathematical claims from
  complete verification. Verification-policy changes require trusted review;
  candidate workflow edits cannot change the policy already running on the base.
- Read [docs/RESEARCH_PROTOCOL.md](docs/RESEARCH_PROTOCOL.md) before substantive
  mathematics. Keep correctness, attribution and novelty separate and preserve
  unresolved assessments until evidence resolves them.
- Preserve substantial credit and superseded work in
  [CONTRIBUTIONS.md](CONTRIBUTIONS.md), with one initial contribution credited
  to Marcus Webb covering both regimes. Do not invent publication metadata.

## Verification and storage

- CI runs administrative repository checks only. Marcus Webb runs the complete
  `./lean/verify.sh` locally before merging each PR; green CI is not evidence of
  Lean verification. Preserve this manual check and all its mathematical checks.
- Reuse compatible installed Lean tools and locked dependencies. Inspect the
  toolchain, Lake configuration and manifest before setup changes. Do not
  upgrade or replace dependencies during routine verification.
- Keep toolchains, dependencies, caches and compiled outputs outside this
  source checkout; keep editable proofs and small configuration here.
- Run `./lean/verify.sh` after proof or verification changes, and
  `python3 scripts/check_canonical_statement.py` after canonical-facing
  documentation or setup changes. Retired Python mathematical checkers must not
  return as an acceptance dependency. Administrative Python establishes no
  mathematical truth; all concrete finite proof obligations are checked in Lean.
- Source hashes are drift guards, not semantic proofs. Preserve independent
  trusted auditing of candidate declarations and the standard axiom allowlist.
  Report actual checks and remaining gaps honestly; never call an interrupted
  build or audit a successful verification.
- Build LaTeX with `./scripts/build_supplement.sh`; check citations, references,
  box warnings and changed pages. In the original paper checkout, retain the
  documented main-then-supplement build.
- Refresh bibliography/label snapshots with `scripts/sync_paper_assets.py`
  from actual existing paper sources; do not invent missing paper content.

## Provenance

Preserve Section S2's account of preceding human mathematical work, model
identity, tool roles and Marcus Webb's responsibility. Keep historical
validation dates, manifests and timings distinct from new portability/CI runs.

The repository is hosted at https://github.com/marcusdavidwebb/SubGaussianTailBounds.
The paper is in preparation with no public version. Repository releases are
separate from paper publication; record release identifiers only when they exist.
The maintainer has selected
the MIT License for the project's original code, proofs and documentation;
preserve [LICENSE](LICENSE) and the scope described in
[LICENSING.md](LICENSING.md). Third-party material retains its own terms and
notices; preserve them.
