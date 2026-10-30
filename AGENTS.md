# Instructions for this Lean repository

Read [README.md](README.md), [CONTRIBUTING.md](CONTRIBUTING.md) and
[lean/README.md](lean/README.md) before changing proofs or verification.

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
  `e62053135682c168816033858a78828abbf34fe47c3b2f9e9db44f6d6fb828b5`.
  Compare bytes before and after work. A digest detects drift; it is not a
  mathematical proof. The README copy must match the full annotated source.
- Inventory repository-local AI instructions, including hidden/editor files,
  when introducing or changing instructions. The current inventory is in
  [docs/HISTORY.md](docs/HISTORY.md).

## Proofs and contributions

- Preserve both canonical baseline propositions, arbitrary sample-space
  universes, hypotheses, MGF normalization, non-strict events and endpoints.
- Either regime may be replaced at componentwise no larger constants than both
  its baseline and current accepted quartet. Equality is allowed; preserve the
  other regime and all accepted improvements. Marcus Webb decides acceptance.
- Contributions are complete Lean sources, comparison proofs, concise explanation
  and attribution, and a [CONTRIBUTIONS.md](CONTRIBUTIONS.md) entry. No separate
  prose/PDF proof or external mathematical certificate is required.
- Never weaken exact-type, universe, kernel, source-coverage or axiom checks,
  introduce unsupported assumptions, or accept conditional results as complete.
  Review verification-policy changes explicitly; candidate changes cannot replace
  the accepted policy for their own assessment.
- Follow the research and attribution rules in [CONTRIBUTING.md](CONTRIBUTING.md).
  Preserve the human and model roles, responsibility, historical validation and
  unresolved assessments in [docs/PROVENANCE.md](docs/PROVENANCE.md).

## Verification and storage

- Marcus Webb runs `./lean/verify.sh` locally before merging each PR. CI performs
  administrative checks only; green CI is not proof verification. Agents must
  not open a PR without explicit approval for that PR, merge it or enable auto-merge.
- Run `./lean/verify.sh` after proof or verification changes, and
  `python3 scripts/check_canonical_statement.py` after canonical-facing
  documentation or setup changes. Report incomplete checks honestly.
- Preserve independent kernel replay and the axiom allowlist: `propext`,
  `Classical.choice`, `Quot.sound`. Python and hashes establish no mathematical
  truth; finite proof obligations must be checked in Lean.
- Reuse installed Lean and compatible locked dependencies. Inspect the toolchain,
  Lake configuration and manifest before setup changes. Do not install, clone,
  upgrade or replace dependencies during routine verification.
- Keep toolchains, dependencies, caches and build outputs outside this checkout;
  use this project's own external workspace under `~/Lean/`. Follow the central
  Elan/package/cache locations documented in [lean/README.md](lean/README.md).
- Preserve [LICENSE](LICENSE), [LICENSING.md](LICENSING.md) and third-party notices.
  Do not invent paper publication metadata, verification dates or releases.
