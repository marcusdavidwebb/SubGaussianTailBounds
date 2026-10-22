# Instructions for work on this repository

Read [README.md](README.md), [CONTRIBUTING.md](CONTRIBUTING.md),
[CONSTANTS.md](CONSTANTS.md) and [lean/README.md](lean/README.md) before changing
the proof or verification setup.

## Mathematical claims

- Preserve baseline quartets, hypotheses, MGF normalization, non-strict tail
  events and endpoints. Do not silently change the theorem.
- Improvement PRs require the complete registered readable proof, compiled
  Lean target, applicable exact certificates/checker mapping and history.
  A PDF or natural-language proof alone cannot pass the improvement gate.
- Never weaken an audit, omit a checker, add unsupported theorem assumptions,
  substitute the baseline for a new target or change CI to admit incomplete work.
- Maintenance authorization belongs to the trusted maintainer workflow;
  contributors cannot exempt their own claims.
- Read [docs/RESEARCH_PROTOCOL.md](docs/RESEARCH_PROTOCOL.md) before substantive
  mathematics. Keep correctness, attribution and novelty separate and preserve
  unresolved assessments until evidence resolves them.
- Preserve substantial credit and superseded records in
  [CONTRIBUTIONS.md](CONTRIBUTIONS.md). Do not invent publication metadata.

## Verification and storage

- Reuse compatible installed Lean tools and locked dependencies. Inspect the
  toolchain, Lake configuration and manifest before setup changes. Do not
  upgrade or replace dependencies during routine verification.
- Keep toolchains, dependencies, caches and compiled outputs outside this
  source checkout; keep editable proofs and small configuration here.
- Use `./lean/check_hybrid.sh` after proof/certificate changes, and the generated
  contribution obligations required by the PR workflow for claimed improvements.
  Keep Python assertions enabled.
- Preserve the hybrid trust boundary: Python supplies no Lean proof terms;
  source hashes are drift guards rather than semantic proofs.
- Build LaTeX with `./scripts/build_supplement.sh`; check citations, references,
  box warnings and changed pages. In the original paper checkout, retain the
  documented main-then-supplement build.
- Refresh bibliography/label snapshots with `scripts/sync_paper_assets.py`
  from actual existing paper sources; do not invent missing paper content.

## Provenance

Preserve Section S2's account of preceding human mathematical work, model
identity, tool roles and Marcus Webb's responsibility. Keep historical
validation dates, manifests and timings distinct from new portability/CI runs.

The paper is in preparation with no public version. Its intended GitHub URL is
supplied, but no public release identifier exists yet. The maintainer has selected
the MIT License for the project's original code, proofs and documentation;
preserve [LICENSE](LICENSE) and the scope described in
[LICENSING.md](LICENSING.md). Third-party material retains its own terms and
notices; preserve them.
