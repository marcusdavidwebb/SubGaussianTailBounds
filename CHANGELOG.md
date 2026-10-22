# Changelog

## Unreleased

- Update the GitHub landing page with reading, verification and contribution
  routes, a live verification badge and a Python quickstart.
- Document existing-repository use, hosted Lean verification, maintenance PRs
  and local pre-PR comparisons; add a question and setup-help issue form.
- Separate ongoing maintainer/release procedures from the historical export
  and validation records. Preserve mathematical sources, dependency pins,
  contribution history and all verification gates.
- Preserve the pinned ProofWidgets release tag during hosted provisioning so
  Lake can locate its release archive; reject a tag that does not match the
  locked commit. Ordinary local verification still downloads nothing.
- Document required maintainer approval and the sole maintainer's review-only
  override for his own PRs, with mandatory CI applying to every PR.

## Initial repository setup — 22 October 2026

The repository is hosted on GitHub. This entry records its setup, not a
numbered release or publication of the accompanying paper.

- Adopt the MIT License for the supplementary repository on 22 October 2026,
  including its original code, proofs and documentation.
- Arrange the proof, exact checkers and pinned Lean sources as standalone
  repository contents.
- Supply bibliography and main-paper reference snapshots while retaining the
  original main-then-supplement workflow.
- Add contribution guidelines, substantial-contribution history and a complete
  evidence gate for constants improvements.
- Preserve both baseline quartets, theorem hypotheses and the hybrid trust
  boundary. Repository preparation makes no mathematical change.

The baseline verification observed on 20 October 2026 and its earlier history
remain in [VERIFICATION_REPORT.md](lean/VERIFICATION_REPORT.md) and
[verification_manifest.json](lean/verification_manifest.json).
