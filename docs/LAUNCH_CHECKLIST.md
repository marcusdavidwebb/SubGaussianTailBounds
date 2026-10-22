# Copy and launch checklist

Preparing files does not create the GitHub repository, publish the paper or
enforce GitHub checks.

## Copy

1. Include and preserve the [MIT License](../LICENSE). Review
   [LICENSING.md](../LICENSING.md) and retain applicable third-party notices.
2. Build/review the PDF; run hybrid and contribution checks on the prepared tree.
   Report the new run separately from historical validation.
3. Create the empty intended repository,
   `https://github.com/marcusdavidwebb/SubGaussianTailBounds`.
4. Copy this folder's **contents** to its root, including hidden `.github/`,
   `.gitignore` and `.latexmkrc`. Do not add an extra `supplementary/` level.
5. Include `lean/` and `supplementary.pdf`. The parent paper intentionally ignores
   its local Lean folder and generated PDFs: its tracked-file list is not an
   export inventory.
6. Exclude build directories, `.lake/`, toolchains, dependencies, caches, compiled
   Lean outputs, logs, SyncTeX and system metadata. Do not copy the parent `.git/`.

The root includes public guides, `contributions/`, `lean/`, `scripts/`, `docs/`,
the LaTeX/PDF, bibliography snapshot and `.github/`.

To make a clean copy including the hidden files, run:

```sh
python3 scripts/export_repository.py /absolute/path/to/new-repository-folder
```

The destination must not already exist. This excludes generated artifacts while
retaining `supplementary.pdf` and all proof sources; it does not initialize Git,
create a remote, commit, or publish anything.

## Enable policy on GitHub

1. Run the included workflow on the initial commit. Linux/GitHub-hosted CI must
   be observed there; local macOS validation alone does not demonstrate it.
2. Protect the default branch with required PR/codeowner review and the
   **CI required** commit status, selecting **GitHub Actions** as its expected
   source. Require branches to be up to date before merging. Its component jobs
   are **Contribution completeness**, **Exact certificates**, **Lean verification**
   and **Supplement build**; all must succeed. The final job is named
   **Report required status**; the branch requirement is the status it posts,
   **CI required**.
   Dismiss stale approvals after new commits and do not allow administrators to
   bypass required CI. GitHub does not count a PR author's own approval: if you
   require an approving review for owner-authored PRs too, appoint another
   trusted reviewer before enabling that requirement.
3. Require maintainer/CODEOWNERS review for workflow, gate and policy changes.
   Confirm the trusted base-revision maintainer list initially names
   `marcusdavidwebb`. The trusted base supplies the `pull_request_target` workflow.
   Candidate jobs must retain read-only permissions, no repository secrets,
   disabled credential persistence and no reusable Actions caches. Only isolated
   static status writers have `statuses: write`; they never check out candidate
   code. See [CI.md](CI.md).
4. A maintenance exception requires an authorized maintainer comment
   `/ci-maintenance <40-character current HEAD SHA>`, then a manual rerun of PR CI.
   A new commit invalidates it. There is no persistent contributor-set label
   bypass. Full regression checks still run.
5. Test an incomplete constants PR: a PDF/readable proof without its registered
   Lean/certificate package must fail. Confirm a genuine documentation PR can
   use the authorized maintenance route without skipping regressions.
6. Enable issues; review templates and credit policy. Record public PR/commit
   and release links only once they exist.

## Publication metadata

The paper remains *in preparation* until a real public version is supplied.
Update README, citation metadata and supplement consistently when it changes.
Do not invent DOI, public paper URL, release date or identifier. A future release
should identify its actual commit and checks; the earlier local baseline
validation date is not a release date.
