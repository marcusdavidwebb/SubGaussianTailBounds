# Maintainer guide

The repository is hosted at
[marcusdavidwebb/SubGaussianTailBounds](https://github.com/marcusdavidwebb/SubGaussianTailBounds).
Readers should start with the [README](../README.md); contributors should use
[CONTRIBUTING.md](../CONTRIBUTING.md). This guide covers ongoing repository
settings, releases and source exports. Its filename is retained for existing links.

## GitHub settings

These settings live on GitHub; editing source files does not enable them.

1. Maintain the **About** description, useful research/formal-verification topics
   and a link to the supplementary PDF. Keep issues enabled with the correctness,
   constants-improvement and question forms.
2. Protect `main` with pull requests and the **CI required** commit status,
   selecting **GitHub Actions** as its expected source. Require branches to be
   up to date and enforce status checks for administrators too. Disallow force
   pushes and deletion. Its component jobs are **Contribution completeness**,
   **Exact certificates**, **Lean verification** and **Supplement build**; all
   must succeed. The final job is **Report required status**; the branch
   requirement is the status it posts, **CI required**.
3. In the separate **Maintainer approval** branch ruleset, require one approving
   review and codeowner approval from Marcus Webb, the sole maintainer named in
   CODEOWNERS. Dismiss stale approvals after changes.
   Permit only `marcusdavidwebb` to bypass the **pull-request review requirement**
   for his own PRs: GitHub rejects literal self-approval, so his decision to
   merge records his approval. Contributor PRs must receive his approval.
   GitHub's bypass is account-based, not author-conditional; use it only for
   maintainer-authored PRs. Required CI and up-to-date checks still apply to him.
   Keep this exception in the review-only ruleset, separate from mandatory CI
   protection. Do not grant an all-protections or status-check bypass.
4. Preserve the trusted base-revision maintainer list and `pull_request_target`
   workflow. Candidate jobs retain read-only permissions, no repository secrets,
   disabled credential persistence and no reusable Actions caches. Only isolated
   static status writers have `statuses: write`; they never execute candidate
   code. See [CI.md](CI.md).
5. Authorize genuine maintenance only with a maintainer comment
   `/ci-maintenance <40-character current HEAD SHA>`, then rerun PR CI. A new
   commit invalidates the authorization. Full regression checks still run;
   this never exempts an incomplete constants claim.

Inspect [hosted runs](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/workflows/ci.yml)
for the exact commit. Local macOS validation does not establish successful
Linux/GitHub execution. Test that an incomplete constants package fails and
that authorized documentation maintenance retains all regression checks.

## Release a verified snapshot

Repository releases are separate from publication of the accompanying paper.
The paper remains *in preparation* until a real public version is supplied.

1. Choose the release commit through the normal reviewed PR process. Verify that
   **CI required** and all component jobs passed for that exact commit on `main`.
   Do not release a queued, failed or partially checked snapshot.
2. Review the supplement PDF from that run's `supplement-<run_id>` artifact,
   including changed pages and the final citation/reference/box-warning checks.
   Confirm it corresponds to the release sources. Preserve the certificate log,
   Lean log/generated targets and document log before Actions artifacts expire.
3. Choose the actual version and publication date. Update [CHANGELOG.md](../CHANGELOG.md)
   and [CITATION.cff](../CITATION.cff) through the same verification process, with
   the chosen version, `date-released` and tag URL. The date must describe the
   repository release, not historical local verification or paper publication.
4. In [Releases](https://github.com/marcusdavidwebb/SubGaussianTailBounds/releases),
   create the tag at the exact verified final commit. Attach `supplementary.pdf`
   and verification logs/targets from its successful run. Include the full SHA,
   hosted run URL, baseline contribution IDs, changes and the hybrid trust
   boundary in the release notes. Review the draft before publishing.
5. Check the tag, assets, citation and download links after publication. Preserve
   previous releases and contribution credit. Never invent a paper DOI, public
   paper URL, verification result or release identifier.

Until a release exists, cite the exact commit using the
[README example](../README.md#citation-and-publication).

## Source export and historical setup

The initial preparation is recorded in
[REPOSITORY_VALIDATION.md](REPOSITORY_VALIDATION.md). Its dates, validation
results and then-pending tasks are historical evidence, not current status.
Ordinary users should clone the repository; they do not need an export step.

For an archival source-only copy including hidden GitHub files:

```sh
python3 scripts/export_repository.py /absolute/path/to/new-repository-folder
```

The destination must be a new directory outside this checkout. The exporter
retains the proof sources, `lean/`, `supplementary.pdf`, bibliography/label
snapshots, licence and `.github/`. It excludes Git history, dependencies,
compiled Lean outputs, caches, build logs and SyncTeX. It does not create a
repository or release. Preserve [LICENSE](../LICENSE), [LICENSING.md](../LICENSING.md)
and all third-party notices. Never use the parent paper's ignored-file list as
the inventory: it intentionally ignores its local Lean folder and generated PDFs.
