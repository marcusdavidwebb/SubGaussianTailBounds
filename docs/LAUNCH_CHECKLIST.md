# Maintainer guide

The repository is hosted at
[marcusdavidwebb/SubGaussianTailBounds](https://github.com/marcusdavidwebb/SubGaussianTailBounds).
Readers should start with the [README](../README.md); contributors should use
[CONTRIBUTING.md](../CONTRIBUTING.md). This guide covers ongoing repository
settings, releases and source exports. Its filename is retained for existing links.

Read [MIGRATION.md](MIGRATION.md) for actual local proof and validation evidence,
and [CI.md](CI.md) before changing the trusted policy. Source edits do not
activate a new base-branch workflow or change hosted branch protection. Do not
advertise a verified release before the complete check passes for its exact
commit.

## Before merging a PR

Check out the current PR branch and run Lean locally with the existing pinned
external setup. Keep a separate existing checkout of the current accepted base
for its policy and comparison constants:

```sh
SVB_TRUSTED_ROOT="/absolute/path/to/accepted-checkout" ./lean/verify.sh
```

Require a successful complete run, including kernel replay, the axiom audit and
all 22 canonical targets. Preserve the command, full log and both candidate/base
commit IDs outside the source checkout. Confirm that neither revision has
changed before merging; rerun if either has. See the
[manual verification procedure](CI.md#manual-verification-before-merge) for
details and initial framework adoption.

**A green `CI required` status covers administrative checks only.** GitHub does
not run Lean or confirm that the local proof check was completed. The maintainer
must perform that check and review the result before merging on GitHub.

## GitHub settings

These settings live on GitHub; editing source files does not enable them.

1. Maintain the **About** description, useful research/formal-verification topics
   and a link to the canonical project's README. Keep issues enabled with the correctness,
   constants-improvement and question forms.
2. Protect `main` with pull requests and the **CI required** commit status,
   selecting **GitHub Actions** as its expected source. Require branches to be
   up to date and enforce status checks for administrators too. Disallow force
   pushes and deletion. Its trusted source/contribution preflight and
   administrative tests must succeed. The final job is **Report required
   status**; the branch requirement is the status it posts, **CI required**.
   This status does not include Lean verification.
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
4. Preserve the trusted base-revision `pull_request_target` workflow. Its source
   preflight retains read-only permissions, no repository secrets and disabled
   credential persistence. It does not execute candidate Lean or setup scripts.
   Only isolated static status writers have `statuses: write`; they never
   execute candidate code. See [CI.md](CI.md).
5. There is no maintenance bypass of complete local canonical verification. A change to the
   verification framework itself requires an explicitly reviewed trusted-policy
   transition, without exempting the candidate's mathematical claims.

Inspect [hosted runs](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/workflows/ci.yml)
for the exact commit and base. These runs establish administrative results;
retain the completed local Lean log separately. Recheck both locally and on CI
when the PR or target branch advances. The historical supplement has an
optional manual workflow and is not a required Lean contribution check.

## Release a verified snapshot

Repository releases are separate from publication of the accompanying paper.
The paper remains *in preparation* until a real public version is supplied.

1. Choose the release commit through the normal reviewed PR process. Verify that
   administrative **CI required** passed and the complete local Lean gate
   succeeded for that exact commit on `main`. Do not release a queued, failed
   or partially checked snapshot.
2. Preserve the successful local canonical audit, generated exact targets and
   build logs, together with the command and candidate/base commit IDs. Confirm
   both regimes and all trusted current comparisons passed. A historical PDF is
   not a proof acceptance artifact.
3. Choose the actual version and publication date. Update [CHANGELOG.md](../CHANGELOG.md)
   and [CITATION.cff](../CITATION.cff) through the same verification process, with
   the chosen version, `date-released` and tag URL. The date must describe the
   repository release, not historical local verification or paper publication.
4. In [Releases](https://github.com/marcusdavidwebb/SubGaussianTailBounds/releases),
   create the tag at the exact verified final commit. Attach verification logs
   and targets from its successful local run. Include the full SHA, local
   verification details, administrative CI run URL, proved quartets, changes
   and attribution in the release notes. Review the
   draft before publishing. Agents require explicit approval to publish.
5. Check the tag, assets, citation and download links after publication. Preserve
   previous releases and contribution credit. Never invent a paper DOI, public
   paper URL, verification result or release identifier.

Until a release exists, cite the exact commit using the
[README citation guidance](../README.md#provenance-and-citation).

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
