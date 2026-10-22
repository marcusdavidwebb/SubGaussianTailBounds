# CI policy and trust boundaries

Default-branch protection must require **CI required**, with GitHub Actions as
the expected source, up-to-date branches and pull requests, including for the
maintainer. All contributor PRs require Marcus Webb's approving codeowner
review. As sole maintainer he may approve his own work by merging through an
account-specific review bypass, because GitHub rejects literal self-approval.
Use that bypass only for his own PRs; GitHub does not restrict it by authorship.
The review-only **Maintainer approval** ruleset is separate from mandatory CI
branch protection. Its exception does not waive any CI or mathematical evidence
requirement.
See the [maintainer guide](LAUNCH_CHECKLIST.md#github-settings). Files alone
cannot enable those repository settings.

## Trusted workflow and candidate execution

The workflow runs on `pull_request_target` so that the trusted base supplies the
workflow and contribution validator. A contributor cannot replace that workflow
with a passing stub in their own PR.

The candidate is the exact PR head merged with the event's base revision.
Candidate-code jobs run on disposable hosted runners with read-only permissions,
no repository secrets, no persisted checkout credentials and no reusable Actions
caches. They run the registered contribution gate, exact certificate checks,
Lean build/audit/generated target checks, and standalone supplement build.

The isolated **Start required status** and **Report required status** jobs have
only the status-write permission needed to post pending/success/failure
**CI required** on the exact PR head. They use static Python and never check out
or execute candidate code. The final status succeeds only when all required
component jobs succeed; failure, cancellation and skipped checks do not count
as success.

This separation is essential: do not give candidate-code jobs write permissions
or secrets, persist checkout credentials, or share their caches with trusted
execution. Workflow/gate changes need codeowner review before becoming trusted
base policy. Inspect the
[hosted workflow runs](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/workflows/ci.yml)
for the exact commit under review. A queued, cancelled or failed run is not
successful validation; historical local runs do not establish hosted success.

## Find results and artifacts

Open **Actions → Verification**, select a run and check its commit and branch.
All four component jobs must succeed, followed by **Report required status**.
The required commit status is **CI required**, not the final job's display name.
The README badge shows workflow status on `main`, not proof of a release or
verification of another commit.

On the run page, **Artifacts** contains `exact-certificates-<run_id>`,
`lean-verification-<run_id>` and `supplement-<run_id>` when their upload steps
have produced files. These contain the certificate log, Lean log/generated
targets, and PDF/LaTeX log respectively. Artifacts can also be uploaded after
failure; inspect the job conclusions before relying on them. Downloading
artifacts requires signing in to GitHub, and artifacts expire.

Repository settings are maintained separately from these source files; see
the [maintainer guide](LAUNCH_CHECKLIST.md#github-settings).

## Complete evidence and maintenance

An improvement needs an editable proof, registered exact constants, a compiled
Lean target at those constants, applicable exact certificate mapping/data and
contribution history. Baseline regression success alone cannot verify the new
quartet. See [CONTRIBUTING.md](../CONTRIBUTING.md) and
[the technical contract](../contributions/README.md).

A maintainer may authorize genuine maintenance using
`/ci-maintenance <40-character current HEAD SHA>`, followed by a manual rerun.
Authorization is read from the trusted base-policy maintainer list
and expires when the head changes. It permits maintenance without a new
improvement record, while retaining regression checks. It cannot validate an
incomplete constants claim.

Human review remains necessary for mathematical intent, attribution and the
documented hybrid checker-to-Lean correspondence. CI does not establish novelty
or remove the external-Python trust boundary.
