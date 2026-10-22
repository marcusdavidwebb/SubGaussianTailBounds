# CI policy and trust boundaries

The default-branch ruleset must require **CI required**, with GitHub Actions as
the expected source, up-to-date branches, and maintainer/codeowner review.
Files alone cannot enable those repository settings.

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
base policy. Initial GitHub-hosted execution still needs to be observed after
the repository is created.

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
