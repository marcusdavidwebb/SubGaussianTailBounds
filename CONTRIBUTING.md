# Contributing

This project welcomes better constants, corrections, literature pointers, and
work on written proofs, exact certificates and Lean formalisation. Marcus Webb
is the initial maintainer. The accompanying paper is in preparation.

## Discuss an idea

Use an issue for questions, numerical exploration or an argument not yet fully
formalised. Distinguish proved statements, conjectures and numerical evidence.
An issue is a discussion record, not an accepted theorem or an automatic claim
to priority.

## A complete constants-improvement pull request

An improvement PR must contain **all** of the following:

1. A machine-readable record in `contributions/records/`, specifying the exact
   quartet, regime, contributor credit, predecessor and evidence paths. Follow
   the [technical contract and template](contributions/README.md).
2. An editable readable proof in `contributions/proofs/`, with precise statements,
   hypotheses, changed estimates and local citations. A PDF may accompany it;
   a PDF or natural-language proof alone is insufficient.
3. A Lean theorem for the claimed quartet under the original row assumptions,
   in `lean/SingularValueBounds/KL/Contributions/`, with the required appended
   umbrella import. The generated gate obligation checks that theorem against
   the exact claimed quartet and the required quantified statement.
4. The applicable exact finite certificates and their checker-to-Lean mapping.
   List reused baseline conditions/checkers explicitly. Any extra finite data
   must use the gate's supported exact format. Numerical samples or floating-point
   optimization do not replace certificates. No new analytic assumption may be
   hidden among the theorem's premises.
5. A note in `contributions/verification/`, and updates to
   [CONTRIBUTIONS.md](CONTRIBUTIONS.md), [CONSTANTS.md](CONSTANTS.md) and relevant
   verification documentation. Record attribution, remaining uncertainties and
   the role of AI or other computational tools.

Preserve the immutable baseline Lean sources, original checker and interface
runners. Improvement PRs add evidence rather than replace those files or weaken
the audit. A different proof architecture, certificate format or intentional
framework revision needs separate maintainer-authorized maintenance work,
still subject to full regression checks.

Use [CONSTANTS.md](CONSTANTS.md) for the exact normalization. Identify the
general-$K$ and $K=1$ scopes, unchanged entries and any tradeoff.

## Checks and review

From the repository root, with [the pinned setup](lean/README.md):

```sh
python3 scripts/check_contributions.py --root .
./lean/check_hybrid.sh
./scripts/build_supplement.sh
```

For an improvement branch, include the base revision and generate/compile the
contribution target as described in [contributions/README.md](contributions/README.md).
The PR workflow performs those comparisons and generated target checks.
Unchanged baseline checks passing do not verify new constants.

The required jobs are **Contribution completeness**, **Exact certificates**,
**Lean verification** and **Supplement build**, aggregated by **CI required**.
The contribution job requires the complete registered package; all PRs run the
full hybrid regression checks. A missing Lean result or certificate package
fails even when a readable mathematical proof is provided.

The trusted base revision supplies the `pull_request_target` workflow and
contribution validator. Candidate code runs on disposable hosted runners with
read-only permissions, no repository secrets, no persisted checkout credentials
and no reusable Actions caches. It is tested at the exact PR head merged with
the event's base revision. Isolated status-writer jobs execute static code
without checking out the candidate and report **CI required** on that exact
head. See [CI policy and trust boundaries](docs/CI.md).

The only maintenance exception requires an authorized maintainer's exact
PR-head-bound comment:

```text
/ci-maintenance <40-character current HEAD SHA>
```

The trusted workflow checks the commenter against its trusted base-revision
maintainer list, initially `marcusdavidwebb`. CI must then be rerun. A new commit
invalidates the previous authorization. A contributor cannot exempt their own
work by declaring a category, changing a label or editing the PR's workflow.
Maintenance authorization permits a PR without a new improvement record; it
does not skip regression checks or accept an incomplete constants claim.

Passing CI is necessary for acceptance. Maintainer review also checks the
mathematics, theorem/checker correspondence, attribution and scope. Python
checks remain external to Lean; CI does not establish novelty. Read the
[research protocol](docs/RESEARCH_PROTOCOL.md).

## Credit and history

Credit every substantial contributor as they wish, with an optional ORCID or
profile link and their agreement before adding personal details. Record the
contribution ID, result, proof/checker evidence, review status and actual
issue/PR/commit/release links when available. Keep earlier entries and add
explicit superseding or corrective entries. Preserve commit authorship and
coauthor credit when integrating work.

The ledger is append-only: retain its existing bytes and append a new entry or
correction. The gate enforces this even for authorized maintenance PRs. Current
overviews can change in `CONSTANTS.md` while the older credited result remains
in the records and ledger.

Substantial proof ideas, certificate construction, formalisation and material
corrections merit a ledger entry; small editorial changes can remain in Git
history and the changelog. This record does not automatically grant paper
authorship. Future authorship and acknowledgements are decided separately with
the people involved.

## Dependencies and licensing

Preserve the pinned toolchain/dependency revisions. Keep dependencies, compiled
outputs and caches outside this source checkout; do not commit build logs or
SyncTeX. Include editable proofs, scripts and the readable supplementary PDF.

The project's original code, proofs and documentation use the
[MIT License](LICENSE); see [LICENSING.md](LICENSING.md). Contributions submitted
for inclusion are provided under the MIT License unless explicitly stated
otherwise and agreed by the maintainer. Identify the source and applicable
terms of any third-party material before adding it, and preserve its notices.
