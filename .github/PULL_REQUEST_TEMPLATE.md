## Type of contribution

- [ ] Constants improvement, with the complete evidence package below.
- [ ] Maintenance, such as documentation, metadata or tooling, with no claimed improvement.

## Change and scope

Explain the problem, the resulting change and the checks you ran. Link any related issue.

## Constants improvements

Complete this section for a claimed improvement; remove it for maintenance.

Give the contribution ID and exact claimed constants, with the parameter range.
Explain any trade-off and identify the previous result being improved.

- [ ] Immutable contribution JSON record and editable mathematical proof source.
- [ ] Lean theorem for the claimed values under the original hypotheses.
- [ ] Exact numerical certificates and checker mapping, including explicit reuse.
- [ ] Contribution history and verification note, with attribution and AI-use disclosure.

A PDF or natural-language proof alone cannot pass the improvement gate. See
[the contribution guide](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/main/CONTRIBUTING.md)
and [technical contract](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/main/contributions/README.md).

## Maintenance

Complete this section for maintenance; remove it for a constants improvement.

Explain why this change does not claim improved constants. An authorized
maintainer must comment `/ci-maintenance <40-character current HEAD SHA>` and
rerun CI. A new commit requires new authorization. Checking a box or adding a
label does not authorize this route. All regression checks still run; see
[the review process](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/main/CONTRIBUTING.md#checks-and-review).

## Review

- [ ] Full CI passes, including the generated theorem-type and axiom checks.

Identify the parts needing particular review, including any affected proof steps
or numerical interfaces.
Do not change the baseline proof, dependency pins, audit, or CI to obtain a pass.
Intentional maintenance requires a separate maintainer-authorized PR; a label
or a statement in this PR does not authorize that exemption.
