## Change and scope

Describe the change, affected regime, concise explanation and attribution.
An alternative formalization at unchanged constants is eligible for review.
No component may increase above either the baseline or the currently accepted
quartet. Marcus Webb decides whether to accept every eligible PR.

## Lean evidence

- [ ] The root `MainTheoremStatement.lean` is byte-for-byte unchanged.
- [ ] Named universe-polymorphic Lean theorem directly proves the canonical proposition.
- [ ] All four baseline and trusted-current comparisons are proved in Lean.
- [ ] The other regime and both baseline corollaries remain verified.
- [ ] `CONTRIBUTIONS.md` records the explanation and attribution.
- [ ] `./lean/verify.sh` passes, including the complete theorem and axiom audits.

The maintainer reruns the complete Lean check locally before merging. CI checks
repository integrity only; its green status is not Lean verification evidence.

Give declaration names and actual verification results. Do not submit a
separate prose proof, PDF proof, or Python certificate package. State incomplete
checks explicitly rather than checking boxes for unfinished mathematics.

## Trusted policy and review

Every PR requires the same complete local Lean check, including comparison with
the accepted base; maintenance comments cannot exempt a claim. Record the checked
head/base revisions and result. Identify any build-policy migration requiring
separate review. See the
[Lean interface](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/main/docs/CI.md#lean-interface).
