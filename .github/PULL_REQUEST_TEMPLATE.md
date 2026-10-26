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

Give declaration names and actual verification results. Do not submit a
separate prose proof, PDF proof, or Python certificate package. State incomplete
checks explicitly rather than checking boxes for unfinished mathematics.

## Trusted policy and review

Every PR uses the same complete Lean gate; maintenance comments cannot exempt a
claim. Candidate workflow edits do not alter the trusted base's policy. Identify
any build-policy migration requiring separate review. See the
[Lean interface](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/main/docs/CI.md#lean-interface).
