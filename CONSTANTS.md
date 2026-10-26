# Constants and replacement policy

The [README theorem statement](README.md#theorem-statement) gives the exact
hypotheses, normalization and tail inequalities. The authoritative formal
definitions are in the immutable root
[MainTheoremStatement.lean](MainTheoremStatement.lean).

| Regime | Exact initial quartet $(\alpha,\beta,\gamma,\delta)$ | Decimal presentation |
|---|---|---|
| Every $K\ge1$ | $(96/25,79/50,47/20,3/2)$ | $(3.84,1.58,2.35,1.5)$ |
| $K=1$ | $(33/25,28/25,58/25,\sqrt2)$ | $(1.32,1.12,2.32,\sqrt2)$ |

No improved quartet has been accepted. These initial comparison ceilings are
also permanent baseline proof targets. The general quartet applies at $K=1$;
the separate unit target has sharper constants. Decimal literals represent
exact Lean real numbers, not floating-point approximations.

Both baseline quartets are proved in Lean by
[`Canonical.general_baseline`](lean/SingularValueBounds/Canonical/General.lean)
and [`Canonical.unit_baseline`](lean/SingularValueBounds/Canonical/Unit.lean).
The public current results, baseline corollaries and comparison proofs are in
[Canonical/Results.lean](lean/SingularValueBounds/Canonical/Results.lean).
[AcceptedConstants.lean](lean/SingularValueBounds/Canonical/AcceptedConstants.lean)
records the jointly proved quartets; Lean checks their equality with the result's
constants. A trusted base supplies the independent comparison ceiling.

The historical records `baseline-general` and `baseline-one` refer to the two
regimes of one initial contribution. Their hybrid verification on 20 October
2026 was conditional Lean plus external Python arithmetic. The complete Lean
proofs and subsequent checks are separate evidence in [MIGRATION.md](docs/MIGRATION.md),
not a change to [the historical report](lean/VERIFICATION_REPORT.md).

## Updating a quartet

A replacement must prove one whole quartet and all four inequalities against
both its original baseline and its regime's current accepted quartet. No
component may increase. Equality in all four entries is allowed, subject to
the maintainer's decision on the proposed replacement. General and unit
quartets are tracked separately; a contribution may address one regime.

After an accepted change from `(3.84, 1.58, 2.35, 1.5)` to
`(3.70, 1.58, 2.35, 1.5)`, a proposal at `(3.75, 1.55, 2.35, 1.5)` must be
rejected: it loses the accepted first-component improvement. This example
asserts no mathematical improvement. Never combine the best coordinates of
separate results without proving their joint claim.

The trusted accepted theorem determines the comparison ceiling; changing this
table or a candidate's metadata does not change it. Update the current quartet
only when the corresponding verified replacement is accepted, and retain the
original baseline results as Lean corollaries. Recompare when the target
branch advances during review. The
[contribution contract](CONTRIBUTING.md) gives the required Lean evidence;
[CONTRIBUTIONS.md](CONTRIBUTIONS.md) records credit and supersession.
