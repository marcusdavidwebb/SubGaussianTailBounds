# Contributing

This project maintains one Lean formalization of the two propositions in
[MainTheoremStatement.lean](MainTheoremStatement.lean). Marcus Webb decides
whether to accept each contribution; a verified result is eligible for review,
not automatically accepted.

## Mathematical contract

A contribution may replace either regime's proof, including at unchanged
constants. Prove the complete canonical proposition at one exact quartet
`(α, β, γ, δ)`, for arbitrary sample-space universe `u`:

```lean
SubGaussian.GeneralSingularValueTailBound.{u} α β γ δ
SubGaussian.UnitSingularValueTailBound.{u} α β γ δ
```

Preserve every hypothesis, positivity, both non-strict tail events and endpoints,
event measurability and `ℝ≥0∞` probability bounds. All numerical obligations must
be proved in Lean; no conditional certificate or analytic premise may remain.

Prove all four componentwise comparisons against both the original baseline
and the current accepted quartet of the same regime:

| Regime | Permanent baseline ceiling |
|---|---|
| General | `(3.84, 1.58, 2.35, 1.5)` = `(96/25, 79/50, 47/20, 3/2)` |
| Unit | `(1.32, 1.12, 2.32, Real.sqrt 2)` = `(33/25, 28/25, 58/25, Real.sqrt 2)` |

**No current component may increase.** Equality in every component is allowed.
Preserve the other regime and every accepted improvement. The quartet must be
proved jointly; selecting coordinates from unrelated results is insufficient.
Decimal literals are exact rationals, and `Real.sqrt 2` is exact.

No improvement over these baselines has yet been accepted. The current ceiling
comes from [AcceptedConstants.lean](lean/SingularValueBounds/Canonical/AcceptedConstants.lean)
in the trusted accepted base. A candidate's snapshot or an older predecessor
cannot authorize a regression. For example, after accepting `(3.70, 1.58, 2.35,
1.5)`, the proposed `(3.75, 1.55, 2.35, 1.5)` would fail the first comparison.
These example constants assert no mathematical improvement.

## Make and verify a change

The root `MainTheoremStatement.lean` is immutable: preserve its exact bytes,
name and location, including imports, comments and universe parameters. Do not
edit, delete, rename, relocate, replace or shadow it. Put proofs and adapters in
other modules importing the actual root source; report problems without changing
or weakening the statement.

Edit proofs under [lean/SingularValueBounds/](lean/SingularValueBounds/).
[Canonical/Results.lean](lean/SingularValueBounds/Canonical/Results.lean) exposes
the public results, baseline corollaries and comparisons. An improved quartet
also updates `AcceptedConstants.lean` and proves its equality with the constants
used by the results. The [22-declaration interface](docs/VERIFICATION.md#lean-interface)
is the acceptance contract. Supporting modules may be reorganized or replaced;
keep the umbrella imports current and preserve credit for superseded work.

Submit Lean sources, a concise explanation and attribution, and an entry in
[CONTRIBUTIONS.md](CONTRIBUTIONS.md). Include computational or AI assistance and
actual commit/PR links when available. Separate prose proofs, PDF proofs and
Python certificate packages are not contribution artifacts.

Run `./lean/verify.sh` with the [pinned external setup](lean/README.md).
The maintainer repeats the complete check on the PR branch against the current
accepted base before merging; see [manual verification](docs/VERIFICATION.md#manual-verification-before-merge).
A green administrative CI status is not a Lean proof check. No maintenance
route exempts a mathematical claim from complete verification.

Keep toolchains, dependencies, caches and build outputs outside the source
checkout, and preserve dependency pins. Changes to verification policy require
explicit maintainer review. Agents need prior approval for a specific PR and
must not merge or enable automatic merging on the maintainer's behalf.

## Research and credit

Before substantive proof development, state the exact target and hypotheses and
investigate primary sources, including stronger results, alternative formulations
and the sources of the methods. For material comparisons record the source and
version, theorem/page, inspected material, hypotheses and precise implication
or obstruction. Report access limitations; an abstract or snippet is not a
full-text check, and inaccessible sources must not be described as read.

Keep correctness, attribution and novelty separate. Attribute borrowed methods
where used; independent derivation, successful Lean verification and unsuccessful
literature searches do not establish novelty. Distinguish established results,
adaptations, alternative proofs and candidate new results. Preserve unresolved
assessments and record checks, limitations and outstanding questions in the
contribution's explanation and Lean documentation. The maintainer reviews
substantive statement and attribution changes; mathematical credit and paper
authorship are separate decisions. [PROVENANCE.md](docs/PROVENANCE.md) records
the existing assessment's scope.

Contributions use the [MIT License](LICENSE) unless explicitly agreed otherwise.
Preserve substantive credit, including Marcus Webb's initial contribution
covering both regimes, and the third-party terms in [LICENSING.md](LICENSING.md).
