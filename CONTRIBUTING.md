# Contributing

Prove both complete propositions in [MainTheoremStatement.lean](MainTheoremStatement.lean)
for arbitrary sample-space universe `u`, at the jointly specified quartets in
[Constants.lean](lean/SingularValueBounds/Canonical/Constants.lean). Preserve all
hypotheses, coefficient positivity, normalization, dimensions, singular-value
conventions, non-strict events, endpoints and probability bounds. Numerical
obligations must be Lean proofs, with only `propext`, `Classical.choice` and
`Quot.sound` as foundational axioms.

Proof methods, auxiliary constants, numerical witnesses, internal APIs and module
boundaries may change. Prefer simpler arguments and sufficient precision.
Published upper-bound coefficients use exact rationals with two decimal places;
round upward and prove the implication. Cheap stronger intermediate estimates
are useful, but stronger symbolic main guarantees are not a separate maintenance
goal. Proposed coefficient or statement changes require conspicuous human review;
Git records previous results. There is no accepted-constants snapshot or automated
componentwise comparison protocol.

`lake build SingularValueBounds.CheckStatements` compiles the two displayed
claims using the root Lake project. Run `./lean/check-statements.sh` while
developing and `./lean/verify.sh` on the
final relevant sources before merging. The latter includes independent kernel
replay, exact types and universes, axiom audits and maintained-source coverage.
Report incomplete checks honestly. Administrative CI does not establish proof
verification. See [Lean setup](lean/README.md) and [verification](docs/VERIFICATION.md).
The verification scripts use an external workspace; the standard root Lake build
uses `.lake` in the checkout. Explain any deliberate dependency migration,
inspect changed imported definitions and supply the needed equivalence proofs.

Submit complete Lean sources, a concise explanation, validation/performance
evidence and an attribution entry in [CONTRIBUTIONS.md](CONTRIBUTIONS.md).
Generators may propose witnesses; Lean must prove the facts they need. No separate
prose proof, certificate service or acceptance ledger is required. Marcus Webb
reviews mathematical changes and decides acceptance. Agents need explicit approval
for each PR and must not merge or enable automatic merging.

Before substantive mathematical development, inspect relevant primary sources
and verify their hypotheses and constants. Record material comparisons precisely,
including version, theorem/page, what was actually inspected and any obstruction.
Report inaccessible sources honestly. Distinguish correctness, attribution and
novelty: successful formalization or an unsuccessful search establishes no priority.
Preserve the human and model roles, responsibility, historical validation and
unresolved assessments recorded in the contribution history. Model review is not
independent human review; paper authorship is a separate decision.

Contributions use the [MIT License](LICENSE) unless explicitly agreed otherwise.
Preserve Marcus Webb's initial contribution covering both regimes, preceding work
with Morgan Lynch-Davies, and third-party notices in [LICENSING.md](LICENSING.md).
