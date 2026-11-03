# Working in this repository

Read [README.md](README.md), [CONTRIBUTING.md](CONTRIBUTING.md) and
[lean/README.md](lean/README.md) before changing proofs or verification.
The repository-local instruction inventory is this root `AGENTS.md`.

`MainTheoremStatement.lean` is the authoritative root statement. Import the actual
file; do not shadow it. Preserve the two required propositions, arbitrary
sample-space universes, all hypotheses, normalization, singular-value conventions,
non-strict events and endpoints. Make any proposed statement or imported-definition
change conspicuous for Marcus's review and prove equivalence when needed.

The required quartets are general `(3.84, 1.58, 2.35, 1.50)` and unit
`(1.32, 1.12, 2.32, 1.42)`. Their authoritative exact rational definitions are in
`lean/SingularValueBounds/Canonical/Constants.lean`. Generate documentation from
those values. Internal estimates and proof methods may change; old algorithms,
intermediate values, symbolic bounds and APIs are not permanent requirements.

All numerical premises must be proved in Lean. Do not use `sorry`, additional
axioms, native-computation assumptions or trusted floating-point evidence.
The only permitted foundational axioms are `propext`, `Classical.choice` and
`Quot.sound`. Preserve exact-type and universe audits, independent kernel replay
in the full check, maintained-source coverage and accurate checked-input reports.
Review changes to the verifier explicitly.

Run `./lean/check-statements.sh` during development and `./lean/verify.sh` on the
final relevant source state. CI is lightweight administration, not proof
verification. Record cache conditions and concurrency when reporting performance.
Keep toolchains, dependencies, caches, logs and compiled outputs outside this
checkout and OneDrive, in this project's external workspace under `~/Lean/`.
Reuse compatible central Elan and pinned packages first; deliberate migrations
need a stated reason and semantic review. Preserve other projects' environments.

Inspect the working tree before editing and preserve unrelated changes. Keep
documentation concise, credit substantive contributions in `CONTRIBUTIONS.md`,
and preserve licensing and the recorded human/model roles and unresolved
attribution assessments. Do not turn implementation choices into permanent policy.

Prepare changes locally. Obtain explicit approval before opening a specific PR;
never merge or enable automatic merging on Marcus's behalf.
