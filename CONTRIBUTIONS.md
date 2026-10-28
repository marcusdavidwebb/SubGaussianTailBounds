# Contribution history

This is the single readable history of substantial contributions. It preserves
credit when an implementation is replaced, without asserting priority, novelty
or future paper authorship. Historical conditional results are not complete
proofs of the canonical propositions.

## Initial contribution — Marcus Webb

- **Contributor and responsibility:** Marcus Webb is credited with the initial
  repository contribution covering both regimes. He is the sole author of the
  historical supplementary document and takes full responsibility for it.
  Its entire proof and exposition were AI-generated without direct input from
  him. The preceding human mathematical work and tool roles are recorded below
  and in [PROVENANCE.md](docs/PROVENANCE.md).
- **Results:** the initial general quartet `(96/25,79/50,47/20,3/2)` for every
  `K ≥ 1`, and unit quartet `(33/25,28/25,58/25,Real.sqrt 2)` for `K = 1`.
  The legacy identifiers `baseline-general` and `baseline-one` refer to these
  two regimes of this one contribution, not separate contributions.
- **Historical evidence:** [the supplement](supplementary.tex),
  [conditional Lean results](lean/SingularValueBounds/KL/Theorem.lean), the
  original exact Python checker and eleven interface runners in Git history, the
  [formalisation record](lean/FORMALISATION_PLAN.md) and
  [verification report](lean/VERIFICATION_REPORT.md).
- **Verification status:** hybrid verification observed on **20 October 2026**,
  after retirement of the earlier standalone theorem. Lean checked the
  analytic implication; Python checked finite conditions outside Lean. Neither
  complete canonical baseline Lean proof was supplied by that historical run.
  On **23 October 2026**, the migration supplied the complete general theorem
  `SingularValueBounds.Canonical.general_baseline`. On **25 October 2026**,
  `SingularValueBounds.Canonical.unit_baseline` and the complete public interface
  supplied the second baseline, with all eleven finite-condition families proved
  in Lean. Python mathematical checkers and their registry were retired after
  replacement. See [the current verification record](docs/MIGRATION.md); this
  evidence is not backdated to the hybrid run.
- **Attribution:** the accompanying in-preparation paper is by Marcus Webb and
  Morgan Lynch-Davies, whose extensive preceding mathematical work yielded
  weaker bounds. Section S2 identifies Codex as GPT-6; the recorded
  formalisation also involved parallel GPT-6.1 Sol Ultra workers and a
  coordinator. Models generated candidate mathematics, code and exposition;
  Lean checked proof terms and Python performed external exact arithmetic.
  Tool roles and this contextual attribution are not additional accepted
  repository contributions.
- **History:** source inventories, assisted timings, cleanup and validation
  scope remain in the original records. The initial record supplied no public
  PR, commit or release identifier; none is invented here. The current
  [migration map](docs/MIGRATION.md) distinguishes subsequent preparation from
  the historical result. Unresolved attribution and novelty assessments remain
  in [PROVENANCE.md](docs/PROVENANCE.md).
- **Efficiency revision — 26 October 2026:** the ongoing migration in
  [PR #2](https://github.com/marcusdavidwebb/SubGaussianTailBounds/pull/2)
  factors repeated polynomial expansions through existing proved coefficient
  identities, reuses verified integer evaluations for small-range entropy nodes,
  narrows implementation imports, and checks axioms alongside independent module
  kernel replay. This preserves both canonical statements,
  their quartets and all verification obligations. The work was implemented
  with Codex assistance; it makes no new mathematical or novelty claim.
  Measurements and completed validation are recorded separately in
  [MIGRATION.md](docs/MIGRATION.md).

- **Proof simplification — 26 October 2026:** a further revision in the same
  [PR #2](https://github.com/marcusdavidwebb/SubGaussianTailBounds/pull/2)
  replaces the 1,150 small endpoint-prefactor evaluations with a uniform bound,
  derives routine moment and second-moment certificate fields from existing
  enclosures, and removes unnecessary endpoint polynomial degree padding.
  Exact integer recurrences and denominator-cleared polynomial identities reduce repeated
  rational arithmetic. Bounded private theorem blocks keep the remaining finite
  decisions small. A subsequent pass applies these methods to the separate
  second-moment upper margins and geometry certificates, replacing routine grid
  enumeration with uniform inequalities where possible. The canonical theorem,
  all numerical margins and truncation orders remain unchanged. This reuses
  the existing Taylor, rounding and
  Bernstein arguments, with Codex assistance; it asserts no new mathematical
  result or novelty. The separate measurements and verification status
  are recorded in [MIGRATION.md](docs/MIGRATION.md).

- **Further proof simplification — 27 October 2026:** the same
  [PR #2](https://github.com/marcusdavidwebb/SubGaussianTailBounds/pull/2)
  shares repeated general entropy decay evaluations and adjacent endpoint
  corner proofs, replaces expanded plateau polynomial identities with exact
  degree-and-evaluation arguments, and uses shared integer logarithm evaluators.
  Uniform inequalities replace another routine corner enumeration, and
  sequential elaboration reduces memory retained within large proof modules.
  The original coefficients, rounding steps, margins, canonical statements and
  verification policy are preserved. This is an implementation revision with
  Codex assistance, using existing mathematical methods; it makes no novelty
  claim. Measurements and verification status are recorded separately in
  [MIGRATION.md](docs/MIGRATION.md).

- **Hosted CI scheduling — 28 October 2026:** the same PR splits cold
  compilation and independent kernel replay into dependency stages across
  standard runners after the hosted build reached GitHub's six-hour job limit.
  Trusted same-attempt checkpoints retain ancestor-first replay and exact
  artifact identity; every module, canonical type, universe and axiom check is
  still required. The Lean proofs, canonical source, quartets and dependency
  pins are unchanged. This infrastructure revision was implemented with Codex
  assistance and makes no mathematical or novelty claim. See
  [the failure and validation record](docs/MIGRATION.md).

No later substantial contribution has been accepted. Add future accepted
entries identifying the contributor, affected regime, jointly proved quartet
or implementation change, explanation and attribution, supersession, and
actual commit/PR links when available. Preserve earlier substantive credit;
follow [CONTRIBUTING.md](CONTRIBUTING.md).
