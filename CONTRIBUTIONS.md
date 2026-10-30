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
- **Historical evidence:** [the historical supplement](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/supplementary.tex),
  [conditional Lean results](lean/SingularValueBounds/KL/Theorem.lean), the
  original exact Python checker and eleven interface runners in Git history, the
  [formalisation record](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/lean/FORMALISATION_PLAN.md) and
  [verification report](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/lean/VERIFICATION_REPORT.md).
- **Verification status:** hybrid verification observed on **20 October 2026**,
  after retirement of the earlier standalone theorem. Lean checked the
  analytic implication; Python checked finite conditions outside Lean. Neither
  complete canonical baseline Lean proof was supplied by that historical run.
  On **23 October 2026**, the migration supplied the complete general theorem
  `SingularValueBounds.Canonical.general_baseline`. On **25 October 2026**,
  `SingularValueBounds.Canonical.unit_baseline` and the complete public interface
  supplied the second baseline, with all eleven finite-condition families proved
  in Lean. Python mathematical checkers and their registry were retired after
  replacement. See [the current verification record](docs/HISTORY.md); this
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
  [migration map](docs/HISTORY.md) distinguishes subsequent preparation from
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
  [HISTORY.md](docs/HISTORY.md).

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
  are recorded in [HISTORY.md](docs/HISTORY.md).

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
  [HISTORY.md](docs/HISTORY.md).

- **Hosted CI scheduling — 28 October 2026:** the same PR splits cold
  compilation and independent kernel replay into dependency stages across
  standard runners after the hosted build reached GitHub's six-hour job limit.
  Trusted same-attempt checkpoints retain ancestor-first replay and exact
  artifact identity; every module, canonical type, universe and axiom check is
  still required. The Lean proofs, canonical source, quartets and dependency
  pins are unchanged. This infrastructure revision was implemented with Codex
  assistance and makes no mathematical or novelty claim. See
  [the failure and validation record](docs/HISTORY.md).

- **Manual Lean verification — 29 October 2026:** at Marcus Webb's request,
  the same PR removes automated Lean compilation and auditing from CI. He will
  run the unchanged complete `./lean/verify.sh` locally before merging each PR.
  CI retains administrative repository checks and makes no proof-success claim.
  This workflow and documentation revision has Codex assistance; it changes no
  theorem, constant or proof. See [the policy and validation record](docs/HISTORY.md).

- **Lean-only cleanup — 29 October 2026:** at Marcus Webb's request, the same
  PR removes the historical supplement and paper tooling, retired hosted Lean
  infrastructure and duplicate diagnostic commands. Current guides are
  consolidated around the formalization and `./lean/verify.sh`. The canonical
  source, proofs, constants and complete mathematical checks are preserved.
  Codex assisted this repository simplification; it makes no mathematical or
  novelty claim. Original documents and detailed measurements remain in Git
  history, linked from [HISTORY.md](docs/HISTORY.md).

## Statement presentation revision — 30 October 2026

At Marcus Webb's explicit request, Codex simplified the canonical statement's
presentation while preserving the natural-language theorem in the README.
Actual Lean imports from
[NLA-lib at commit 6491e752](https://github.com/NLA-lib/NLAlib/tree/6491e7528c1b1e68e46301cde6a76ae153e8e834)
supply `IsSubgaussianVector`, `IsIsotropic` and `singularValues`; a shared tail
conclusion removes repetition. The root statement is now 80 lines. The MGF
parameter remains `K`, passed to NLA-lib as variance proxy `K²`. Explicit row
measurability, both sharp quartets, both individual non-strict measurable tail
guarantees and arbitrary sample-space universes are preserved. The revision
uses NLA-lib's definitions and supporting lemmas; its
[sub-Gaussian row tail theorem](https://github.com/NLA-lib/NLAlib/blob/6491e7528c1b1e68e46301cde6a76ae153e8e834/NLAlib/RandomMatrix/SubGaussian/ExtremeSingularValues.lean)
does not replace this repository's sharp proof.

[StatementEquivalence.lean](lean/SingularValueBounds/Canonical/StatementEquivalence.lean)
connects the statement to the preceding expanded propositions, using
[NLARows.lean](lean/SingularValueBounds/Canonical/NLARows.lean) for the exact MGF
normalization and coordinate moments, and
[NLASingularValues.lean](lean/SingularValueBounds/Canonical/NLASingularValues.lean)
for the old minimum/maximum definitions, including zero singular values.
The existing adapters and monotonicity proofs are updated accordingly. The
authorized root replacement also repins the source-integrity digest and
refreshes the README copy; it does not relax any mathematical verification check.

The requested imports use Lean/Mathlib 4.33.1 and a separate central workspace
under `~/Lean/SubGaussianTailBounds/0ad011255e709e4d/nla-4.33.1/`. NLA-lib and
Mathlib reside in its `.lake/packages/`; the older 4.19.0 dependencies remain
untouched. No NLA-lib source is copied into the repository, and the external
dependency retains its Apache 2.0 licence; see [LICENSING.md](LICENSING.md).

The complete proof library, both sharp canonical results and the full statement
equivalences compile with Lean 4.33.1. The generated canonical acceptance
obligations also compile and pass their supplemental axiom audit. Marcus Webb
explicitly deferred independent kernel replay, so no complete verification of
this dependency migration is claimed. Validation is recorded in
[HISTORY.md](docs/HISTORY.md). This presentation and compatibility revision makes
no new bound or novelty claim and has not been accepted. It is included in
[draft PR #4](https://github.com/marcusdavidwebb/SubGaussianTailBounds/pull/4).

## Real-valued tail probabilities — 30 October 2026

At Marcus Webb's explicit request and authorization, Codex revised the canonical
`SingularValueTails` to require a probability measure and express both probability
bounds in `ℝ`. [TailEquivalence.lean](lean/SingularValueBounds/Canonical/TailEquivalence.lean)
relates these bounds to the previous `ENNReal.ofReal` form under the
probability-measure assumption. No extra finite-measure assumption, new constants
or new bounds are introduced; the measurable non-strict events and arbitrary
sample-space universes are retained.
This is an implementation and statement-presentation change, with no novelty
claim. The earlier migration's compilation and audit record applies to its
original source and does not by itself verify this revision; see
[HISTORY.md](docs/HISTORY.md). Future unauthorized changes to the canonical
root remain prohibited.

## Canonical helper simplification — 30 October 2026

Marcus Webb removed an unused scope opening and an explanatory comment; at his
request, Codex removed an unused helper proof argument and a direct import
already supplied transitively. Both theorem statements retain their dimension
hypothesis and all other hypotheses and bounds. A temporary Lean variant proved
the previous and simplified helper and complete propositions equivalent by
`Iff.rfl` at arbitrary sample-space universes. The helper's Lean interface changes;
this is a presentation change, with no new bound or novelty claim. The
canonical file remains protected against future unauthorized changes.

No later substantial contribution has been accepted. Add future accepted
entries identifying the contributor, affected regime, jointly proved quartet
or implementation change, explanation and attribution, supersession, and
actual commit/PR links when available. Preserve earlier substantive credit;
follow [CONTRIBUTING.md](CONTRIBUTING.md).
