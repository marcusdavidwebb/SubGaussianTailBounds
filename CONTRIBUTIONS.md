# Contribution history

This is the readable history of substantial contributions. Earlier entries describe
their contemporaneous policies and verification status; current instructions
are in CONTRIBUTING.md and the current verification/performance guides. It preserves
credit when an implementation is replaced, without asserting priority, novelty
or future paper authorship. Historical conditional results are not complete
proofs of the canonical propositions.

## Initial contribution — Marcus Webb

- **Contributor and responsibility:** Marcus Webb is credited with the initial
  repository contribution covering both regimes. He is the sole author of the
  historical supplementary document and takes full responsibility for it.
  Its entire proof and exposition were AI-generated without direct input from
  him. The preceding human mathematical work and tool roles are recorded below
  and in the [archived provenance](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/PROVENANCE.md).
- **Results:** the initial general quartet `(96/25,79/50,47/20,3/2)` for every
  `K ≥ 1`, together with tail bounds for the unit regime `K = 1`.
  The legacy identifiers `baseline-general` and `baseline-one` refer to these
  two regimes of this one contribution, not separate contributions.
- **Historical evidence:** [the historical supplement](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/supplementary.tex),
  [conditional Lean results](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/lean/SingularValueBounds/KL/Theorem.lean), the
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
  replacement. See [the current verification record](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md); this
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
  [migration map](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md) distinguishes subsequent preparation from
  the historical result. Unresolved attribution and novelty assessments remain
  in [PROVENANCE.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/PROVENANCE.md).
- **Efficiency revision — 26 October 2026:** the ongoing migration in
  [PR #2](https://github.com/marcusdavidwebb/SubGaussianTailBounds/pull/2)
  factors repeated polynomial expansions through existing proved coefficient
  identities, reuses verified integer evaluations for small-range entropy nodes,
  narrows implementation imports, and checks axioms alongside independent module
  kernel replay. This preserves both canonical statements,
  their quartets and all verification obligations. The work was implemented
  with Codex assistance; it makes no new mathematical or novelty claim.
  Measurements and completed validation are recorded separately in
  [HISTORY.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md).

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
  are recorded in [HISTORY.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md).

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
  [HISTORY.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md).

- **Hosted CI scheduling — 28 October 2026:** the same PR splits cold
  compilation and independent kernel replay into dependency stages across
  standard runners after the hosted build reached GitHub's six-hour job limit.
  Trusted same-attempt checkpoints retain ancestor-first replay and exact
  artifact identity; every module, canonical type, universe and axiom check is
  still required. The Lean proofs, canonical source, quartets and dependency
  pins are unchanged. This infrastructure revision was implemented with Codex
  assistance and makes no mathematical or novelty claim. See
  [the failure and validation record](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md).

- **Manual Lean verification — 29 October 2026:** at Marcus Webb's request,
  the same PR removes automated Lean compilation and auditing from CI. He will
  run the unchanged complete `./lean/verify.sh` locally before merging each PR.
  CI retains administrative repository checks and makes no proof-success claim.
  This workflow and documentation revision has Codex assistance; it changes no
  theorem, constant or proof. See [the policy and validation record](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md).

- **Lean-only cleanup — 29 October 2026:** at Marcus Webb's request, the same
  PR removes the historical supplement and paper tooling, retired hosted Lean
  infrastructure and duplicate diagnostic commands. Current guides are
  consolidated around the formalization and `./lean/verify.sh`. The canonical
  source, proofs, constants and complete mathematical checks are preserved.
  Codex assisted this repository simplification; it makes no mathematical or
  novelty claim. Original documents and detailed measurements remain in Git
  history, linked from [HISTORY.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md).

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
[HISTORY.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md). This presentation and compatibility revision makes
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
[HISTORY.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md). Future unauthorized changes to the canonical
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

## Proof-checking simplification — 30 October 2026

At Marcus Webb's request, Codex and parallel agents simplified the proof
implementation in [PR #4](https://github.com/marcusdavidwebb/SubGaussianTailBounds/pull/4).
The canonical root's bytes, both jointly proved quartets, hypotheses, endpoints
and sample-space universes are unchanged. No new bound or novelty is claimed;
Marcus Webb retains the acceptance decision.

Balanced integer matrix lookup, shared coefficient tables and checked logarithm
lookups reduce repeated finite arithmetic. Integer exponential, logarithm and
resolvent evaluators are proved equal to their original rational specifications,
retaining every rounding step and all finite truncation orders. Closed proof data omit
unused executable code while preserving their kernel definitions. Smaller
imports, shared analytic lemmas, structural polynomial identities and three
small module consolidations remove duplicated work. Pure polynomial certificates,
lookup/grid definitions and rational row data have separate modules from analytic
soundness. Existing Mathlib results supply the elementary square-root,
trigonometric, order and integration steps. The underlying Taylor, rounding,
Bernstein and KL arguments retain their existing attribution.

Python prepared proposed finite values and benchmark inputs; Lean checks the
exact equalities and all finite obligations. Wolfram MCP supported limited
algebraic exploration and supplied no accepted mathematical fact. Model review
is not independent human review. This revision preserves the preceding human
and model credit and the unresolved assessments in
[PROVENANCE.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/PROVENANCE.md). Iterations, measurements and verification
attempts are recorded in [HISTORY.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md); focused checks alone
are not complete verification. No verification policy or dependency pin is
changed by this proof-simplification revision.

## Unused-code cleanup — 2 November 2026

At Marcus Webb's request, Codex and parallel agents removed unused and
unreachable tactics, unused simplifier arguments, redundant section variables
and unnecessary helper parameters, updating their callers. Bindings required
by function or structure types use anonymous names where appropriate. This
cleanup preserves both quartets, the canonical hypotheses, endpoints and
universes, and does not edit the canonical statement, dependency pins or
verification policy. The canonical statement and its recorded digest were
edited separately during this work. This is source maintenance, with no new
mathematical result or novelty claim; existing human and model attribution and
the maintainer's acceptance decision are unchanged.

Three focused checks using the unchanged kernel/axiom worker passed for
`Scalar.UpperExponentialTools`, `KL.Certificates.Polynomial` and
`Main.VariationalOptimization`. Final source compilation passed for all 565
maintained modules, with no unused-code diagnostics in the proof implementation.
The two unused `hn` names in the protected canonical source remain untouched.
A full attempt compiled the then-current 565
modules and elaborated 22 acceptance obligations, then detected that the
protected canonical artifact had changed during compilation. The final full
verification attempt stops at the canonical integrity guard: the statement's
SHA-256 is `60817c0a497cdb99b7b22773c920f4d1ae09e6195d16a4652b5468d5902ba46b`,
whereas the separately edited guard records
`f92b4dcee6d8bf6460c5097ad57643eca7d7d922de43afa08477e3a39745854f`.
Complete independent replay and canonical verification are not claimed.

## Repository debloat — 2 November 2026

At Marcus Webb's request, Codex and parallel agents removed unused hybrid and
retired-theorem interfaces, two conditional canonical wrappers and three
duplicate certificate-assembly modules. The public general/unit proofs now
import their live row estimates explicitly. All numerical proof families,
canonical propositions, quartets, universes, dependency pins and verification
checks are preserved. Historical source links remain available in Git history.

The repository catalogue is replaced by a short source layout; setup, templates
and the refactor plan are shortened around existing entry points. This is
maintenance, with no new bound or novelty claim. Existing attribution,
unrelated proof/TeX work and the maintainer's acceptance decision remain
unchanged. Actual checks and limitations are recorded in
[HISTORY.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md#repository-debloat--2-november-2026).

## Shared tail statement — 2 November 2026

Marcus Webb refactored the canonical statement through the common fixed-parameter
`TailBoundAt` proposition and requested repository synchronization. Codex and
parallel agents preserved his source bytes, adapted the general/unit equivalence
proofs, updated the protected digest and documentation, and regenerated the
TeX/PDF. The general parameter moves before the sample-space arguments; the
unit specialization simplifies `K = 1` to the preceding thresholds. The
expanded equivalence targets, baseline quartets, hypotheses, endpoints and
arbitrary universes remain unchanged.

This is a statement-presentation and compatibility change, with no new bound,
novelty or acceptance claim. Existing mathematical credit and unresolved
assessments remain as recorded in [PROVENANCE.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/PROVENANCE.md).
The maintainer explicitly deferred full Lean verification; the
[validation record](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md#shared-tail-statement--2-november-2026)
distinguishes focused checks from the complete before-merge requirement.

## Final statement synchronization — 2 November 2026

Marcus Webb declared his latest root statement final and requested repository
consistency changes. Codex and parallel agents preserved those exact bytes,
adapted `StatementEquivalence.lean` to `GaussianSingularValueTails` and the new
dimension-argument order, repinned the source guard, and synchronized the README,
TeX/PDF and handoff plan. The mathematical requirements, quartets, arbitrary
universes, dependency pins and acceptance checks are unchanged. The README table
now displays the same exact general coefficient as `1.50`.

This is maintenance of the supplied statement and its consumers, with no new
bound, optimality or acceptance claim. Existing credit and unresolved assessments
remain unchanged. The [validation record](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md#final-statement-synchronization--2-november-2026)
distinguishes focused checks from the complete verifier, which was not run at
the maintainer's request.

## Refactor continuation — 2 November 2026

At Marcus Webb's request, Codex and parallel agents removed three support
modules outside the canonical results' import closure, retained their historical
credit, consolidated ignore rules and corrected obsolete checking descriptions.
The launcher and verification changes are proposed maintenance, not an accepted
policy or a new mathematical result. The optional computation pilot is deferred.
Checks and outstanding review are recorded in [HISTORY.md](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/480fa4b70f12c1362c88c7e05abce1a853f91bb9/docs/HISTORY.md).

## Proof architecture simplification — 2 November 2026

At Marcus Webb's request, Codex and parallel agents reconsidered the numerical
proof and verification workflow at the fixed general `(3.84, 1.58, 2.35, 1.50)`
and unit `(1.32, 1.12, 2.32, 1.42)` quartets. This is a local implementation for
his review, with no new bound, optimality, novelty or acceptance claim.

The supplied root source needed two syntax repairs: remove unmatched closing
parentheses and separate `Real.exp` from its argument. Its mathematical
expressions, hypotheses and dimension conditions are preserved. The preceding
statement-equivalence adapters also needed correction: match the actual isotropy/
sub-Gaussian argument order, derive measurable events from measurable rows in the
forward direction, and project probability bounds in the reverse direction.
The imported definitions and dependency revisions are unchanged.

The general mean proof replaces inherited uniform log-parameter subdivisions
with sufficient adaptive convexity bounds. The endpoint mean uses exact exponential-resolvent interval integrals instead of
8,000-point quadrature and decay-prefix tables. The unused polynomial positivity
slack permits coarser entropy allowances at the same required coefficient. Its
4,502 joint and 100 small-shape intervals replace 60,352 and 513, respectively.
The polynomial witnesses use shared exact integer transforms instead of repeated intermediate matrices. The unit
public/internal tail contract uses the rational `1.42`; the cheap square-root
comparison is local to its upper-tail estimate. The existing barrier, Taylor,
rounding and Bernstein methods retain their historical attribution. Exact
Python arithmetic proposes finite witnesses; Lean proves every retained fact.
Wolfram MCP supports scalar exploration and supplies no accepted mathematical
fact. Model review is not independent human review.

The two published quartets now have one exact rational source. Focused and full
local checks share a two-result specification. The obsolete accepted-constants
snapshots, trusted-checkout comparisons and 22-obligation interface are removed;
Marcus reviews coefficient and verification-policy changes. Full independent
kernel replay, type/universe/axiom checks, source coverage and checked-input
identity remain required. CI is read-only lightweight administration. Actual
measurements and completed validation are recorded in [PERFORMANCE.md](docs/PERFORMANCE.md).

The preceding provenance record's unresolved assessments remain unresolved:
the selector/Gaussian spectral-limit discussion uses established ingredients
with elementary consequences; the sparse example was recorded as inherited from
Jeong–Li–Plan–Yılmaz, with elementary normalization and separate-tail deductions.
Those sharpness discussions and the paper's applications lie outside these two
Lean propositions. Neither verification nor an unsuccessful literature search
establishes priority or novelty. The paper remains in preparation.

## Editable root statement and generated presentation — 3 November 2026

Marcus Webb revised the authoritative root statement and requested synchronization
of its proof and documentation dependencies. Codex and parallel agents removed the
fixed source-hash gate, simplified document generation around the current Lean
source and README theorem, and retained source identity checks during verification.
Generation refreshes the README's Lean copy and exact constants table; its check
mode is read-only. The root's only subsequent edits add the whitespace Lean
requires after `Real.exp`, with no change to its mathematical expressions.

The revised root omits the earlier coefficient-positivity conjunctions and explicit
measurable-row premise. The adapters prove the required positive-coefficient
specializations using measurable representatives of almost-everywhere measurable
rows and invariance of the tail measures under almost-everywhere equality. The
required quartets, arbitrary universes, normalization and endpoints are unchanged.
No third-party dependency or toolchain version is changed. This compatibility work
adds no bound, optimality, novelty or acceptance claim; earlier attribution and
unresolved assessments remain unchanged.

Validation passes both local Lean commands, including 339 independent kernel
replays and both exact theorem targets; the axiom audit reports only `propext`,
`Classical.choice` and `Quot.sound`. Both modes report checked-input SHA-256
`a34f7c69faed51ba6247c7771f03b810473ab9b5f43020a1cb972163d9c84b32`.
The Python suite passes 99 tests, with 22 optional Lean integration tests skipped;
canonical presentation, TeX synchronization and all three numerical-generator
checks also pass. Existing pinned dependency artifacts are reused; the focused
run rebuilds 216 stale project modules and the full run reuses them. Build and
replay concurrency are both 24 workers. Logs are retained under
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/statement-sync-20261103/`.

## Python test simplification — 3 November 2026

At Marcus Webb's request, Codex and parallel agents shortened the Python tests
around document synchronization, environment setup and verification behavior.
The changes remove workflow/source-text assertions, duplicate document-formatting
cases, a fake verification environment and a redundant Lake freshness fixture.
Focused behavior tests retain synchronization, preservation of user edits,
dependency reuse, input identity, report/source coverage and failure propagation.
The process-race regressions and all adversarial Lean acceptance/replay cases
remain. Workflow details and some auxiliary formatting/error paths now rely on
review instead of dedicated regression tests.

Only tests and this attribution entry change. The mathematical sources,
production generators, verifier, toolchain and package pins are unchanged; the
previous successful focused/full checked-input inventory still matches exactly.
This is maintenance with no mathematical, novelty or acceptance claim, and
preserves the earlier human/model attribution and unresolved assessments.

Test sources shrink from 2,181 to 1,715 lines, with 87 test cases instead of 121.
The ordinary run passes 66 cases and skips 21 opt-in Lean integrations. A separate
run passes both retained Lake freshness tests and their 11 accompanying scheduler
tests using the existing pinned central workspace. The unchanged Lean proof was
not rebuilt or replayed again for this test-only change.

## Further test reduction — 3 November 2026

At Marcus Webb's request, Codex and parallel agents further reduced the tests
to nine workflow tests in three files, totaling 339 lines. These cover document
generation and preservation, source/artifact identity, maintained-source coverage,
real Lake cache invalidation, and Lean acceptance/replay with valid and invalid
examples. The invalid cases include wrong constants, restricted universes, extra
assumptions, forbidden axioms, forged proofs and native-computation assumptions.
Individual helper/setup tests, mock scheduler harnesses, governance checks and
specialized race, spoofing, collision and format fixtures are removed; these
auxiliary paths have less dedicated regression coverage.

No production generator, verifier, mathematical source, dependency pin or
toolchain changes. The earlier full verification's checked inputs still match.
Earlier attribution and unresolved assessments remain unchanged. An intermediate
875-line suite passed all 42 cases; its log remains `leaner-tests.log`. The final
nine workflow tests all pass with real Lean/Lake enabled in the existing central
workspace. Their log is
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/statement-sync-20261103/workflow-tests.log`.

## Structural numerical certificates — 3 November 2026

At Marcus Webb's request, Codex and parallel agents profiled the current proof
and removed a redundant finite-domain search from every general mean numerical
row. A shared structural lemma derives interval order from the already checked
partition. Generated endpoint proofs reuse the existing grid-endpoint lemma.
The rational certificate interface now has its own smaller import closure;
its declarations are moved unchanged. All 1,331 rows, 6,267 nodes, 4,936 intervals
and exact numerical witnesses are retained.

The root statement, required quartets, imported mathematical definitions and
dependency revisions are unchanged. This is a computational simplification of
the inherited proof, with no new bound, optimality, novelty or acceptance claim.
Existing human/model attribution and unresolved assessments remain unchanged;
model review is not independent human review. The actual starting implementation,
rejected experiments, controlled measurements and completed validation are
recorded in [PERFORMANCE.md](docs/PERFORMANCE.md).

## Lake statement-checking interface — 3 November 2026

At Marcus Webb's request, Codex and parallel agents added a readable Lake target
showing both exact, universe-polymorphic propositions and applying the existing
canonical proofs. An intermediate version used an opt-in bootstrap in an external
workspace. Its direct Lake target, focused check, full verification and 14 workflow
tests passed with the existing pinned toolchain and dependency artifacts. The full
run replayed 341 modules with 24 build and replay workers. That bootstrap was tested
offline and against the existing package workspace; a fresh network installation
was not tested.

Marcus then requested a conventional root Lake project, with `lake build` defaulting
to the visible statement target. Codex and parallel agents replaced the intermediate
bootstrap with root Lake configuration and retained the reuse-only external setup
for local verification. The root statement, constants, imported definitions and
dependency pins are unchanged. This is an accessibility change, with no new
mathematical result; earlier human/model roles and unresolved attribution
assessments remain unchanged. At Marcus's request, the current source state has not
been fully built or independently replayed; the intermediate checks above do not
verify this later configuration. A no-build Lake check and the focused type,
universe and axiom audit passed using existing project and dependency artifacts,
with one build worker. Offline configuration and source-identity tests also passed.

Future entries should identify the contributor, affected regime or implementation,
explanation, attribution, supersession and actual commit/PR links when available.
Preserve earlier substantive credit and follow [CONTRIBUTING.md](CONTRIBUTING.md).
