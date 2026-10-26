# Provenance and verification scope

This note preserves historical attribution independently of the temporary
supplement. The repository targets complete Lean proofs of the two canonical propositions.
See [MIGRATION.md](MIGRATION.md) for present proof scope and actual validation
evidence, kept separate from the historical hybrid runs.

The accompanying paper, *Sharp tail bounds for the extreme singular values of
sub-Gaussian matrices*, by Marcus Webb and Morgan Lynch-Davies, is in preparation.
No public paper version or repository release is asserted by this preparation.

## Human and tool roles

The paper authors undertook extensive mathematical work yielding weaker bounds
before working with Codex. The supplementary document is distinct from that
earlier work. It lists Marcus Webb as sole author and states that its entire
proof and exposition were AI-generated without direct input from him; he takes
full responsibility.

Section S2 records that the authors identified Codex as GPT-6. The recorded
formalisation also involved parallel GPT-6.1 Sol Ultra workers and a coordinator.
Models generated candidate mathematics, code and exposition; Lean checked formal
proof terms and Python executed external exact arithmetic. Reviews by additional
model instances are not independent human review.

## Historical verification

The baseline quartets are `(96/25,79/50,47/20,3/2)` for every `K ≥ 1` and
`(33/25,28/25,58/25,sqrt(2))` for `K = 1`.

In that historical development, Lean proved the analytic implication from the
original row assumptions and finite rational conditions. External exact Python
checked those conditions and supplied no Lean proof terms. Checker correctness,
execution and correspondence to the Lean predicates were part of its hybrid trust boundary. Source digests
detect drift and do not prove correspondence.

The post-cleanup baseline verification was observed on **20 October 2026**:
147 KL modules and 32 shared supporting modules built; 3,224 audited declarations
used only `propext`, `Classical.choice` and `Quot.sound`; the original checker and
all eleven interface runners passed. The recorded environment, timings, source
inventory and preceding history remain in
[the verification report](../lean/VERIFICATION_REPORT.md),
[the completed plan](../lean/FORMALISATION_PLAN.md) and
the original `lean/verification_manifest.json` in Git history.

Portability and CI preparation are later changes. Historical hashes and
timestamps describe the earlier run; a new packaging hash or document build
does not retroactively change that run. Current validation is reported separately.

The root `MainTheoremStatement.lean` supplies definitions of the canonical
propositions, not proofs. The old conditional results are useful mathematical
components; they have not become unconditional canonical proofs merely through
the repository migration. Python's historical role remains part of this record
after its certificate programs are retired. Current acceptance requires Lean
proofs of every numerical obligation used by the canonical results.

The retained `supplementary.tex` and PDF are historical, pending later deletion.
They are not maintained alongside future Lean changes. The source's introductory
arXiv assertion is not supported by publication evidence available here; the
repository continues to describe the paper as in preparation. See the
[historical supplement notice](HISTORICAL_SUPPLEMENT.md).

## Historical paths and omitted material

Historical records use paths such as `main.tex`, `OLD/paper.tex`,
`supplementary/lean/`, central workspace paths and a temporary log path.
These identify the original paper checkout or validation environment, not
files promised in this standalone collection. The retired standalone
`n^(1/6)` theorem is not restored; its 32 shared modules needed by KL remain.

The paper's background, applications, sharpness examples and proofs remain in
the paper. The historical exact checker also checked finite arithmetic associated with
some examples, not their analytic arguments. Five label snapshots retain references
to the in-preparation paper without distributing it or linking a missing PDF.

## Attribution and novelty

The parent-paper audit retains unresolved assessments. This preparation neither
resolves nor erases them, and makes no priority/novelty claim from verification.
The recent audit identifies the selector/Gaussian spectral-limit discussion as
established ingredients with elementary consequences, and the sparse example
as inherited from Jeong–Li–Plan–Yılmaz with elementary normalization and
separate-tail deductions. Those sharpness discussions are outside the Lean
theorem's scope. Other attribution and novelty questions remain subject to
source review. Future contributions follow
[RESEARCH_PROTOCOL.md](RESEARCH_PROTOCOL.md).

## Migration work on 23 October 2026

The general canonical theorem was completed during this migration, separately
from the historical hybrid run. Codex and parallel agents developed adapters,
finite polynomial proofs and exact arithmetic proofs; Lean checked their proof
terms. Python was used to prepare rational data, whose identities and signs were
then proved in Lean, not accepted on Python authority. Wolfram MCP supported a
small numerical exploration; it supplied no Lean proof terms or accepted facts.
At the end of that session, the unit canonical theorem remained unfinished.
That status and the interrupted replay are preserved in the migration history.

## Completion work on 25 October 2026

Codex and parallel agents completed the remaining unit entropy and polynomial
families, assembled the exact unit theorem and public current interface, and
replaced the Python certificate pipeline. Generated rational data was accepted
only through Lean proofs of its identities and inequalities. Supporting code
schedules builds, protects source/artifact provenance and reports audits; it
supplies no mathematical oracle. The [migration record](MIGRATION.md) records
the actual final checks separately from both earlier sessions. Hosted policy
activation and paper publication are not implied by local verification.
