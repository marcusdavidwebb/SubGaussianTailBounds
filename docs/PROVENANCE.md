# Provenance and verification scope

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

## What was checked

The baseline quartets are `(96/25,79/50,47/20,3/2)` for every `K ≥ 1` and
`(33/25,28/25,58/25,sqrt(2))` for `K = 1`.

Lean proves the analytic implication from the original row assumptions and
finite rational conditions. External exact Python checks those conditions;
it supplies no Lean proof terms. Checker correctness, execution and correspondence
to the Lean predicates remain part of the hybrid trust boundary. Source digests
detect drift and do not prove correspondence.

The post-cleanup baseline verification was observed on **20 October 2026**:
147 KL modules and 32 shared supporting modules built; 3,224 audited declarations
used only `propext`, `Classical.choice` and `Quot.sound`; the original checker and
all eleven interface runners passed. The recorded environment, timings, source
inventory and preceding history remain in
[the verification report](../lean/VERIFICATION_REPORT.md),
[the completed plan](../lean/FORMALISATION_PLAN.md) and
[the original manifest](../lean/verification_manifest.json).

Portability and CI preparation are later changes. Historical hashes and
timestamps describe the earlier run; a new packaging hash or document build
does not retroactively change that run. Current validation is reported separately.

## Historical paths and omitted material

Historical records use paths such as `main.tex`, `OLD/paper.tex`,
`supplementary/lean/`, central workspace paths and a temporary log path.
These identify the original paper checkout or validation environment, not
files promised in this standalone collection. The retired standalone
`n^(1/6)` theorem is not restored; its 32 shared modules needed by KL remain.

The paper's background, applications, sharpness examples and proofs remain in
the paper. The exact checker also checks finite arithmetic associated with some
examples, not their analytic arguments. Five label snapshots retain references
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
