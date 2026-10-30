# Provenance

This record preserves attribution and responsibility after removal of the
historical supplement. Current validation is in [HISTORY.md](HISTORY.md);
substantial contributions are credited in [CONTRIBUTIONS.md](../CONTRIBUTIONS.md).

## Human and tool roles

The accompanying paper, *Sharp tail bounds for the extreme singular values of
sub-Gaussian matrices*, is by Marcus Webb and Morgan Lynch-Davies and is in
preparation. They undertook extensive preceding mathematical work yielding
weaker bounds. No public paper version or repository release is recorded here.

The historical supplement was distinct from that preceding work. Marcus Webb
was its sole author and stated that its entire proof and exposition were
AI-generated without direct input from him. He takes responsibility for its
arguments, exposition, certificates, attribution and correspondence between
mathematical statements and numerical checkers.

Section S2 identified Codex as GPT-6. The recorded formalization also involved
parallel GPT-6.1 Sol Ultra workers and a coordinator. Codex refined arguments,
searched literature, wrote and ran exact checkers, prepared exposition, developed
formalizations, resolved elaboration problems and checked correspondence.
Models generated candidate mathematics and code; Lean checked proof terms and
Python executed the historical external exact arithmetic. Model reviews are
not independent human review. The original disclosure remains in the
[archived Section S2](https://github.com/marcusdavidwebb/SubGaussianTailBounds/blob/73aa7fe4db3d982d446e292d82a34b6af784238b/supplementary.tex).

## Historical verification and completion

The hybrid verification observed on 20 October 2026 covered 147 KL modules,
32 shared modules and 3,224 audited declarations, using only `propext`,
`Classical.choice` and `Quot.sound`. The original checker and eleven interface
runners passed. Lean then proved an analytic implication from finite numerical
conditions; external Python checked those conditions without supplying Lean
proof terms. This did not prove either complete canonical baseline. Historical
checker correctness and correspondence were part of that hybrid trust boundary;
source hashes did not establish mathematical correspondence.

On 23 October, Codex and parallel agents completed the general canonical theorem.
The unit theorem remained unfinished and an interrupted replay was not counted
as success. Python prepared rational data whose identities and inequalities
were proved in Lean; Wolfram MCP supported a small numerical exploration and
supplied no accepted facts. On 25 October, the remaining unit entropy and
polynomial families and public result interface were completed. Both canonical
proofs in that completed formalization included all finite numerical obligations.
Supporting Python performs administration and supplies no mathematical oracle.

Historical dates, source inventories, timings and earlier conditional results
remain in the [archived validation records](HISTORY.md#historical-sources).
Local validation does not imply paper publication, novelty or completion of a
hosted workflow. Later source hashes do not retroactively alter an earlier run.

## NLA-lib statement imports — 30 October 2026

At Marcus Webb's request, Codex replaced local row predicates and singular-value
extrema in the canonical statement with actual Lean imports from
[NLA-lib commit 6491e752](https://github.com/NLA-lib/NLAlib/tree/6491e7528c1b1e68e46301cde6a76ae153e8e834).
Credit for these definitions and their supporting theorems belongs to NLA-lib's
contributors. The new compatibility proofs relate its variance proxy `K²`,
isotropy and ordered singular values to the preceding expanded assumptions
and extrema. Row measurability remains explicit, and the statement retains
both sharp quartets, separate non-strict measurable events and arbitrary
sample-space universes. This imports no replacement proof of the sharp tail
bounds and makes no new mathematical or novelty claim.

The dependency migration uses separately stored Lean/Mathlib 4.33.1 and NLA-lib
under `~/Lean/`, preserving the older 4.19.0 environment. NLA-lib retains its
Apache 2.0 licence; no dependency source is copied into this repository.
The complete proof library, both sharp canonical results and the full statement
equivalences compile with the new environment. The generated canonical
acceptance obligations also compile and pass their supplemental axiom audit.
Independent kernel replay was explicitly deferred by Marcus Webb. These checks
do not establish complete verification of the migrated library or change the
scope of the historical runs. See [HISTORY.md](HISTORY.md) for the validation
record and [CONTRIBUTIONS.md](../CONTRIBUTIONS.md) for the implementation attribution.

## Real-valued probability formulation — 30 October 2026

Marcus Webb explicitly authorized this canonical statement change, implemented
with Codex assistance. Under a probability-measure instance the real-valued
tail inequalities are equivalent to the preceding `ENNReal` inequalities;
the separate equivalence module records the formal bridge. This does not claim
a new bound or resolve earlier attribution or novelty questions. The validation
of the earlier NLA-lib source does not establish validation of this revision.
The authorization is specific to this change; future unauthorized canonical
changes remain prohibited.

## Canonical helper simplification — 30 October 2026

At Marcus Webb's request, Codex removed the unused dimension proof parameter
from the tail helper and an import already available transitively. Marcus Webb
also removed an unused scope opening and explanatory comment. The dimension
hypothesis remains in both theorem statements, and a temporary Lean check
established definitional equivalence of both full propositions. This makes no
new mathematical or novelty claim and does not resolve earlier assessments.
This authorization is specific; future unauthorized canonical changes remain
prohibited.

## Scope and unresolved assessments

The formalization proves the two canonical singular-value tail propositions,
not the paper's applications or sharpness discussion. Historical paths such as
`main.tex`, `OLD/paper.tex` and `supplementary/lean/` refer to the original paper
checkout, not missing files promised by this repository. The retired standalone
`n^(1/6)` theorem is not restored; its shared modules needed by KL remain.
The removed bibliography and label snapshots supported the old document only.
The supplement's introductory arXiv assertion lacked supporting publication
evidence in this repository; the paper remains described as in preparation.

The parent-paper audit's unresolved attribution and novelty assessments remain
unresolved. It identified the selector/Gaussian spectral-limit discussion as
established ingredients with elementary consequences, and the sparse example
as inherited from Jeong–Li–Plan–Yılmaz with elementary normalization and
separate-tail deductions. These sharpness discussions are outside the Lean
theorem's scope. Other questions remain subject to source review.

Verification establishes neither priority nor novelty nor completeness of a
literature assessment. Future work follows the
[research and attribution rules](../CONTRIBUTING.md#research-and-credit).
