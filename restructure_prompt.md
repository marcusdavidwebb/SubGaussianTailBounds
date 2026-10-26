# Repository restructuring prompt — revised draft

This is a draft specification for a future restructuring task, revised to
incorporate the maintainer's answers. Editing this document does not carry
out that restructuring. The design questions raised so far are resolved.

## Objective

Restructure this repository around complete Lean formalizations of the two
propositions defined in the root file `MainTheoremStatement.lean`:

```lean
SubGaussian.GeneralSingularValueTailBound 3.84 1.58 2.35 1.5
SubGaussian.UnitSingularValueTailBound 1.32 1.12 2.32 (Real.sqrt 2)
```

The repository must supply proofs of both baseline results and make it easy
for someone to contribute a new Lean formalization of either result at
constants that are componentwise no larger than the current best accepted
constants for that regime. Initially these are the specified baselines;
subsequent replacements must preserve every improvement already achieved.
An alternative proof with all four current constants unchanged is eligible
for review. A contribution need not prove both regimes. The maintainer
reserves judgment on accepting or rejecting every PR.

Maintain **one Lean formalization** of the two results, potentially spread
across many supporting modules. Accepted contributions update or replace
the relevant part of this implementation; do not accumulate independent
implementations in the working tree. Record their history in one Markdown
file, initially containing one contribution credited to Marcus Webb.

**Prove the whole result in Lean and remove the Python certificate pipeline.**
This includes all finite numerical inequalities needed by the proof. An
external computation or a Lean theorem conditional on unproved certificate
conditions does not meet the objective.

Do not maintain or accept natural-language proofs. Contributions consist of
Lean proofs with concise explanation and attribution. The README retains
the natural-language **theorem statement**, but contains no prose proof or
proof outline. `supplementary.tex` is a temporary historical document that
the maintainer intends to delete later; it is the explicit temporary
exception to removing the old prose proof from the repository.

## 1. Protect the single authoritative statement

`MainTheoremStatement.lean` is the single point of truth. **Do not change it.**
Keep its exact name, root location, and bytes, including imports, comments,
definitions, hypotheses, conclusions, and universe parameters. Do not delete,
rename, relocate, replace, or shadow it with another module of the same name.
Place proofs, adapters, and auxiliary lemmas in other files that import it.

At the time this draft was prepared, this file was present but untracked.
Preserve that existing working copy; do not reset it to Git HEAD, where it
does not yet exist. Integrate these exact bytes into the eventual tracked
source tree and build. Its observed SHA-256 was:

```text
eb24daadaf9c0aaac3bea45128a08b81ba5492183bcbb6eb03b62c3245c2701c
```

Record and compare its bytes before and after the work. A digest is an
immutability check, not mathematical evidence. If the starting file differs
from this snapshot, identify the discrepancy before proceeding; do not
silently choose or manufacture a replacement.

Inventory every repository-local instruction source for AI agents, including
hidden and editor-specific files. Update `AGENTS.md` and every other such
source found or created to state this prohibition explicitly. This prompt
is also subject to it. Future instructions must not grant an exception for
formatting, compatibility, convenient proof development, or maintenance.

Enforce the protection in the trusted contribution/CI policy as well as prose.
Candidate changes must not be able to edit both the canonical statement and
its expected digest to evade the check. Compile the actual root module and
verify that acceptance checks import that module. README copies are
presentations of this source, never competing definitions.

If a mathematical or compatibility problem is found in the protected file,
report the precise problem. Do not fix it by changing the file or weakening
the required theorem.

## 2. Inspect and plan the migration

Before making changes, read `AGENTS.md`, `README.md`, `CONTRIBUTING.md`,
`CONSTANTS.md`, `lean/README.md`, `docs/RESEARCH_PROTOCOL.md`, the Lean toolchain,
Lake configuration, and manifest. Inspect the current theorem, certificate
interfaces, audits, contribution validator, tests, and CI trust boundaries.
Preserve unrelated working-tree changes.

Prepare a concise migration map covering the source layout, proof entry
points, public documentation, contribution history, verification commands,
and files to retire. Keep the structure simple; further restructuring can
happen later. Identify reusable mathematics and gaps separately.
Use the existing proof where useful; a different proof architecture is also
permitted. Do not require contributors to follow the old barrier/certificate
architecture if they can prove the canonical proposition another way.

The present library proves conditional results in
`lean/SingularValueBounds/KL/Theorem.lean`. Their `FinalCertificateConditions`
are checked by eleven external Python interfaces. The root canonical file
defines propositions, not proofs of either tail theorem, and is not currently
part of the configured library build. Passing the existing checks does not
establish the new acceptance targets.

The current gate requires a strict constants improvement, permits some
tradeoffs, and generates conditional theorem obligations. Those policies must
be replaced consistently with the contract below. Its maintenance route also
restricts new Lean modules and umbrella imports: inspect the actual trusted
base policy and explain any required migration stages. Do not claim that
editing candidate workflow files changes the policy already running from the
trusted base revision. Prepare local changes without publishing a PR.

Replace the old blanket protection of baseline implementation files with
protection of the canonical statement and complete mathematical verification.
The maintained proof modules must be editable and replaceable through the
reviewed contribution route. A rule freezing all old Lean sources would
conflict with the requested single evolving formalization.

## 3. Complete the mathematical proofs in Lean

Provide named, universe-polymorphic Lean theorems whose types are exactly
the two canonical baseline propositions. Preserve the arbitrary sample-space
universe `u` in the source definitions. No extra parameter or premise may
stand for a missing mathematical fact or computation.

When the maintained proof establishes stronger constants, derive the
baseline results as Lean corollaries, with any necessary monotonicity proved
in Lean. These corollaries are part of the same formalization, not a reason
to retain an obsolete independent implementation.

In particular, preserve:

- Positivity of all four constants and their exact values.
- Every dimension `m ≥ n ≥ 1`, every admissible probability space and matrix,
  every `K ≥ 1` in the general result, and every `t ≥ 0`.
- Measurable, mutually independent rows; centering, isotropy, integrability,
  and the exact directional MGF normalization in the canonical file.
- Both non-strict tail events, their measurability, and their probability
  bounds in `ℝ≥0∞`.
- All singular values, including zeros; rank deficiency, `n = 1`, `t = 0`,
  and zero or negative lower thresholds.
- Natural logarithms, `L = log(eK)`, the leading terms, and the separate
  failure bound `exp(-t²/2)` for each tail.

When reusing the existing library, prove the correspondence to the canonical
definitions in separate adapter modules. Check at least the singular-value
definitions, matrix/row representations, dimension evidence, directional
versus coordinate assumptions, Euclidean norms, `log(exp 1 * K)` versus
`1 + log K`, tail-event measurability, and real-valued versus `ENNReal`
probabilities. Do not assume that a similar-looking old theorem has the
required type.

Discharge every required finite condition in Lean, or replace that part of
the argument with another Lean proof. Exact rational computations, interval
estimates, polynomial certificates, finite tables, and reflection are allowed
only with soundness and concrete instances checked by Lean's kernel. Data
does not prove its own validity. External code may not serve as a mathematical
oracle or supply an unchecked fact.

Audit the final theorems and their transitive dependencies. Preserve the
existing standard axiom allowlist: `propext`, `Classical.choice`, `Quot.sound`.
Reject `sorry`, `admit`, `sorryAx`, new axioms, native-oracle dependencies,
assumed certificates, and unproved analytic side conditions. Compilation of
a conditional implication alone is insufficient.

This is substantive proof work as well as repository reorganization. If a
gap cannot be closed, document the exact remaining obligation and verified
progress. Do not label the objective complete, invent a proof, weaken a gate,
or change the canonical statement to obtain a passing build.

## 4. Remove Python mathematical certification

The final active repository must not depend on Python certificates or Python
mathematical checking. Remove the obsolete Python certificate implementations,
their runners, checker mappings, generated-certificate acceptance interfaces,
and CI jobs once their required mathematical content has been replaced by
Lean proofs. Include `check_main_constants.py`, the numerical/interface
checkers under `lean/`, and the hybrid verification entry point in this review.
Do not remove useful Lean mathematics merely because it was previously used
by the hybrid pipeline. Lean finite-condition structures and certificate
lemmas may remain if every required concrete instance is proved in Lean and
no unproved certificate premise survives in an accepted target.

Migrate all active documentation, contribution templates, schemas, tests,
commands, audit messages, badges, and workflow dependencies. No contributor
should be asked to submit Python certificates or invoke a retired hybrid check.
Do not leave an executable copy of the old certificate pipeline in an archive
inside the working tree. Git history and a concise historical account can
preserve what it did.

This explicitly requested removal supersedes the old requirement to retain
Python checkers as active verification. Replace that requirement with complete
Lean verification; do not merely omit checks while retaining their conclusions.

Python used solely for repository administration, document building support,
or metadata validation may remain. Such tooling
must not establish mathematical truth or bypass Lean acceptance checks.

## 5. Define the contribution contract

For a general-regime submission, require a Lean proof of
`SubGaussian.GeneralSingularValueTailBound α β γ δ` and Lean proofs that:

```text
α ≤ 3.84    β ≤ 1.58    γ ≤ 2.35    δ ≤ 1.5
```

For a unit-regime submission, require a Lean proof of
`SubGaussian.UnitSingularValueTailBound α β γ δ` and Lean proofs that:

```text
α ≤ 1.32    β ≤ 1.12    γ ≤ 2.32    δ ≤ Real.sqrt 2
```

The canonical proposition already requires the four constants to be positive.
The decimals denote exact Lean real numbers, not floating-point approximations;
the unit bound uses the exact square root.

These original baselines remain absolute ceilings and permanent theorem
targets. In addition, every replacement must preserve the current best
accepted quartet for its regime. If that quartet is
`(α_current, β_current, γ_current, δ_current)`, require Lean proofs that:

```text
α ≤ α_current    β ≤ β_current    γ ≤ γ_current    δ ≤ δ_current
```

Initially the current quartets are the original baselines. After an accepted
improvement, use the new jointly proved quartet as the comparison ceiling
for the next replacement. No component may increase, even if the proof is
simpler, faster, or improves a different component. For example, replacing
`(3.70, 1.58, 2.35, 1.5)` with `(3.75, 1.55, 2.35, 1.5)` is prohibited:
the increase in `α` loses an accepted improvement despite meeting the original
baseline. Keep the two regimes' current quartets distinct.

All comparisons must hold simultaneously for the same proved quartet.
Equality in any or all entries is allowed; strict improvement is optional.
Use the trusted current accepted result for comparison, not an arbitrary
older predecessor or candidate-supplied ceiling. Recheck against the updated
accepted result if the target branch advances during review. Never combine
coordinates from different theorems without proving their joint claim.

Allow exact constants expressed in Lean, with their comparison proofs, rather
than arbitrarily restricting them to the current JSON arithmetic format.
Use fully qualified, stable declaration names. Generate or maintain checked
acceptance obligations that apply the submitted theorem directly to the
canonical proposition and verify the baseline ceilings and all four
comparisons with the current accepted quartet. Metadata alone cannot certify
the constants or theorem, and editing the displayed current constants cannot
authorize a regression.

Give contributors a small, documented interface and a clear place to edit
the maintained Lean proof. A complete submission contains the Lean sources,
the result and regime, comparison proofs, concise explanation and attribution,
and an entry in the Markdown contribution history. Explain how to run the
common verification command. Do not require or accept a separate
natural-language proof, PDF proof, or Python certificate package.

Explanation may describe the purpose of a change, relevant Lean declarations,
reuse, and attribution; it is not a second proof artifact. Keep ordinary
useful Lean comments and documentation. Do not introduce per-contribution
prose-proof directories or a new elaborate metadata registry.

Support alternative formalizations at unchanged constants as proposals to
replace the existing implementation, as well as strict improvements. An
eligible submission is not automatically accepted or merged: Marcus Webb
reserves judgment on accepting or rejecting every PR, including equal-constant
replacements. Do not impose an additional automatic criterion such as a
required speedup or shorter proof. This discretion does not permit an increase
in any current constant or a waiver of complete Lean verification. Preserve
both regimes when integrating a contribution concerning just one of them.
Remove superseded independent implementations from the working tree once
their replacements are verified; retain their credit and Git history.

Keep meaningful history without requiring a strict-improvement predecessor
for an equal-constant replacement. Do not relabel historical conditional
results as complete proofs of the canonical propositions. Update the recorded
current quartet only when the corresponding verified improvement is accepted,
and keep all previous accepted improvements represented in the maintained
theorems or their Lean corollaries.

## 6. Reorganize the repository and public documentation

Make the repository's main identity a Lean formalization project with two
fixed target statements and an open contribution interface. Replace the
current presentation centered on supplementary materials and hybrid checks.
Use a small number of entry points so a newcomer can find the theorem,
the maintained Lean proof, its verification command, and contribution history.
Avoid introducing a hierarchy for multiple proof implementations.

Use this minimal layout as guidance, retaining useful existing module paths:

```text
MainTheoremStatement.lean       # immutable canonical source, stays here
AGENTS.md                      # includes explicit immutable-source rule
README.md                      # purpose, NL theorem, expandable Lean statement, build
CONTRIBUTING.md                 # either-regime contribution contract
CONTRIBUTIONS.md                # one initial contribution: Marcus Webb; later history
lean/                          # small build templates and verification entry points
  SingularValueBounds/         # the single maintained formalization and its support
docs/                          # only essential setup, trust, and provenance detail
supplementary.tex              # historical only, pending the maintainer's later deletion
```

This is not a demand to move every file. Preserve required licensing and
configuration files. Consolidate duplicated documentation where useful;
keep `CONSTANTS.md` only if it serves a clear purpose beyond the README.
Retire the old prose-proof templates and certificate contribution registry
when their active roles have been replaced. Prefer a small Lean acceptance
module and the Markdown history to parallel JSON and prose submission systems.
Do not replace the old registry with an elaborate Markdown-parsing framework.
Do not retain obsolete machinery solely to preserve the previous layout.

Keep compiled outputs and dependencies outside this tree. Adapt the exact
module arrangement to Lean's import requirements without moving or editing
`MainTheoremStatement.lean` or creating another editable authoritative copy.
Avoid moving hundreds of modules solely for appearance; reorganize according
to their final role and update every affected import and link.

The README must include:

1. The new purpose and both exact baseline targets, with an accurate current
   verification status and the current best accepted quartet for each regime
   when it improves on the baseline.
2. The natural-language theorem currently in `supplementary.tex`, labeled
   `thm:explicit-constants` (Theorem S1.1): hypotheses, MGF inequality, definition
   of `L`, both tail inequalities, and both quartets. Convert it to readable
   Markdown mathematics without changing its content. Explain the `K = 1`
   specialization and the meaning of the four constants. Do not include a
   natural-language proof or proof outline.
3. The full annotated Lean statement from `MainTheoremStatement.lean`, including
   its supporting singular-value definitions, in an expandable section using
   Markdown-compatible `<details>` and `<summary>` elements. Reproduce the
   entire file inside a fenced Lean block, generated or mechanically checked
   against the source so that the displayed statement cannot drift.
4. Links to the actual complete Lean proof declarations and implementation
   modules, clearly distinguished from statement definitions.
5. A short build/verification quickstart, contribution example, the rule that
   no current constant may increase, the maintainer's discretion over eligible
   PRs, and links to proof status, credit, and detailed setup.

The user's phrase “Lean proof currently in MainTheoremStatement.lean” refers
to a file that currently contains statement definitions. Describe these
accurately as the formal statement; the new theorem proofs belong elsewhere.
The natural-language theorem statement remains useful for readers and is
distinct from the natural-language proof that is being retired.

Remove active standalone natural-language proofs and proof outlines elsewhere
in the repository as well. Mark `supplementary.tex` and any temporarily retained
associated PDF explicitly as historical, preferably through a short historical
notice rather than revising their mathematics. Do not keep the supplement
updated with future Lean changes or require it for building or understanding
the current formalization. Preserve concise attribution and provenance outside
it so the maintainer can delete it later without losing that information.

Synchronize `AGENTS.md`, the root and Lean READMEs, `CONTRIBUTING.md`,
`CONSTANTS.md`, contribution documentation/templates, issue and PR templates,
CI documentation, and inventory/export tooling with the new purpose. Remove
stale requirements and broken references, and remove or consolidate documents
that no longer have a role. Preserve licenses and substantive credit. Keep
historical descriptions explicitly historical.

## 7. Build, verification, and trusted CI

Reuse the installed central Elan toolchains. Inspect the inventory before
invoking the pinned Lean version; do not trigger automatic installation.
Preserve Lean 4.19.0 and all locked dependency revisions, including Mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

Reuse `~/Lean/SingularValueBounds/.lake/packages/` only where it matches those
pins. Do not clone Mathlib again, upgrade dependencies, or overwrite the
SingularValueBounds project's build directory. Keep this checkout's resolved
Lake configuration, manifest, dependencies, caches, and compiled outputs in
its own external workspace under `~/Lean/`. Use
`~/Library/Caches/mathlib` for `MATHLIB_CACHE_DIR`. Do not symlink bulky
dependencies into this repository. Diagnose missing paths, versions, and
permissions rather than silently reinstalling. Preserve the separately
documented disposable hosted-runner setup where compatible with these pins.

Provide one documented command for complete Lean verification. It must
compile the protected statement, the single current formalization of both
results, its baseline corollaries and current exact comparisons, and the
relevant axiom/import audits. It need not rebuild superseded implementations
from Git history.
An unrelated library build cannot stand in for those targets.

Preserve the trusted CI separation between candidate execution and privileged
status reporting. Candidates must not gain secrets or write credentials or
be able to exempt their own claims. Update the required status aggregation to
reflect the new Lean checks and remove the external-certificate job. Preserve
relevant Markdown/documentation checks. Retire the historical supplement build
as a required check for current Lean contributions.

Do not rewrite the historical supplement as part of routine maintenance. If
its LaTeX source is changed, use the existing documented build command and
inspect citations, references, box warnings, and changed pages. Do not invent
missing paper sources to make its historical build work.

Add meaningful regression coverage for the changed acceptance policy:

- Either regime alone and a complete alternative at the current constants
  pass mathematical eligibility checks, subject to maintainer acceptance.
- A componentwise improvement over the current quartet with unchanged
  components passes mathematical eligibility checks.
- Any component above its regime's baseline is rejected.
- Any component above its regime's current accepted value is rejected even
  if all original baseline ceilings are met and another component improves.
- A candidate cannot evade this comparison by changing the recorded ceiling
  or selecting an older predecessor; advancing the accepted result triggers
  a fresh comparison before acceptance.
- Wrong-regime, partial, conditional, shadowed, or universe-restricted results
  cannot substitute for the required canonical theorem.
- Missing comparison proofs, forbidden axioms, and canonical-file changes
  fail the appropriate checks.
- README statement drift is detected and all advertised proof targets build.
- Integrating a contribution to one regime preserves the other regime and
  leaves one maintained formalization, with its history recorded.

## 8. Preserve attribution and honest historical records

Use `CONTRIBUTIONS.md` as the single readable contribution history. Initially,
it must contain **one contribution credited to Marcus Webb**, covering the
initial work on both regimes. Do not turn the two existing baseline JSON
records into two contributions or add an AI agent as a separate contributor.
Record the actual verification status and relevant dates truthfully; do not
backdate complete Lean verification to the earlier hybrid run.

This requested consolidation supersedes the old requirement to retain every
byte of the current ledger and its machine-readable registry in the active
tree. Preserve substantive attribution and historical facts in the rewritten
initial entry or a concise provenance note, with older detail available through
Git history. Later accepted changes add entries identifying the contributor,
affected regime, result or implementation change, explanation, attribution,
and actual commit/PR links when available. Maintain one implementation while
retaining credit for work it supersedes.

Preserve the historical account of preceding human mathematics, model
identities, tool roles, and Marcus Webb's responsibility from Section S2 and
`docs/PROVENANCE.md`, without treating that contextual attribution as additional
accepted repository contributions. Python's historical role remains a fact
after its certificate programs are removed. No prose proof needs to be copied
to preserve provenance.

Keep past dates, manifests, and timings distinct from new validation. Old
checker paths may be described as historical references resolved in the
corresponding Git revision; do not make current validation depend on their
continued existence. Preserve unresolved correctness, attribution, and novelty
issues until evidence resolves them. Follow `docs/RESEARCH_PROTOCOL.md` for
substantive proof work. Preserve `LICENSE`, `LICENSING.md`, and third-party
notices.

Do not invent paper publication metadata or release identifiers. There is an
existing inconsistency: introductory prose in `supplementary.tex` says the
paper is on arXiv, while the repository instructions and README say it is in
preparation with no public version. Do not propagate the unverified arXiv claim
when extracting the mathematical statement; resolve metadata using actual
evidence if needed.

## 9. Completion requirements and handoff

Deliver the restructured local source tree, a concise old-to-new migration
map, the updated contributor workflow, and evidence from the actual checks.
Report the precise theorem names, build command, validation results, and any
remaining limitations. Do not create or publish a PR without explicit prior
approval for that specific PR, and do not merge one.

The objective is complete only when all of the following hold:

- The canonical file is unchanged and protected in every AI instruction
  source and the trusted acceptance path.
- Both baseline propositions have complete Lean proofs with the prescribed
  universe generality and allowed axioms, with no external numerical premises.
- The Python certificate pipeline has been removed from the active tree and
  no verification or contributor path still depends on it.
- New proofs of either regime at constants componentwise no larger than the
  current accepted quartet, including equality in all four entries, have a
  working and tested route to update the single maintained formalization,
  subject to the maintainer's PR decision. No accepted improvement can be lost.
- README contains the natural-language theorem statement and the complete
  canonical Lean statement in an expandable section, accurately identifies
  the actual Lean proofs, and has working verification links.
- There are no maintained natural-language proofs or prose-proof submission
  routes. The supplement is clearly historical pending later deletion.
- The structure is simple, and the Markdown history initially contains one
  contribution credited to Marcus Webb, with accurate provenance.
- The configured build, contribution checks, audits, and documentation agree;
  attribution, licensing, dependency pins, and external storage rules survive.

