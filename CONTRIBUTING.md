# Contributing

This project maintains one Lean formalization of the two propositions in
[MainTheoremStatement.lean](MainTheoremStatement.lean). A contribution may
replace the proof of either regime, including at unchanged constants. Marcus
Webb decides whether to accept every proposal; passing verification establishes
mathematical eligibility, not automatic acceptance.

## Mathematical contract

Prove the relevant canonical proposition at one exact quartet `(α, β, γ, δ)`:

```lean
SubGaussian.GeneralSingularValueTailBound.{u} α β γ δ
SubGaussian.UnitSingularValueTailBound.{u} α β γ δ
```

A submission can concern either regime alone. Preserve the arbitrary sample-space
universe `u`, every hypothesis, positivity, both non-strict events, endpoints,
measurability and `ℝ≥0∞` probability bounds. No finite certificate or analytic
premise may remain unproved. Constants may be exact Lean expressions;
there is no separate JSON arithmetic format.

Prove all four componentwise comparisons in Lean against both ceilings:

| Regime | Permanent original ceilings | Additional ceiling |
|---|---|---|
| General | `(3.84, 1.58, 2.35, 1.5)` | Its trusted current accepted quartet |
| Unit | `(1.32, 1.12, 2.32, Real.sqrt 2)` | Its trusted current accepted quartet |

**No current constant may increase.** All comparisons apply simultaneously to
the same proved quartet. Equality in any or all entries is eligible; strict
improvement, a speedup or a shorter proof is not required. Keep the two regimes
separate and preserve the other regime when changing one. Do not combine
coordinates from different results without a proof of the joint quartet.

For example, after accepting general constants `(3.70, 1.58, 2.35, 1.5)`, a
proposal at `(3.70, 1.55, 2.35, 1.5)` meets the numerical policy. A proposal at
`(3.75, 1.55, 2.35, 1.5)` fails because it increases the first component. These
examples assert no mathematical improvement. Editing recorded ceilings or
selecting an older predecessor cannot authorize a regression. The maintainer's
local Lean verification compares against the current accepted target branch and
must be repeated if the candidate or accepted base changes.

## Edit the maintained proof

The root canonical file is immutable: do not edit, delete, rename, move,
replace or shadow `MainTheoremStatement.lean`, including its comments and
imports. Put proofs and adapters in other modules that import the actual root
source. Report any mathematical or compatibility problem without changing the
statement. The README's full presentation is checked against the root bytes.

Edit [lean/SingularValueBounds/](lean/SingularValueBounds/). The public interface
is [Canonical/Results.lean](lean/SingularValueBounds/Canonical/Results.lean),
under `SubGaussian.Current`. It exposes the jointly proved constants, both
current results, their baseline corollaries, and comparisons. The small
[AcceptedConstants.lean](lean/SingularValueBounds/Canonical/AcceptedConstants.lean)
records the exact proposed quartets; its equality with the proved constants is
itself a Lean obligation. The trusted base supplies the comparison ceilings,
independently of the proposed snapshot.

Keep this small snapshot declarative and deterministic: ordinary exact Lean
expressions and local helper definitions are supported, including functions such
as `Real.sqrt` and `Real.log`. Put tactics and proof development in the proof
modules. The trusted snapshot syntax guard rejects metaprogramming and scope
escapes, so an accepted quartet cannot change when it becomes the next base.
See [the snapshot interface](docs/CI.md#lean-interface) for its supported forms.

For an equal-constant general replacement, update its supporting proof and keep
this public target proved, while retaining the unit declarations:

```lean
universe u
example : SubGaussian.GeneralSingularValueTailBound.{u}
    SubGaussian.Current.generalAlpha SubGaussian.Current.generalBeta
    SubGaussian.Current.generalGamma SubGaussian.Current.generalDelta :=
  SubGaussian.Current.general.{u}
```

For an improvement, also update that regime's snapshot and prove each
`general_baseline_alpha`, `general_current_alpha`, etc. comparison against its
original and trusted current ceilings. Use the corresponding `unit_*` names
for the unit regime. See the complete [22-declaration interface](docs/CI.md#lean-interface).
The baseline corollaries may use the componentwise monotonicity lemmas in
[Canonical/Monotonicity.lean](lean/SingularValueBounds/Canonical/Monotonicity.lean).

A different proof architecture is welcome. Supporting modules may be edited,
added or removed; their historical names are not acceptance targets. Update the
umbrella imports when changing modules. Remove superseded independent
implementations after their replacements are verified, retaining credit in
[CONTRIBUTIONS.md](CONTRIBUTIONS.md) and earlier sources in Git history.

## Submit and verify

A complete submission contains:

1. Lean proof sources, the affected regime and exact quartet, and the checked
   public result, comparison and snapshot-equality declarations.
2. Concise explanation of the change, relevant declarations, reuse and
   attribution, including computational or AI assistance where applicable.
3. An entry in [CONTRIBUTIONS.md](CONTRIBUTIONS.md), with actual PR or commit
   links when available.

Do not submit a separate natural-language proof, PDF proof or Python certificate
package. Ordinary useful Lean comments and documentation remain welcome. The
historical supplement is not maintained with future Lean contributions.

With the [pinned external setup](lean/README.md), run from the repository root:

```sh
./lean/verify.sh
```

This compiles the actual protected statement and the single maintained
formalization, checks both regimes and all comparisons, and audits their full
logical dependencies. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed. `sorry`, `admit`, new axioms, native-oracle facts and assumed numerical
certificates are ineligible. Source hashes and administrative Python never
establish a mathematical claim. See [current validation](docs/MIGRATION.md).

A local self-comparison is a preflight. Before merging, Marcus Webb checks out
the PR branch and runs the complete Lean verification locally, using a separate
existing checkout of the current accepted base for comparison:

```sh
SVB_TRUSTED_ROOT="/absolute/path/to/accepted-checkout" ./lean/verify.sh
```

Record the candidate and accepted-base commit IDs, the command and its completed
log. Repeat the check if either revision changes. Candidate code executed locally
has the local user's permissions; review changes to the verification setup before
running it. The [manual verification procedure](docs/CI.md#manual-verification-before-merge)
also explains the initial trusted-policy transition.

GitHub CI runs source-integrity, contribution-history and administrative checks.
It does not install Lean, compile proofs or replay the kernel. **A green
`CI required` status is not evidence that the Lean proof passed.** Complete
local mathematical verification remains required before merge. Candidate
workflow edits do not change the trusted-base workflow already checking a PR.

There is no maintenance exemption from complete mathematical verification or
from the no-increase rule. Marcus Webb retains review discretion. Agents must
not publish a PR without explicit approval for that specific PR, or merge or
enable automatic merging on the maintainer's behalf.

## Credit and research

Preserve substantive credit in the single Markdown history, including when work
is superseded. Its initial entry credits Marcus Webb for both regimes; the
preceding human mathematics and tool roles remain in
[PROVENANCE.md](docs/PROVENANCE.md). Mathematical credit and future paper
authorship are separate decisions.

Follow [RESEARCH_PROTOCOL.md](docs/RESEARCH_PROTOCOL.md) for substantive
mathematics. Distinguish correctness, attribution and novelty, and retain
unresolved assessments. Questions, numerical exploration and literature
pointers can be discussed in issues; an issue is not an accepted theorem.

Keep dependency pins unchanged and toolchains, dependencies, caches and build
outputs outside the source checkout. Contributions use the [MIT License](LICENSE)
unless explicitly agreed otherwise by the maintainer; preserve third-party
terms and notices as described in [LICENSING.md](LICENSING.md).
