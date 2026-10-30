# Running the Lean proof

Run the complete check from the repository root:

```sh
./lean/verify.sh
```

It configures the external workspace, builds the actual immutable root statement
and maintained proofs, independently replays every module through Lean's kernel,
and checks all canonical types, comparisons, universes and allowed axioms.
[Verification and review](../docs/VERIFICATION.md) explains the full contract.
For a PR review, pass the accepted checkout with `SVB_TRUSTED_ROOT` as described
there. GitHub CI performs administrative checks only.

The two starting points for reading the mathematics are the immutable
[root statement](../MainTheoremStatement.lean) and the public
[results](SingularValueBounds/Canonical/Results.lean). The
[repository map](../REPOSITORY_MAP.md) explains every supporting folder and tool.

The NLA-lib migration on 30 October 2026 compiled all 530 Lean source modules
with Lean 4.33.1, including both sharp canonical theorems and the equivalences
with the preceding statement. The 22 generated canonical acceptance obligations
also compiled and passed their supplemental axiom audit. Marcus Webb explicitly
deferred independent kernel replay, so this is not a completed verification run.
The complete requirements above remain in place;
[HISTORY.md](../docs/HISTORY.md) records the checks performed.

## Pinned environment and storage

Reuse Lean **4.33.1** and the exact dependency revisions in
[lake-manifest.json](lake-manifest.json): Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`, and
[NLA-lib](https://github.com/NLA-lib/NLAlib/tree/6491e7528c1b1e68e46301cde6a76ae153e8e834)
to `6491e7528c1b1e68e46301cde6a76ae153e8e834`. These versions were installed
centrally for the explicitly requested NLA-lib imports. Check the central
installation before running a command that could otherwise download a toolchain:

```sh
"$HOME/.elan/bin/elan" toolchain list
```

The list must include `leanprover/lean4:v4.33.1`. The verifier reports missing or
incompatible dependencies; ordinary local verification does not install, clone,
fetch or upgrade them.

The default setup uses:

- Elan in `~/.elan`.
- This checkout's own build workspace at
  `~/Lean/SubGaussianTailBounds/<source-path-digest>/nla-4.33.1/`.
- All pinned dependencies in that external workspace's `.lake/packages/`,
  including `NLAlib/` and `mathlib/`; build outputs in `.lake/build/`.
- The Mathlib download cache at `~/Library/Caches/mathlib` on macOS.

For the current checkout, the workspace is
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/nla-4.33.1/`; NLA-lib is stored
under its `.lake/packages/NLAlib/`. The older Lean 4.19.0 dependency tree at
`~/Lean/SingularValueBounds/.lake/packages/` remains untouched and is not used
by this setup.

Keep dependencies, caches and compiled outputs outside this source checkout and
OneDrive. Do not reuse `SingularValueBounds/.lake/build/` for this project or
symlink bulky dependencies into the repository. Workspace ownership checks keep
different checkouts' build outputs separate. Lake's configuration and manifest
are resolved in that external workspace; this repository contains proof sources,
scripts and small configuration templates, with no local dependency tree.

| Environment variable | Override |
|---|---|
| `SVB_WORK_DIR` | Absolute external workspace belonging to this checkout |
| `SVB_PACKAGES_DIR` | Existing directory of exact pinned dependencies |
| `SVB_ELAN_BIN` | Existing Elan executable; defaults to central `~/.elan/bin/elan` |
| `MATHLIB_CACHE_DIR` | External Mathlib cache |
| `SVB_TRUSTED_ROOT` | Existing accepted-base checkout for policy and constants comparisons |
| `SVB_BUILD_JOBS` | Maximum concurrent module builds; defaults to 1 |
| `SVB_REPLAY_JOBS` | Maximum concurrent kernel replay workers; defaults to 1 |

Cold verification can take hours, and individual proof modules can use several
gigabytes of RAM. Increase parallelism only to fit the machine. Lake reuses
current compiled outputs after checking source-content traces; independent
kernel replay still runs afresh in dependency order. See
[recorded measurements](../docs/HISTORY.md) for observed costs.

## Proof layout

| Location | Role |
|---|---|
| [MainTheoremStatement.lean](../MainTheoremStatement.lean) | Actual immutable statement compiled from the repository root |
| [Canonical/Results.lean](SingularValueBounds/Canonical/Results.lean) | Public current results, baseline corollaries and comparisons |
| [Canonical/](SingularValueBounds/Canonical/) | Baseline proofs, adapters, NLA-lib equivalence bridges, monotonicity and accepted constants |
| [KL/](SingularValueBounds/KL/) | Analytic arguments and complete finite numerical proofs under `Certificates/` |

Proof changes and new constants follow [CONTRIBUTING.md](../CONTRIBUTING.md).

`SingularValueTails` requires `IsProbabilityMeasure μ` and states its bounds
as real-valued inequalities using `ENNReal.toReal`. Its probability-measure
instance implies finiteness; no separate finite-measure hypothesis is required.
The preceding extended-nonnegative-real inequalities are equivalent under this
instance by [TailEquivalence.lean](SingularValueBounds/Canonical/TailEquivalence.lean).
The migration compilation described above predates this revision and is not
evidence that the revised sources have passed the complete verifier.

The root statement imports NLA-lib's `IsSubgaussianVector` and `singularValues`;
the pinned sub-Gaussian module supplies `IsIsotropic` transitively. Its
sub-Gaussian argument is the variance proxy `K²`; row measurability remains
explicit. The tail helper takes no dimension proof, but both theorem statements
retain the `1 ≤ n` hypothesis. The bridges in
[NLARows.lean](SingularValueBounds/Canonical/NLARows.lean),
[NLASingularValues.lean](SingularValueBounds/Canonical/NLASingularValues.lean)
and [StatementEquivalence.lean](SingularValueBounds/Canonical/StatementEquivalence.lean)
connect these imports to the preceding expanded propositions, retaining both
sharp regimes, non-strict measurable tail events and arbitrary sample-space
universes.

## Verification tools

[verify.sh](verify.sh) is the full entry point. [setup.sh](setup.sh) calls
[scripts/configure_lean.py](../scripts/configure_lean.py) to resolve the existing
environment; setup alone does not check proofs. All six operational Python
helpers live in [scripts/](../scripts/).

[Verification/](Verification/) contains the Lean import parser, constants-source
guard, independent kernel worker and two audit templates. The generator fills
those templates in the external workspace. Keep these checking programs separate
from the mathematical library under `SingularValueBounds/`.

The Python [regression tests](../tests/) exercise the verification tools. Their
optional Lean fixtures use small example modules; the full proof check remains
`./lean/verify.sh`. Python does not supply mathematical certificates.
