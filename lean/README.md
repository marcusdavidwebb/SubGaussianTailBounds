# Running the Lean proof

To check just the two displayed statements, run from the repository root:

```sh
./lean/check-statements.sh
```

This builds the required proof dependency closure, checks the two exact,
universe-polymorphic propositions and audits their proof dependencies for
allowed axioms. It trusts imported compiled artifacts and elaborators; it does
not independently replay every module or protect its expected types against
hostile imported syntax. It also omits contribution-policy comparisons and
source-coverage checks.

For the complete check, run:

```sh
./lean/verify.sh
```

This builds the actual root statement and all maintained proofs, independently
replays every module through Lean's kernel, and checks exact types, constants,
universes and allowed axioms. Setup alone does not verify proofs. For PR review,
set `SVB_TRUSTED_ROOT` to a separate accepted checkout; self-comparison is only
preflight. [Verification and review](../docs/VERIFICATION.md) defines the complete
contract. GitHub CI performs administrative checks only.

The complete local self-check passed on **2 November 2026**, including independent
kernel replay of all 563 modules and all 22 acceptance targets, with exact-type,
universe, source-coverage and axiom audits. This was a self-comparison; verification
against a separate accepted base remains required before merging.

## Pinned environment and storage

Reuse Lean **4.33.1** and the exact dependency revisions in
[lake-manifest.json](lake-manifest.json): Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`, and
[NLA-lib](https://github.com/NLA-lib/NLAlib/tree/6491e7528c1b1e68e46301cde6a76ae153e8e834)
to `6491e7528c1b1e68e46301cde6a76ae153e8e834`. Reuse the central Elan installation
in `~/.elan`; check installed toolchains before invoking Lean:

```sh
"$HOME/.elan/bin/elan" toolchain list
```

The list must include `leanprover/lean4:v4.33.1`. Missing or incompatible
dependencies are reported; routine verification never installs, clones, fetches
or upgrades them.

Each checkout owns an external workspace at
`~/Lean/SubGaussianTailBounds/<source-path-digest>/nla-4.33.1/`
(`0ad011255e709e4d` for this checkout). It contains the resolved Lake configuration
and manifest, pinned `.lake/packages/mathlib/` and `.lake/packages/NLAlib/`,
generated checking modules, logs and `.lake/build/` outputs. Use
`~/Library/Caches/mathlib` for `MATHLIB_CACHE_DIR` on macOS.

Keep dependencies, caches and compiled outputs outside this source checkout and
OneDrive. Do not reuse `SingularValueBounds/.lake/build/` for this project or
symlink bulky dependencies into the repository. The older Lean 4.19.0 dependency
tree at `~/Lean/SingularValueBounds/.lake/packages/` is incompatible with these
pins and remains untouched. Workspace ownership checks keep build outputs
separate for different checkouts.

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

## Source layout

| Location | Role |
|---|---|
| [Root statement](../MainTheoremStatement.lean) → [Canonical/Results.lean](SingularValueBounds/Canonical/Results.lean) | Authoritative propositions and complete public results; follow their imports into the proofs |
| [Canonical/](SingularValueBounds/Canonical/) | Baseline proofs, NLA-lib equivalence bridges, adapters, monotonicity and accepted constants |
| [KL/](SingularValueBounds/KL/) | Barrier/row analysis and exact finite proofs in `Certificates/`; row/block modules bound memory use and share computations |
| Other [SingularValueBounds/](SingularValueBounds/) folders | Shared scalar, spectral, matrix, concentration and quadratic-form mathematics |
| [SingularValueBounds.lean](SingularValueBounds.lean) | Umbrella importing every maintained mathematical module for verification coverage |
| [scripts/](../scripts/) and [Verification/](Verification/) | Python setup/scheduling/administration and Lean checking programs/templates; Python supplies no mathematical oracle |
| [tests/](../tests/) | Tool regression tests, including opt-in local Lean fixtures; separate from the complete verifier |

Preserve the root statement's exact bytes, name and location, including imports,
comments and universes. Never edit, delete, rename, relocate, replace or shadow it,
including for maintenance. Proof changes follow [CONTRIBUTING.md](../CONTRIBUTING.md).

[generate_theorem_tex.py](../scripts/generate_theorem_tex.py) and
[its regression test](../tests/test_theorem_tex.py) maintain the standalone
[TeX statement](../README.md#tex-statement) from the README and actual root source.
