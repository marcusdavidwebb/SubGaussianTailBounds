# Lean setup

Run the complete check from the repository root:

```sh
./lean/verify.sh
```

It configures the external workspace, builds the actual immutable root statement
and maintained proofs, independently replays every module through Lean's kernel,
and checks all canonical types, comparisons, universes and allowed axioms.
[Verification and review](../docs/VERIFICATION.md) explains the full contract.

## Pinned environment and storage

Reuse Lean **4.19.0** and the exact dependency revisions in
[lake-manifest.json](lake-manifest.json). Mathlib is pinned to
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Check the central installation before
running a command that could otherwise download a toolchain:

```sh
"$HOME/.elan/bin/elan" toolchain list
```

The list must include `leanprover/lean4:v4.19.0`. The verifier reports missing or
incompatible dependencies; ordinary local verification does not install, clone,
fetch or upgrade them.

The default setup uses:

- Elan in `~/.elan` and compatible pinned dependencies in
  `~/Lean/SingularValueBounds/.lake/packages/`.
- This checkout's own build workspace at
  `~/Lean/SubGaussianTailBounds/<source-path-digest>/`.
- The Mathlib download cache at `~/Library/Caches/mathlib` on macOS.

Keep dependencies, caches and compiled outputs outside this source checkout and
OneDrive. Do not reuse `SingularValueBounds/.lake/build/` for this project or
symlink bulky dependencies into the repository. Workspace ownership checks keep
different checkouts' build outputs separate. Lake's configuration and manifest
are resolved in that external workspace; proof sources remain here.

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
| [Canonical/](SingularValueBounds/Canonical/) | Baseline proofs, adapters, monotonicity and accepted constants |
| [KL/](SingularValueBounds/KL/) | Analytic arguments and complete finite numerical proofs under `Certificates/` |

Proof changes and new constants follow [CONTRIBUTING.md](../CONTRIBUTING.md).

`scripts/` and `tests/` support builds and independent Lean verification.
They do not supply mathematical certificates; all proof obligations are in Lean.
