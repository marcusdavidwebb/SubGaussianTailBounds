# Checking the Lean proof

## First-time setup and Lake build

Install [Elan](https://github.com/leanprover/elan), Git and ensure that `lake`
is on your `PATH`. From a fresh checkout, run:

```sh
lake exe cache get
lake build
```

Elan selects Lean **4.33.1** from [lean-toolchain](../lean-toolchain), installing
it if necessary. Lake obtains the revisions in [lake-manifest.json](../lake-manifest.json)
and matching Mathlib build artifacts. Network access is required for this first
setup. The conventional root project stores dependencies and compiled project
outputs in `.lake` inside the checkout; other dependencies and project modules
may still need compilation. Mathlib normally stores its download cache in
`$XDG_CACHE_HOME/mathlib` or `~/.cache/mathlib`; set `MATHLIB_CACHE_DIR` to use
another external directory.

[CheckStatements.lean](SingularValueBounds/CheckStatements.lean) displays the two
claims at their exact coefficients and applies `SubGaussian.Current.general.{u}`
and `SubGaussian.Current.unit.{u}`. Their proposition definitions are in the actual
[root statement](../MainTheoremStatement.lean). This module is the default Lake
target; `lake build SingularValueBounds.CheckStatements` selects it explicitly.
A Lake build can reuse existing
compiled artifacts and does not perform the independent audits below.

## Additional verification

From the repository root:

```sh
./lean/check-statements.sh
./lean/verify.sh
```

These scripts require Bash, Git, Python 3.11 or newer and `shasum`, plus the
existing external setup described below. Both build the needed modules and check the
same two exact propositions for arbitrary sample-space universes. The focused
command audits the two results and their transitive axioms, trusting compiled
imports. The full command also builds and independently replays every maintained
proof module through Lean's kernel, checks source coverage and binds the report
to unchanged source/artifact inputs. There is no separate accepted checkout or
constants-comparison interface. Marcus reviews coefficient and policy changes.

## Environment and storage

The pinned environment is Lean **4.33.1**, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, NLA-lib
`6491e7528c1b1e68e46301cde6a76ae153e8e834`, and the exact transitive revisions in
the [root manifest](../lake-manifest.json). For an external workspace, `setup.sh`
and the verification scripts reuse existing installations and report missing or
incompatible dependencies without downloading or replacing them. An explicitly
supplied `SVB_PACKAGES_DIR` must already contain the pinned packages. Lake's cache
retrieval and builds may write compiled artifacts into that directory, so use a
project-owned package directory rather than a dependency tree shared with another
project.

The default external workspace is
`~/Lean/SubGaussianTailBounds/<checkout-id>/nla-4.33.1/`, where the ID depends on
the checkout path. It holds resolved Lake
configuration/manifest, `.lake/packages/`, `.lake/build/` and generated auditors.
The verification setup defaults `MATHLIB_CACHE_DIR` to `~/Library/Caches/mathlib`
on macOS. The older `~/Lean/SingularValueBounds/` Lean 4.19.0 project is separate.
Use this external workspace if the checkout is on OneDrive or should contain no
dependencies or compiled artifacts. With existing compatible dependencies, Lake
can also be invoked there explicitly:

```sh
(
  cd "$(./lean/setup.sh)"
  lake build SingularValueBounds.CheckStatements
)
```

| Variable | Purpose |
|---|---|
| `SVB_WORK_DIR` | Absolute external workspace owned by this checkout |
| `SVB_PACKAGES_DIR` | Existing packages at the exact pinned revisions |
| `SVB_ELAN_BIN` | Existing Elan executable; defaults to `~/.elan/bin/elan` |
| `SVB_BUILD_JOBS` | Concurrent module builds; default 1 |
| `SVB_REPLAY_JOBS` | Concurrent independent kernel workers; default 1 |
| `MATHLIB_CACHE_DIR` | External Mathlib download cache |

Choose concurrency to fit available memory. Both verification scripts use the
same bounded build scheduler because this pinned Lake version provides no
compiler-process concurrency limit; a direct Lake build uses Lake's own scheduler.
That direct build can use substantial memory. From the repository root,
`SVB_BUILD_JOBS=1 ./lean/check-statements.sh` offers a bounded build and the
focused audit for limited-memory machines.
Current project artifacts can be reused after Lake checks source traces; full
kernel replay always runs afresh. Measurements distinguish
project-clean builds with existing dependency artifacts from incremental checks.

## Source layout

Start at [Canonical/Results.lean](SingularValueBounds/Canonical/Results.lean).
The root statement defines the propositions and
[Constants.lean](SingularValueBounds/Canonical/Constants.lean) supplies their exact
rational coefficients. `Canonical/` connects imported definitions to the proof;
`KL/Lower`, `KL/Upper` and `KL/Barrier` provide the scalar estimates and matrix
transfer. `KL/Certificates` contains exact finite data and checking lemmas.
Other folders supply shared scalar, matrix and concentration facts.

[SingularValueBounds.lean](SingularValueBounds.lean) imports all maintained
mathematical modules. `Verification/` and `scripts/` implement source enumeration,
bounded build scheduling and the independent kernel/type/axiom audits. Python
provides no mathematical oracle. Numerical generators propose exact witnesses;
the corresponding Lean modules establish the required bounds.

For documentation, `python3 scripts/generate_theorem_tex.py` combines the README
theorem with the actual root Lean source to generate TeX and PDF. It also refreshes
the README's Lean block and constants table. The root source is not hash-pinned;
`--check` detects drift without writing or compiling. See
[CONTRIBUTING.md](../CONTRIBUTING.md) for proof and review requirements.

To reproduce the generated numerical proof sources after editing their rational
input data, run the three `scripts/generate_*.py` proof generators (general mean,
endpoint entropy, polynomial certificates). Each supports `--check` for a read-only
consistency check; CI runs those checks. Lean, rather than the generators,
establishes their mathematical validity.
