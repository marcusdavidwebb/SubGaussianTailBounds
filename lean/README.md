# Checking the Lean proof

From the repository root:

```sh
./lean/check-statements.sh
./lean/verify.sh
```

Both commands perform setup internally, build the needed modules and check the
same two exact propositions for arbitrary sample-space universes. The focused
command audits the two results and their transitive axioms, trusting compiled
imports. The full command also builds and independently replays every maintained
proof module through Lean's kernel, checks source coverage and binds the report
to unchanged source/artifact inputs. There is no separate accepted checkout or
constants-comparison interface. Marcus reviews coefficient and policy changes.

## Existing environment and storage

The pinned environment is Lean **4.33.1**, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, NLA-lib
`6491e7528c1b1e68e46301cde6a76ae153e8e834`, and the exact transitive revisions in
[lake-manifest.json](lake-manifest.json). Check installed toolchains with
`~/.elan/bin/elan toolchain list`; setup reuses existing installations and reports
missing or incompatible dependencies without downloading or replacing them.

This checkout's default external workspace is
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/nla-4.33.1/`. It holds resolved Lake
configuration/manifest, `.lake/packages/`, `.lake/build/`, generated auditors and
logs. `MATHLIB_CACHE_DIR` defaults to `~/Library/Caches/mathlib` on macOS. The
older `~/Lean/SingularValueBounds/` Lean 4.19.0 project is separate and untouched.
Do not place dependencies, caches or compiled outputs in this checkout or OneDrive.

| Variable | Purpose |
|---|---|
| `SVB_WORK_DIR` | Absolute external workspace owned by this checkout |
| `SVB_PACKAGES_DIR` | Existing packages at the exact pinned revisions |
| `SVB_ELAN_BIN` | Existing Elan executable; defaults to `~/.elan/bin/elan` |
| `SVB_BUILD_JOBS` | Concurrent module builds; default 1 |
| `SVB_REPLAY_JOBS` | Concurrent independent kernel workers; default 1 |
| `MATHLIB_CACHE_DIR` | External Mathlib download cache |

Choose concurrency to fit available memory. Both commands use the same bounded
build scheduler because this pinned Lake version provides no compiler-process
concurrency limit. Current project artifacts can be reused after Lake checks
source traces; full kernel replay always runs afresh. Measurements distinguish
project-clean builds with existing dependency artifacts from incremental checks.
See [performance](../docs/PERFORMANCE.md).

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
