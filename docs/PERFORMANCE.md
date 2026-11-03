# Proof structure and checking costs

This records the 3 November 2026 structural-certificate simplification. Its
baseline is the actual starting commit `57dd34d2754d24eb5b60f857f418ae0111174d40`,
whose working tree was clean. The two required results remain exactly general
`(3.84, 1.58, 2.35, 1.50)` and unit `(1.32, 1.12, 2.32, 1.42)`, for arbitrary
sample-space universes.

## Work eliminated

The dominant general entropy blocks were spending their time on a redundant
order proof, rather than the rational/logarithmic inequalities. After
`simp only [List.forall_mem_cons]`, the generated proof retained a universally
quantified empty-list tail over `Fin 121 × Fin 121`. `decide +kernel` enumerated
all 14,641 pairs for that vacuous tail, once in each of 1,331 numerical rows.
A representative block's profiler attributed about 125 of 135 elaboration
seconds to the numerical-assembly declarations.

`GeneralMeanPartition.ordered` now derives strict order structurally from the
partition's existing conjuncts. The assembly lemma no longer requests a second
order proof. Generated final-node proofs also reuse `generalMeanGrid_last`
instead of repeating `norm_num`. All 1,331 rows, 6,267 nodes, 4,936 intervals and
exact witness values are unchanged; no inequality or required coefficient is
weakened. The generator retains the same exact numerical calculation and search.

The rational definitions and sufficient-condition structure move unchanged to
`GeneralMeanNumericalData.lean`. Finite certificates can import them without the
probability/matrix arguments that interpret them. The remaining analytic proofs
are unchanged. This adds one maintained module, included in both the complete
build and independent replay. No work is exempted from verification.

The root statement, canonical constants, toolchain, dependency pins and imported
mathematical definitions are unchanged. The root SHA-256 remains
`1ae54907833fdcf4e1dff8dcd579a9cea0c3db578d9417e7d6331513db6bd84c`.
No statement-equivalence migration is needed.

## Controlled whole-project comparison

The starting checked-input inventory matched the latest successful verification
exactly: `a34f7c69faed51ba6247c7771f03b810473ab9b5f43020a1cb972163d9c84b32`.
It differed in seven files from the older 2 November performance inventory, so
those timings were not reused as the baseline. Both columns below are fresh
measurements of the actual starting and retained implementations.

Machine: Apple M3 Ultra, 32 CPU cores, 512 GiB RAM, arm64 macOS26.6.2. Both use
Lean4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and NLA-lib
`6491e7528c1b1e68e46301cde6a76ae153e8e834`. Concurrency is matched: 24 module
workers, project compiler `-j2`, 24 replay workers, and the same original module scheduler.
There were no competing proof-development processes. Existing pinned dependency
artifacts and OS file caches were reused; no system cache was cleared. Each clean
build used a fresh project workspace with no project build artifacts. The other
measurements started with current compiled project artifacts. Full verification
always performed fresh independent kernel replay.
The baseline uses its frozen source archive and the retained run uses the actual
checkout; both source trees and their separate build workspaces share one filesystem.

Times are seconds. Clean/full rows are single complete runs; short rows report
the median and range of three complete trials. User/system CPU sums include child
processes. RSS is the maximum child-process RSS from `/usr/bin/time -l`, **not**
aggregate concurrent memory.

| Phase | Before wall | Retained wall |
| --- | ---: | ---: |
| Project-clean build | 1,047.43 | 890.64 |
| Full independent verification | 959.82 | 715.04 |
| Focused check, interleaved median (range) | 109.09 (87.79–112.24) | 108.26 (99.95–126.06) |
| All-current build, interleaved median (range) | 9.28 (9.23–9.71) | 8.26 (8.08–8.47) |

| Phase | Before user / system | Retained user / system | Before / retained max child RSS |
| --- | ---: | ---: | ---: |
| Project-clean build | 11,881.67 / 4,067.58 | 8,026.92 / 4,336.59 | 6.91 / 6.91 GiB |
| Full independent verification | 8,349.98 / 2,273.00 | 4,453.37 / 2,174.45 | 8.21 / 8.21 GiB |

Clean wall time falls 15.0% and total CPU 22.5%; full wall time falls 25.5% and
total CPU 37.6%. Clean-build system CPU rises 6.6%, for an unresolved reason.
That increase is included in the total-CPU comparison: the retained change still
saves 3,585.74 CPU seconds and 156.79 wall seconds in a clean build, simplifies
the proof, and adds no scheduling or checking machinery. Peak child RSS does not
materially improve. These are complete-run measurements, not projections from
the block pilot.

During the controlled clean runs, the nineteen general entropy blocks go from
153.4–324.7 to 33.3–61.2 seconds; their independent replays go from 147.8–295.4 to
22.3–37.0 seconds. The remaining longest clean-build jobs are unchanged majorant
and endpoint certificates: majorant Row3 takes 255.7 versus 256.8 seconds and
endpoint analytic Block02 takes 190.2 versus 195.7 seconds. Both completion paths
end through the unit endpoint proof. Its former 154.49-second build-slot wait
disappears, but substantial early spectral-path waits remain. Read-only inspection
found no analogous vacuous-quantifier defect in those two remaining certificates;
finer arithmetic-cost attribution would require further profiling.

The short rows use three additional interleaved before/retained pairs, with order
reversed in the middle pair under one launcher. Initial post-full-verification
trials gave focused medians 100.33 versus 71.88 seconds (ranges 97.13–108.73 and
71.51–112.94), and unchanged-build medians 10.99 versus 12.62 seconds (ranges
10.46–11.39 and 12.60–12.88). The unchanged-build difference reverses in the
interleaved repeats, and focused medians are then nearly equal. No reliable
focused/startup improvement is claimed; no speculative checker change was kept.

The import split lowers memory for representative certificate blocks, but not
the whole-workflow peak. Separate production inventory and planning probes peak
at 6.64 and 4.59 GiB; neither reproduces the full workflow's 8.21 GiB maximum.
Its exact subprocess attribution remains unresolved. These isolated diagnostics
do not measure every concurrent worker, and their JSON outputs were not fed into
verification.

## Supporting experiments and limitations

With one compiler process and `-j2`, the representative original block took
148.75 seconds wall / 142.89 user / 2.99 system. An explicit-constructor pilot took
18.68 / 14.32 / 2.32 seconds, with the numerical arithmetic and imports otherwise
unchanged. The integrated assembly helper and representative block were separately
compiled and independently replayed; both public target closures then passed the
focused check. The final whole-project measurements include all supporting work.

Three paired import-split trials reduced median block compilation from 16.65 to
15.91 seconds and maximum RSS from about 3.03 to 2.50 GiB. The probe's loaded environment
shrinks from 4,739 to 3,752 modules, including one probe module in both counts
(project modules 50 to 22). Separate replay
checks include the new interface, assembly lemma, integer resolvent bridge and
representative block. Broad standalone replay pilots had large cache/loading
differences; their wall times and RSS are not estimates of the production full
workflow.

A shared-Lake batch experiment improved a matched 19-sibling rebuild from 97.58
to 80.42 seconds, but a complete clean build of the revised proof and import split
with the large-batch scheduler took 1,426.87 seconds. Whole-batch
barriers delayed unrelated dependency chains; the change was rejected. The final
scheduler is byte-identical to the starting implementation. Hash-set/axiom-scan
and thread-count experiments also produced no reliable benefit and were rejected.

Focused-check profiling located substantial variability in imports and startup.
In the actual workflow, fresh expected-type compilation took 19–27 seconds and
auditor import took about 20 seconds; warm standalone imports took 4.3–4.5 seconds.
The same axiom scan remained near seven seconds. Explicit `-j2` did not improve
the auditor or expected-type compiler. Identical import paths and low hard-page-
fault counts in some slow runs do not establish a simple cold-cache explanation.
The context-dependent startup cause remains unresolved; isolated timings are not
substituted for the complete focused-command measurements above.

## Validation and retained records

Both focused and full commands pass the exact general and unit propositions,
including arbitrary sample-space universes. Full verification passes all 340
independent replays (339 maintained project modules plus the expected
specification), source coverage, and the complete axiom audit. The report contains
51,798 theorem targets and 114,943 visited constants, and only `propext`,
`Classical.choice` and `Quot.sound`. Fewer generated auxiliary theorems are needed;
no maintained source is omitted.

All nine final workflow tests pass with real Lean/Lake enabled. They reject wrong
types/constants, restricted universes, extra assumptions, forbidden axioms,
forged compiled proofs, native-computation assumptions, altered artifacts and
omitted sources, and exercise actual Lake invalidation. All three exact-arithmetic
generator checks, theorem-presentation synchronization and contribution checks pass.

The checked-input SHA-256 for the retained sources is
`2e69d0aeba9ede9dbea4ac3af32898125ddc71c8c819a3912549de3ca39578f4`.
The scheduler, verifier, replay worker, exact-type/universe and axiom policies,
source coverage checks, input-identity checks, regression tests and lightweight
CI are unchanged. The README, TeX and PDF presentations are unaffected; the
README/TeX source-synchronization checks pass.

All logs, source/input snapshots, conditions and pilots are retained outside the
checkout under
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/simplification-20261103/`.
Primary logs are `before-clean-build.log`, `before-full.log`,
`before-{focused,incremental}-{1,2,3}.log`, and their `retained-` counterparts.
`paired-{before,retained}-{focused,incremental}-{1,2,3}.log` records the interleaved
short repeats. `retained-regressions.log` and `retained-administrative.log` record
the final tests. `critical-path-analysis.{json,txt}` records the timing
reconstruction. `after-clean-build.log` is the rejected large-batch experiment, **not**
the retained result; its launcher was stopped after the completed build, before
unnecessary verification of that rejected scheduler. `focused-startup/summary.txt`
records the additional startup diagnostics. No dependencies or toolchains were
installed or changed.
`retained-{inventory,plan}-diagnostic.log` records the separate memory probes.

The preceding mathematical refactor and its historical validation remain credited
in [CONTRIBUTIONS.md](../CONTRIBUTIONS.md). Its complete performance record is
preserved in Git at `57dd34d:docs/PERFORMANCE.md`. The historical 2 November after
times were 1,007.42 seconds clean, 900.24 full, 44.50 focused and 19.58 incremental,
with 8.21 GiB maximum child RSS during full verification, for checked-input SHA-256
`e2c09bf86f31fd4aefde283083012a2da9c4e5c93b5a0f51ae54f86aba33dc98`.
Those earlier improvements are not attributed to this change.
