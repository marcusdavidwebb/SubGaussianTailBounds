# Proof structure and checking costs

This records the 2 November 2026 refactor and its checked inputs. Subsequent
statement edits and removal of the fixed statement hash require fresh verification;
the measurements below are historical, not timings for the current checkout.

The two targets remain the exact general `(3.84, 1.58, 2.35, 1.50)` and unit
`(1.32, 1.12, 2.32, 1.42)` propositions for arbitrary sample-space universes.
The barrier/row argument remains. This refactor changes the sufficient numerical
bounds and their proof representation rather than reproducing old calculations.

## Mathematical changes

The general upper-mean error is convex and decreasing for `L ≥ 1`. A certified
chord bounds all intermediate values; the logarithmic/affine expression is
checked at its clipped exact critical point. An adaptive partition covers
`[1,4]`; monotonicity handles the remaining unbounded range. It uses 4,936
intervals and 6,267 nodes, replacing 159,720 intervals and 161,051 nodes. The
exponential uses Taylor order 24 and a proved geometric remainder, and the error is
rounded upward at six decimal places. The retained 18-term logarithm enclosure
is sufficient. All values are regenerated, with direct soundness proofs for the
shorter calculation; no equality to an order-80 calculation is required.

The endpoint proof replaces rectangular entropy sums with exact integrals
on selected rate intervals. For the existing exponential resolvent `R`,

```math
F(c,q,u)=\frac{2}{q}e^{-qu/2}
  \left(1+\log(u/c)+R(qu/2)\right).
```

The integral of `(1 + log(u/c)) exp(−qu/2)` over a finite interval is
`F(start) − F(stop)`. Weighted sums of these integrals bound the survival entropy
integral. Shared lemmas prove the identity, nonnegativity, finite-list assembly
and the infinite tail.
Rational enclosures use the order-24 exponential and existing rational resolvent
bounds. A zero lower primitive beyond `qu/2 ≥ 24` avoids unnecessary positive
exponential work. Polynomial positivity slack permits larger intermediate entropy
allowances and coarser rate partitions. These are intermediate witnesses, not
changes to the required coefficients. The joint rate partitions shrink from
60,352 intervals to 4,502, and the small-parameter partition from 513 to 100.
Lean checks all 3,398 entropy inequalities and 837 updated polynomial certificates.
The old 8,000-point entropy grid and 888,000-state decay-prefix calculation are
removed. Only 2,111 lower and 932 upper logarithm values are retained.

Polynomial certificates store only their polynomial coefficients and compute
affine/Bernstein transforms in Lean instead of carrying three large intermediate
matrices per box. An exact rational generator derives the coefficients from the
actual cell data and proved identities. Six endpoint rows share a module, reducing
repeated compiler/kernel import overhead. Smaller sources alone do not establish
a speed improvement: pilots found a CPU tradeoff from recomputing transforms,
which must be included in complete-run measurements.

The pinned NLA-lib singular-value theorem was inspected at revision
`6491e7528c1b1e68e46301cde6a76ae153e8e834`,
[`ExtremeSingularValues.lean`, lines 439–486](https://github.com/NLA-lib/NLAlib/blob/6491e7528c1b1e68e46301cde6a76ae153e8e834/NLAlib/RandomMatrix/SubGaussian/ExtremeSingularValues.lean).
It assumes independent isotropic sub-Gaussian rows but gives displacement
`24c(√n+t)` and probability `2exp(−t²)`. Here its variance proxy would be `c=K²`;
the leading dimension coefficient alone prevents deriving the required targets
for arbitrary dimensions. No replacement theorem from that file is used.

## Statement and environment

The supplied root source did not parse. Its only edits remove two unmatched
closing parentheses and put a space before each exponential argument. The observed
source SHA-256 changes from
`54bd00eaf5dd251b40f6abe229fa2daaedaccf2df65b9ae72a91336d863dd9c8`
to `8febdb5f8bff85c42f8270f86dae261225247d75c40a80ca9edcfa0fef602178`.
The expressions, hypotheses, dimensions and endpoints are preserved. The old
adapter also used the wrong isotropy/sub-Gaussian argument order and expected
measurability fields no longer present in the root helper. Its repaired
bidirectional equivalences derive event measurability from measurable rows.
The benchmark baseline includes these compatibility repairs.

No toolchain, dependency revision or imported NLA-lib definition is changed: Lean4.33.1,
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and NLA-lib
`6491e7528c1b1e68e46301cde6a76ae153e8e834`. The quartets now have one authoritative
exact rational source. The obsolete accepted-constants snapshots and 22-target
comparison protocol are removed; both local modes share the two actual targets.
Full verification retains independent replay, exact types/universes, allowed
axioms, source coverage and checked-input identity, and now replays the root and
coefficient specification as project modules too.

## Measurement conditions

Machine: Apple M3 Ultra, 32 CPU cores, 512 GiB RAM, arm64 macOS26.6.2. Lean4.33.1
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, release build. Sources, pinned
dependency artifacts, project outputs and logs are on the same machine; all build
outputs stay in isolated project workspaces under `~/Lean/`. Dependency artifacts
and the operating-system file cache are reused; no dependency or system cache is
cleared. A project-clean build has no project `.lake/build/` artifacts.

Exploratory pilots and the initial baseline build ran alongside development
processes and are labelled contended. They are not the controlled before/after
comparison. The external directory
`~/Lean/SubGaussianTailBounds/0ad011255e709e4d/simplification-20261102/` retains the
repaired old source snapshot, pilot measurements, verifier-regression summary
and build logs. Controlled measurements use 24 module workers, compiler
`-j2`, and 24 replay workers, without concurrent proof-development processes.
Wall/user/system times and maximum child-process RSS come from `/usr/bin/time -l`;
that RSS is not the aggregate memory of all concurrent workers.

## Controlled results

All times are seconds. Each column is one complete successful run; these are not
repeated-trial estimates. CPU time is the sum over child processes. The clean
builds reuse pinned dependency artifacts, and the other rows start with current
compiled project artifacts. Full verification performs a fresh independent
kernel replay in both runs.

| Phase | Before wall | After wall | Before user / system | After user / system |
| --- | ---: | ---: | ---: | ---: |
| Project-clean build | 1,427.43 | 1,007.42 | 18,192.87 / 5,147.98 | 11,515.78 / 4,285.64 |
| All-current incremental build | 13.43 | 19.58 | 3.15 / 6.60 | 3.18 / 9.89 |
| Focused result check | 28.66 | 44.50 | 11.75 / 6.90 | 12.37 / 12.93 |
| Full local verification | 1,314.54 | 900.24 | 13,875.23 / 3,320.86 | 8,149.81 / 2,223.08 |

The project-clean build is 29.4% faster, and the full workflow is 31.5% faster.
Their total CPU times fall by 32.3% and 39.7%, respectively. The replay plus
complete-audit phase takes about 1,225 seconds before and 878 seconds after.
The former is reconstructed from the running process timer and final log time
(one-second resolution); the latter is reported by the verification script.
The full-workflow numbers are not cold build measurements.

The focused and all-current build measurements regress. The focused check now
separately compiles its protected expected specification and audits exact types,
arbitrary universes and actual proof dependencies. Source/input checks and Lake
startup also contribute to short runs. The scheduler's stale-target selection
avoids launching a Lake process for every cached module after an edit, but that
does not imply a faster all-current run.

Maximum child-process RSS increases from 6.26 to 6.91 GiB for the clean build,
from 6.64 to 8.21 GiB for full verification, and from 4.14 to 4.92 GiB for the
focused check. These measurements do not estimate aggregate concurrent memory.
The largest remaining jobs are the nineteen large general entropy row blocks: roughly
270–313 seconds per block during these concurrent runs. Their rational/logarithm
inequalities and proof reduction dominate despite the much smaller partition.
The retained barrier argument still needs these finite bounds; a different
mathematical argument could remove more work. Computing polynomial transforms
inside Lean saves duplicate data but adds some reduction work.

| Maintained project material | Before | After |
| --- | ---: | ---: |
| Compiled modules, including root and umbrella | 563 | 338 |
| Proof-submodule source bytes | 63,925,993 | 19,850,110 |
| Project `.olean` bytes | 959,075,160 | 624,532,432 |

Proof sources shrink by 68.9% and `.olean` artifacts by 34.9%. The obsolete
critical-log/decay caches, endpoint grid/prefix families and duplicate polynomial
matrices are gone. Generators use exact arithmetic and reproduce the retained
witnesses; their output is still checked by Lean.

## Final validation

The final focused check passes both exact propositions. Full verification passes
all 339 replays (338 project modules plus the independent expected specification),
source coverage and the axiom audit, which reports only `propext`,
`Classical.choice` and `Quot.sound`. Both successful modes identify their inputs
with SHA-256 `e2c09bf86f31fd4aefde283083012a2da9c4e5c93b5a0f51ae54f86aba33dc98`;
the complete path/content inventory is retained externally with the logs.

The ordinary regression suite reports 115 tests: 93 pass and 22 optional Lean
integration tests are skipped; those 22 actual Lean/Lake fixtures also pass
in separate opt-in runs. They cover wrong types and constants, restricted
universes, conditional/incomplete proofs, unsupported axioms, elaboration
spoofing, independent replay, omitted sources and stale artifacts. All three
exact-arithmetic generator checks, canonical-source/README checks and TeX
regeneration checks pass. The PDF was regenerated with XeLaTeX.

Raw controlled logs are `before-{clean-build,focused,full,incremental-build}.log`
and their `after-` counterparts in the external directory above. A failed
561.34-second integration attempt exposed coefficient-alias normalization in
transfer lemmas; it was fixed, the isolated project output was cleared, and the
final clean run restarted. That partial attempt and contended pilots are excluded
from the comparison.
