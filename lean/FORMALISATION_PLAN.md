# Historical formalization and validation record

This record preserves the actual 20 October 2026 development timings, model
identities, tool roles and legacy checker mapping. It is not a maintained prose
proof or a claim that the immutable canonical propositions are proved.
The old proof outline and detailed development plan are available in Git history;
the historical supplement is the temporary prose-proof exception.

For current sources, setup and verification use [README.md](README.md).
For the canonical proof coverage and subsequent validation observations use
[the migration record](../docs/MIGRATION.md). The single contribution history is
[CONTRIBUTIONS.md](../CONTRIBUTIONS.md). Earlier reuse descriptions and obsolete
implementation paths remain available in Git history.

## Historical measured timing record

All measurements below are from 20 October 2026. Historical partial-completion
counts and forecasts have been removed; the measured windows and caveats are
retained. They do not provide isolated serial estimates for each section.

### Measured pilot: P06

[KL/Weighted/Entropy.lean](SingularValueBounds/KL/Weighted/Entropy.lean)
now verifies the finite-integrability version of supplementary Lemma S1.4.
It contains six lemmas: the scalar entropy/exponential inequality, positivity
and normalisation of the exponential moment, weighted entropy, weighted-product
integrability for nonnegative observables, and the corresponding entropy
corollary. This section requires no external numerical conditions.

The proof worker was explicitly selected as `gpt-6.1-sol` with `ultra`
reasoning for the requested Fast-mode experiment. Local metadata identifies
the available `priority` tier as Fast; the worker tool does not provide a
separate per-request service-tier telemetry report. One short read-only API
assistant and the coordinating agent supported implementation and review.
These are elapsed wall times, not sums of worker activity or CPU timings.

| Event | UTC, 20 October 2026 |
|---|---|
| Overall timed task began | 11:56:52 |
| Explicitly selected proof worker began | 11:57:42 |
| First proof-file edit | 11:58:49 |
| First successful module build | 12:00:41 |
| Full build and axiom audit started | 12:01:00 |
| Full build and axiom audit observed complete | 12:01:47 |

Measured durations:

- Proof worker start to successful module build: **2 min 59 s**.
- First edit to successful module build: **1 min 52 s**.
- Overall start through successful full build and axiom audit: **4 min 55 s**.
  Subsequent documentation is excluded.

There were three source elaboration attempts and two earlier setup failures.
The setup failures exposed central-directory write permissions and Lean's
source-root check across the central symlink. The latter was fixed by setting
the library's `srcDir` to the canonical source directory; dependency pins and
central build/dependency paths were preserved. The proof corrections concerned
function-coercion normalisation in rewrites.

### Three further completed sections

P05, P07 and P09 were then implemented by three explicitly selected
`gpt-6.1-sol` workers with `ultra` reasoning under the same requested Fast
configuration. They worked in separate files in parallel. A coordinator
performed integration, Python checking and the full audit. The module times
below are worker-start to **observed successful module build**, including
inspection and compiler corrections; they exclude documentation afterward.

| Section | Worker start UTC | First edit UTC | Successful module build observed UTC | Elapsed minutes |
|---|---|---|---|---:|
| P05 — Gaussian comparison and quadratic moments | 12:07:14 | 12:08:24 | 12:10:08 | 2.9 |
| P07 — analytic enclosure rules and finite interface | 12:07:25 | 12:08:21 | 12:11:01 | 3.6 |
| P09 — offset moments and sharp lower Laplace | 12:07:39 | 12:10:00 | 12:13:44 | 6.1 |

The second batch began at 12:06:45 UTC. The integrated build/audit ran from
12:14:26 through observed completion at 12:15:43 UTC: **1.3 minutes** for
that validation and **9.0 minutes** for the parallel batch through validation.
The batch duration must not be interpreted as sequential effort for all three
workers. P09's Moments artifact was created at 12:13:35; the table consistently
uses the later observed completion rather than mixing timestamp conventions.

### First nine-section extension

The nine-section batch began at **12:19:34 UTC**. Three proof workers were
explicitly selected as GPT-6.1 Sol Ultra with the same available Fast/priority
setup described above. The coordinating agent implemented P01/P08 and the
concrete certificate and determinant bridges, integrated the library, reviewed
scope and ran the full checks. These assisted timings are not an isolated
single-worker model benchmark. Several work windows overlap and must not be
added or treated as isolated per-worker timings.

| Work | Measured development window, UTC | Minutes | Timing scope |
|---|---|---:|---|
| P01 and P08 | Approximately 12:23:30–12:36:01 | 12.5 | Shared coordinating-agent window; includes dependency waits and work on both interfaces |
| P02 | 12:23:03–12:26:04 | 3.0 | First source edit through observed complete root module; earlier inspection excluded |
| P10 | 12:25:50–12:32:01 | 6.2 | First source edit through complete lower comparison module |
| P18 | 12:21:04–12:28:34 | 7.5 | Worker start through complete entropy/integral package |
| P21 | 12:28:34–12:37:16; 12:49:04–12:50:57 | 8.7 + 1.9 | Moment estimates/series, then explicit exponential integrability and integral/series equality; intervening P15 work excluded |
| P15–P17 primary worker | 12:20:42–12:49:41 | 29.0 | Shared three-package window; includes matrix/norm, majorization and certificate assistance from the other workers and coordinator |
| P15 majorization/joint-tail assistance | 12:37:16–12:46:08 | 8.9 | Additional worker window, already overlapping the preceding row |

P15's complete joint-tail build was observed at 12:46:08; the final actual-matrix
P17 certificate wrapper was observed built at 12:46:21; P16's final two-piece,
all-fifteen-rate wrapper compiled at 12:49:22. P21's last integrability interface
compiled at 12:50:57. The integrated `./supplementary/lean/check.sh` build and
axiom audit ran from approximately **12:51:27 to 12:55:11 UTC** and passed.
The batch through observed full validation took **35 min 37 s (35.6 minutes)**.
Documentation completed afterwards is excluded.

### Second nine-section extension

This batch implemented P03, P04, P11, P13, P14, P19, P20, P22 and P23. It began
at **13:00:08 UTC** on 20 October 2026. Three explicitly selected GPT-6.1 Sol
Ultra workers used the same available Fast/priority setup described above;
the coordinator implemented and integrated additional proofs and checkers.
These are assisted, overlapping wall-clock measurements, not isolated model
benchmarks or additive worker times.

| Work | Observed development window, UTC | Minutes | Timing scope |
|---|---|---:|---|
| P03/P04 | 13:00:37–13:18:50 | 18.2 | Shared worker window; P03 built at 13:16:31, transfer at 13:18:50 |
| P11 | 13:00:08–13:39:34 | 39.4 | Coordinator window shared with integration and other helpers; plateau assistance overlapped |
| P13 | 13:01:05–13:10:13 | 9.1 | Worker start through complete covariance package |
| P14 | 13:10:13–13:28:18 | 18.1 | Endpoint lower cap, with overlapping polynomial-certificate assistance |
| P19/P22 | 13:00:56–14:03:00 | 62.1 | Shared endpoint worker window; P22 built 13:41:54, P19 built 14:02:15, bundled theorem 14:03:00 |
| P20 | 13:32:45.6–14:01:55 | 29.2 | First main entropy proof edit through full mean build; excludes earlier inspection and overlaps two helpers |
| P20/P23 final bundle | 14:01:55–14:03:16 | 1.4 | Combines the completed general mean and MGF without a mean hypothesis |
| P23 finite/analytic completion | 13:38:09–13:56:50 | 18.7 | Shared scalar worker/coordinator window; preliminary fourth-moment work began about 13:33 |

The final full build and axiom audit began at approximately **14:03:55 UTC**
and was observed complete at **14:13:08 UTC**. The batch through this validation
took **73.0 minutes**; documentation afterward is excluded.

### Final P12/P24 batch

The final assisted P12/P24 batch began at **14:24:48 UTC**: the actual mixed pathwise budget was observed
built at **14:43:33 UTC**, and the complete final theorem's compiled artifact
was written at **14:44:37 UTC** (observed before the full audit began).
These overlapping measurements include three explicitly selected GPT-6.1 Sol
Ultra workers and the coordinator; they are not isolated single-worker timings.

The complete `check_hybrid.sh` run began at **14:45:40 UTC** and was observed
successful at **14:50:46 UTC**. The full batch through hybrid validation
took **26.0 minutes**; later documentation and LaTeX builds are
excluded.

## Historical hybrid trust boundary

The legacy analytic theorem is conditional on `FinalCertificateConditions`.
External exact Python arithmetic checked its finite predicates and supplied no
Lean proof terms. The following correspondence records the retired pipeline in Git history; it
is not an active acceptance interface and its files need not remain in the tree.

| Final bundle field | Exact runner under `supplementary/lean/` |
|---|---|
| `generalLower` | `check_lower_interface.py`, `check_lower_plateau_cost.py` |
| `endpointLowerTable`, `endpointLowerFar` | `check_endpoint_interface.py` |
| `majorant`, `normDeterminant`, `rate` | `check_polynomial_interface.py` |
| `generalMeanCells` | `check_general_mean_cells.py` |
| `generalMeanEntropy` | `check_general_mean_entropy.py` |
| `endpointMean` | `check_upper_mean_interface.py` |
| `endpointLogratio` | `check_upper_mgf_interface.py` |
| `generalSecond` | `check_general_second_interface.py` |

The enclosure runner also checked a pilot; the profile-integral runner repeated
arithmetic whose comparisons already had Lean proofs. Source hashes guarded
drift and never proved semantic correspondence. The original checker included
sharpness checks outside the theorem dependency chain.

The original completion run audited 3,241 targets through 53,669 constants.
After retirement of 16 modules exclusive to the earlier theorem and 17 audit
targets, the recorded audit had 3,224 targets and retained a 3,015-target
checkpoint. These are historical counts, not the expanded current inventory.
[VERIFICATION_REPORT.md](VERIFICATION_REPORT.md) and
the original `verification_manifest.json` in Git history preserve the dates,
source snapshots and observed validation details. The only allowed axioms were
`propext`, `Classical.choice` and `Quot.sound`; that allowlist remains in force.

The pinned Lean version was 4.19.0 and Mathlib revision was
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Those pins are unchanged.
The preceding record describes the original paper checkout, where proof sources
were Git-ignored and dependencies/builds were central. Current portable setup
instructions belong to [README.md](README.md); historical paths and commands
must not be used as an alternative live setup.

Neither the historical hybrid run nor this restructuring establishes novelty
or priority. Preserve the unresolved assessments in
[PROVENANCE.md](../docs/PROVENANCE.md).
