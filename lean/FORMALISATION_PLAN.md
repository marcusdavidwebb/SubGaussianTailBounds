# Completed plan for hybrid Lean/Python verification

This is the historical completion record. Paths and setup descriptions below
refer to the original paper checkout. Use [README.md](README.md) for the current
portable setup and [the public provenance note](../docs/PROVENANCE.md) for
material that is not distributed in this repository.

**Date:** 20 October 2026. **Status:** all 24 sections complete.  
**Verification model:** Lean proves the analytic implication; exact Python checks its explicit finite rational premises.

This record follows Theorem S1.1 and Sections S1.1–S1.6 of the
[supplementary materials](../supplementary.tex), including the barrier
construction imported from the in-preparation main paper (not included here). Obsolete
implementation instructions and superseded forecasts were removed after
completion. The reuse assessment, completed section map and measured timing
evidence are retained.

## 1. Scope and target statement

The user has specified that auxiliary lemmas need only be formalised in
versions sufficient for the final theorem. The implemented scope is:

- The analytic proof follows the supplement's sequence and constants. Module
  documentation identifies the corresponding LaTeX labels.
- Mixed regularity is specialised to the two profiles used by the final theorem;
  arbitrary absolutely continuous profiles are outside scope.
- Entropy inequalities use finite-integrability versions, with integrability
  proved in every application; the most general extended-real version is outside scope.
- Matrix, probability, real-analysis and certificate-interpretation arguments
  are in Lean. Python checks finite comparisons, coefficient identities, tables
  and subdivision bookkeeping. Section 5 records the interface.
- Main-paper applications and sharpness examples are outside the Lean scope.
  Its barrier arguments used by the supplement **are** included.

For independent centred isotropic rows with the stated directional MGF bound,
\(m\ge n\ge1\), \(K\ge1\), \(L=\log(eK)\), and every \(t\ge0\), the
combined Lean/Python verification establishes

\[
\begin{aligned}
\mathbb P\{\sigma_{\min}(S)\le\sqrt m-K\sqrt n-\alpha KL
                    -\beta K\sqrt L\,t\}&\le e^{-t^2/2},\\
\mathbb P\{\sigma_{\max}(S)\ge\sqrt m+K\sqrt n+\gamma KL
                    +\delta K\sqrt L\,t\}&\le e^{-t^2/2}.
\end{aligned}
\]

The public results expose both choices:

| Range | \(\alpha\) | \(\beta\) | \(\gamma\) | \(\delta\) |
|---|---:|---:|---:|---:|
| Every \(K\ge1\) | \(96/25\) | \(79/50\) | \(47/20\) | \(3/2\) |
| \(K=1\) | \(33/25\) | \(28/25\) | \(58/25\) | \(\sqrt2\) |

These are exactly the displayed decimals \(3.84,1.58,2.35,1.5\) and
\(1.32,1.12,2.32,\sqrt2\). All four fixed targets were retained.

The original probabilistic scope is retained: arbitrary probability spaces,
independent rows that need not have the same distribution, dependent
coordinates within a row, and all \(n\) Gram singular values including zeros.
The non-strict tail events include \(t=0\), \(n=1\), zero rows, rank deficiency,
and negative or zero lower thresholds.

The completed namespace is `SingularValueBounds.KL`. Its public results in
[KL/Theorem.lean](SingularValueBounds/KL/Theorem.lean) are
`singular_value_tails_general_of_certificates`,
`singular_value_tails_one_of_certificates`, and
`theorem_explicit_constants_of_certificates`. The last concludes
`TheoremKL μ generalConstants ∧ TheoremKLOne μ`.

Their numerical premise is the actual typed bundle `FinalCertificateConditions`
in [Certificates/Final.lean](SingularValueBounds/KL/Certificates/Final.lean).
Its eleven fields contain only the specific finite families required by the
proof. There is no one-row estimate, correction budget,
real-variable inequality or matrix assertion in the final numerical premise.
The original row assumptions and non-strict events are preserved.
The earlier `SingularValueBounds.theorem11` and `singular_value_tails` results
were retired after KL completion; they are no longer exported.

## 2. Reuse assessment at the starting point

This assessment records the starting point before the new KL modules were
implemented. All existing identifiers in this section are in namespace
`SingularValueBounds`. “Retain” records which inspected statement supplied a
required fact, sometimes after a wrapper. “Extend” and “recycle” describe the additional work subsequently
completed under `KL`; they are historical assessments, not outstanding tasks.
Sixteen modules exclusive to the earlier theorem were subsequently retired.
References to those files below are historical plain-text paths; the 32 shared
supporting modules required by KL remain in the current library.

| Existing source and declarations | Assessment for the current proof |
|---|---|
| [Core/Assumptions.lean](SingularValueBounds/Core/Assumptions.lean): `CentredIsotropic`, `SubGaussianMGF` | **Retain.** Directional isotropy and MGF assumptions already allow dependent coordinates. Their equivalence to the paper's vector/covariance formulation and their explicit measurability/integrability fields required justification at the statement boundary. |
| [Core/Constants.lean](SingularValueBounds/Core/Constants.lean): `logParameter`, `one_le_logParameter`, `logParameter_eq_log_exp_mul` | **Retain.** `logParameter K = 1 + log K` represents \(L\). The old `fourthMomentConstant` is preserved; refined bounds are separate. |
| [Core/Matrix.lean](SingularValueBounds/Core/Matrix.lean): `real_spectral_decomposition`, `real_spectral_trace`, `real_spectral_trace_square`, `quadratic_conjugate_diagonal`, `diagonal_rankOne_inverse` | **Retain.** Spectral algebra and the rank-one inverse identity support both new comparisons. |
| [Core/MeasurableMatrix.lean](SingularValueBounds/Core/MeasurableMatrix.lean): `measurable_matrix_inverse` | **Retain.** This does not by itself prove measurability of a selected root or an adaptive correction. |
| [QuadraticForms/Basic.lean](SingularValueBounds/QuadraticForms/Basic.lean): `SubGaussianMGF.directional_memLp`, `.directional_integrable_pow`, `.quadratic_memLp_two`, `CentredIsotropic.quadratic_mean` | **Retain.** These discharge many integrability and isotropy obligations. |
| [QuadraticForms/GaussianComparison.lean](SingularValueBounds/QuadraticForms/GaussianComparison.lean): `quadratic_exponential_bound` | **Retain with a wrapper.** It proves exponential integrability and the eigenvalue-product bound. The determinant/log-determinant form of Lemma S1.3 required the P05 wrapper. |
| [QuadraticForms/ScalarMoments.lean](SingularValueBounds/QuadraticForms/ScalarMoments.lean): `scalar_even_moment_lower`, `scalar_fourth_implicit`, `scalar_fourth_general`, `scalar_fourth_unit` | **Retain.** The \(5K^2L\) and \(K=1\) fourth-moment results are already available. **Extended in P09/P23** to \(4.99K^2L+1/2\) and the retained-cosh exclusion used near \(K=1\). |
| [QuadraticForms/Bounds.lean](SingularValueBounds/QuadraticForms/Bounds.lean): `quadratic_second_strong`, `quadratic_endpoint_variance` | **Retain/generalise.** The first uses the old fourth-moment constant; P05 generalises through a supplied directional bound. The endpoint variance is directly usable. The new mixed covariance inequalities required P13. |
| [Scalar/Exponential.lean](SingularValueBounds/Scalar/Exponential.lean): `integral_ratio_cauchy` | **Retain.** The integrability arguments from `scalar_lower_exponential` are recycled; P09 proves the sharper denominator \(1+(m_2-\tfrac12)\lambda\). |
| [Core/ScalarTail.lean](SingularValueBounds/Core/ScalarTail.lean): `exponential_tail_moment`, `exponential_tail_positive_part_moment`; [Scalar/TailSecond.lean](SingularValueBounds/Scalar/TailSecond.lean): `exponential_tail_second_le` | **Retain as tools.** Their finite-measure scope also permits restriction to a rare event without assuming independence of that event and the random variable. |
| [Scalar/UpperExponentialTools.lean](SingularValueBounds/Scalar/UpperExponentialTools.lean): `exponential_tail_remainder` | **Recycle.** Useful tail-integration machinery; P21–P23 supply the new coefficient-sensitive moment-to-MGF arguments. |
| [Shifts/UpperRoot.lean](SingularValueBounds/Shifts/UpperRoot.lean): `upperShift`, `upperShift_nonneg`, `upperShift_lt_iff`, `measurable_upperShift`; [Shifts/UpperMatrixUpdate.lean](SingularValueBounds/Shifts/UpperMatrixUpdate.lean): `upperShift_preserves`, `upperShift_unique_preserves` | **Retain.** These already construct the exact upper root, prove joint measurability, preserve positive definiteness, and give equality of inverse traces. |
| [Spectral/Scalar.lean](SingularValueBounds/Spectral/Scalar.lean): `resolventRoot`, `resolventRoot_eq`, `resolventRoot_unique`; [Spectral/Continuity.lean](SingularValueBounds/Spectral/Continuity.lean): `continuous_resolventRoot` | **Recycle for the exact lower root.** The retained continuity result fixes the target trace; P02 extends to joint dependence on matrix and target. |
| [Concentration/IndependentAveraging.lean](SingularValueBounds/Concentration/IndependentAveraging.lean): `independent_weighted_average`; `SpectralConcentration/RowLaws.lean` (retired): `centredIsotropic_map`, `subGaussianMGF_map` | **Retain.** These provide the Fubini induction and transfer of assumptions to the next row's law. P04 generalises the private past-row arguments in [Rows.lean](SingularValueBounds/SpectralConcentration/Rows.lean) to an entire measurable history-dependent state. |
| [SpectralConcentration/Chernoff.lean](SingularValueBounds/SpectralConcentration/Chernoff.lean): `spectral_lower_tail_of_mgf`, `spectral_upper_tail_of_mgf`, `spectral_lower_sqrt_tail`, `spectral_upper_sqrt_tail` | **Retain.** Despite their names, the lemmas apply to an arbitrary real random variable, not just the old spectral functions. |
| [Main/VariationalOptimization.lean](SingularValueBounds/Main/VariationalOptimization.lean): `spectral_lower_optimal_normalization`, `spectral_lower_optimal_cost` and their upper counterparts; [Main/SpectralBounds.lean](SingularValueBounds/Main/SpectralBounds.lean): `singularValues_sq`, `smallestSingularValue_sq_gt`, `largestSingularValue_sq_lt`, `gram_eq_sum_outer` | **Retain the algebra and matrix-to-singular-value passage.** The new barrier bounds supply their inputs. |

Four parts must not be mistaken for reusable proofs of the new result:

1. `paperLowerShift` in `Shifts/Lower.lean` (retired)
   is an explicit conservative ratio. Its preservation theorem gives
   \(\operatorname{tr}R_{\mathrm{new}}\le\operatorname{tr}R\), not equality.
   The supplement uses a different, exact lower root.
2. `upperComparison` in
   [Shifts/UpperQuadraticComparison.lean](SingularValueBounds/Shifts/UpperQuadraticComparison.lean)
   is \(R+P(\operatorname{tr}(RP)I-R)\). The new matrix is
   \(C=R+P(\operatorname{tr}(RP)I-2R)\). Its trace and positivity properties
   differ; it can be zero when \(n=1\). The exact-root machinery is reused;
   P17 supplies the new comparison theorem.
3. The capped variational spectral functions, `spectral_mgf`, and
   `Main/DimensionAllowance.lean` implement separate caps and the old
   \(n^{1/6}\) optimisation. The new outward corrections depend on the
   ordered row history. Their proof patterns support P03/P04, but their
   conclusions describe the earlier theorem.
4. The old scalar exponential estimates do not give the new fluctuation
   constants. Likewise, `scalar_cosh_fourth_lower` drops a term needed by
   the new upper argument. P22 supplies the additional coefficients of the
   explicit Gaussian MGF majorant.

## 3. Completed sections and proof map

The current KL sources are under `SingularValueBounds/KL/`, grouped into
`Barrier/`, `Weighted/`, `Certificates/`, `Lower/` and `Upper/`, with
`Statement.lean`, `Transfer.lean` and `Theorem.lean` at the top level.
All 147 KL modules are imported by `SingularValueBounds.lean`.

The proof uses explicit spectral quantities on positive-definite matrices:

\[
F(R)=\sqrt{\operatorname{tr}(R^2)},\qquad
M(R)=\max_i\lambda_i(R),\qquad \kappa=M(R)/F(R).
\]

`Barrier/Norms.lean` relates these to Frobenius and Euclidean operator norms;
the default norm on a Lean matrix or function type is not substituted for
these norms. The theorem's tail parameter retains its meaning throughout.

All sections below are complete; projected remaining minutes are zero.
The table records the original package dependencies and paper correspondence.
The following outcomes identify their actual source modules.

| ID | Discrete section | Paper correspondence | Dependencies | Remaining minutes |
|---|---|---|---|---:|
| P01 | Current statement and hybrid verification interface: **complete** | Theorem S1.1 | Existing foundations; P02 for exact-row wrappers | 0 |
| P02 | Exact roots and resolvent interfaces: **complete** | Main §3; S1.3; S1.6.1 | Existing resolvent and upper-root foundations | 0 |
| P03 | Outward corrections and deterministic barrier process: **complete** | Main §4; S1.1 | P02 | 0 |
| P04 | Independent-row iteration and transfer: **complete** | S1.1, Lemma S1.2 | P03 | 0 |
| P05 | Gaussian comparison and quadratic adapters: **complete** | S1.2, Lemma S1.3 | Existing foundations | 0 |
| P06 | Weighted entropy: **complete** | S1.2, Lemma S1.4 | Mathlib only | 0 |
| P07 | Analytic enclosure rules and Python check mapping: **complete** | S1.2 arithmetic rules | Mathlib only | 0 |
| P08 | Bernstein and coverage implications: **complete** | S1.2 Bernstein rules | P07 | 0 |
| P09 | Fourth moments and sharpened lower Laplace bound: **complete** | S1.3 | P05; existing scalar tools | 0 |
| P10 | Deterministic exact-lower-shift comparisons: **complete** | S1.3 | P02, P05 | 0 |
| P11 | General lower spectral profile and its certificates: **complete** | S1.4, Lemma S1.5 | P06, P08, P09, P10 | 0 |
| P12 | Mixed-cap cost for the actual profiles: **complete** | S1.4, Lemma S1.6 | P03, P08 | 0 |
| P13 | \(K=1\) covariance refinements: **complete** | S1.5 | P05 | 0 |
| P14 | \(K=1\) lower profile, cap and arithmetic: **complete** | S1.5 | P08, P10, P13 | 0 |
| P15 | Exact upper tail and spectral-shape bounds: **complete** | S1.6.1 | P02, P05 | 0 |
| P16 | Upper-tail rates exceeding two: **complete** | S1.6.1, Lemma S1.7 | P08, P15 | 0 |
| P17 | New upper comparison and determinant majorants: **complete** | S1.6.2, Lemma S1.8 | P08, P15 | 0 |
| P18 | Entropy integration and rational integral bounds: **complete** | S1.6.3 | P06, P07, P15 | 0 |
| P19 | \(K=1\) upper mean: **complete** | S1.6.3, Lemma S1.9 | P08, P17, P18 | 0 |
| P20 | General upper mean: **complete** | S1.6.3, Lemma S1.10 | P16, P17, P18 | 0 |
| P21 | Moments from the mean and a tail: **complete** | S1.6.4, Lemma S1.11 | P07, P15 | 0 |
| P22 | \(K=1\) upper exponential moment: **complete** | S1.6.4, Lemma S1.12 | P17, P19, P21 | 0 |
| P23 | General upper exponential moment: **complete** | S1.6.4, Lemma S1.13 | P09, P20, P21, P22 | 0 |
| P24 | Conditional theorem assembly and hybrid audit: **complete** | End of S1.6; S2 verification status | P04, P09, P11, P12, P14, P22, P23 | 0 |

### P01. Statement and interfaces

[Statement.lean](SingularValueBounds/KL/Statement.lean) defines the current
general/endpoint targets, exact quartets and finite arithmetic, row-estimate
and correction-budget interfaces. [Barrier/Norms.lean](SingularValueBounds/KL/Barrier/Norms.lean)
proves Euclidean Rayleigh bounds and attainment. The final statement was
compared with `thm:explicit-constants`, including general constants at K=1.

### P02. Exact roots and resolvents

[Barrier/Roots.lean](SingularValueBounds/KL/Barrier/Roots.lean) constructs the
exact lower root using the reciprocal-trace root of
\(-[R^{-1}+xx^\top]\) at target \(\operatorname{tr}R\).
It proves positive gaps, nonnegativity, uniqueness, trace equality, zero-row
equality, joint continuity and measurability. The exact upper root is retained;
no continuously varying eigenvectors are required.

### P03. Outward corrections and the barrier process

[Barrier/Corrections.lean](SingularValueBounds/KL/Barrier/Corrections.lean),
[Process.lean](SingularValueBounds/KL/Barrier/Process.lean),
[Budget.lean](SingularValueBounds/KL/Barrier/Budget.lean) and
[Initialization.lean](SingularValueBounds/KL/Barrier/Initialization.lean)
prove the least measurable constant-cap correction and deterministic process,
trace preservation at row updates, decrease during corrections, disjoint trace
intervals and strict initial/final gaps. The initial distance is
\((K^2n+w\sqrt n)/b\), with corrections at most \(w\sqrt n/b\).
These are pathwise results for every deterministic row sequence.

### P04. Independent-row iteration and transfer

[Barrier/Adaptive.lean](SingularValueBounds/KL/Barrier/Adaptive.lean) and
[Transfer.lean](SingularValueBounds/KL/Transfer.lean) prove measurable history
iteration, independence, integrability and the MGF induction, then transfer to
actual singular values. The intermediate mixed-budget transfer accepts
\(d^2=K^2n+2K^2L\mathcal H\sqrt n\); P12 supplies its pathwise budget.
The strict allowance \(d<K\sqrt n+KL\mathcal H\) handles zero lower thresholds.

### P05. Gaussian and quadratic interfaces

[Weighted/Gaussian.lean](SingularValueBounds/KL/Weighted/Gaussian.lean)
proves `quadratic_exponential_det_bound`, `quadratic_log_mgf_le_logdet` and
`quadratic_log_mgf_le_sum`, including exponential integrability under the
positive-definite gap. `quadratic_second_of_directional_fourth` gives Gaussian
averaging for a supplied homogeneous fourth-moment bound. No coordinate
independence or external numerical premise is introduced.

### P06. Weighted entropy

[Weighted/Entropy.lean](SingularValueBounds/KL/Weighted/Entropy.lean) proves
`weighted_entropy` and `weighted_entropy_of_nonneg` using the exponential
tangent inequality. Zero weights are handled. The nonnegative-observable
corollary derives weighted-product integrability from finite entropy and the
exponential moment, supplied internally in each final application. P06 uses
Mathlib directly and has no P05 dependency or external numerical premise.

### P07. Analytic enclosure rules and the Python interface

[Certificates/Enclosures.lean](SingularValueBounds/KL/Certificates/Enclosures.lean)
proves exponential Taylor, odd-logarithm, power-of-two, reciprocal, sign,
product, division and outward rounding rules. General rules are unconditional;
`ExpCertificate` and `LogCertificate` pilots retain explicit finite premises,
checked by [check_enclosure_interface.py](check_enclosure_interface.py).
The large families are connected in their respective packages, not in P07 alone.

### P08. Bernstein and coverage implications

[Certificates/Polynomial.lean](SingularValueBounds/KL/Certificates/Polynomial.lean)
proves univariate/tensor Bernstein implications, affine substitution, degree
elevation, closed subdivision/clipping, degenerate cells and root/calculus
rules. Python checks the concrete coefficient and subdivision data. Lean proves
whole-domain consequences. P11 uses direct Taylor/Bernstein plateau bounds,
avoiding the originally proposed critical-root isolation.

### P09. Fourth moments and the lower Laplace estimate

[Lower/Moments.lean](SingularValueBounds/KL/Lower/Moments.lean) proves
\(m_4\le(499/100)K^2L+1/2\), its homogeneous directional form and trace-one
quadratic consequences, including the real-L argument and small Taylor bounds.
[Lower/Laplace.lean](SingularValueBounds/KL/Lower/Laplace.lean) retains
\(m_2-1/2\) in the sharp weighted estimate. Its general/endpoint applications
discharge moment and integrability hypotheses, giving
\(\nu_-=(499/100)K^2L\) and \(5/2\), with the comparisons to
\(\beta=79/50\) and \(28/25\) proved in Lean. There is no external numerical premise.

### P10. Lower deterministic comparisons

[Lower/Comparison.lean](SingularValueBounds/KL/Lower/Comparison.lean) proves
Sherman–Morrison trace identities, both exact lower ratios, the normalized
minimum bound, PSD and canonical positive-definite comparison matrices.
It establishes `eq:app-low-two-comparisons`, including zero/division cases,
the \(B_0\) comparison and \(B=R+P(A\eta I-cR)\).

### P11. General lower profile

[Lower/GeneralProfile.lean](SingularValueBounds/KL/Lower/GeneralProfile.lean)
and [ProfileCells.lean](SingularValueBounds/KL/Lower/ProfileCells.lean)
prove the actual normalized profile from finite conditions, using real-p
integrability, moment/entropy bounds, spectral monotonicities and all 681
closed cells. Direct finite Taylor/Bernstein plateau certificates establish
\[
h_*(k)=\min\{4137/1000,\max\{3/2,
57/40+23k/10+47k^2/20-3k^3/10\}\}.
\]
All overlap and boundary cases of Lemma S1.5 are covered.

### P12. Cost of the two concrete mixed caps

[Barrier/MixedPathwise.lean](SingularValueBounds/KL/Barrier/MixedPathwise.lean)
proves the actual initial-plus-outward budget, using the spectral
Cauchy–Schwarz envelope, monotone cap and disjoint trace intervals.
[Lower/ProfileIntegral.lean](SingularValueBounds/KL/Lower/ProfileIntegral.lean)
and [ProfileIntegralRegularity.lean](SingularValueBounds/KL/Lower/ProfileIntegralRegularity.lean)
prove singular/angular integral correspondence, integrability, Lipschitz
bounds, breakpoints and both strict costs:
\[
\mathcal H(h_*)<96/25,\qquad
\mathcal H(\min\{2k,73/50\})<33/25.
\]
The cubic breakpoints are unique roots at 3/2 and 4137/1000; the endpoint
profile breaks at 73/100. A clipped inverse and Fubini/Young inverse-integral
identity justify profile breakpoints without inverse differentiability.
The n=1 case is included. All scalar comparisons here are Lean-proved; no
new external numerical premise is needed.

### P13. Endpoint covariance estimates

[Lower/Covariance.lean](SingularValueBounds/KL/Lower/Covariance.lean),
[EndpointQuartic.lean](SingularValueBounds/KL/Lower/EndpointQuartic.lean) and
[EndpointRankOne.lean](SingularValueBounds/KL/Lower/EndpointRankOne.lean)
prove mixed PSD covariance and orthogonal rank-one refinements using quartic
averaging and the original directional assumptions. No coordinate independence,
unwarranted commutation or external numerical premise is introduced.

### P14. Endpoint lower cap

[Lower/EndpointCap.lean](SingularValueBounds/KL/Lower/EndpointCap.lean) and
[EndpointCertificateBridges.lean](SingularValueBounds/KL/Lower/EndpointCertificateBridges.lean)
prove the endpoint profile \(\min\{2\kappa,73/50\}\), including the
operator-cost range \(\kappa\le73/100\), eight certified boxes and far-shape
region. [check_endpoint_interface.py](check_endpoint_interface.py) checks
the finite table/quartic conditions. P09 and P12 complete the endpoint lower bound.

### P15. Upper shifts and their tails

[Upper/ExactTails.lean](SingularValueBounds/KL/Upper/ExactTails.lean),
[Margin.lean](SingularValueBounds/KL/Upper/Margin.lean),
[Majorization.lean](SingularValueBounds/KL/Upper/Majorization.lean) and
[JointTail.lean](SingularValueBounds/KL/Upper/JointTail.lean) establish the
exact event, Gaussian rate/shape/margin bounds and joint prefactor
\(\mathcal G(\kappa,a,q)\) with all parameter restrictions. The upper
criterion is identified with \(B_h/h\) for h>0, with h=0 handled separately.
These results have no external numerical premise.

### P16. Rates exceeding two

[Upper/ExtendedTailPieces.lean](SingularValueBounds/KL/Upper/ExtendedTailPieces.lean)
and its `TailExtension`, `RateEnvelope`, `RateAnalysis` and `ExtendedTails`
dependencies prove continuous rescaling, actual extended shift tails and both
continuation pieces. `RateCertificateConditions` instantiates all fifteen rates
and their \(C_q\) corrections, using canonical norms. Python checks the
finite degree-27/coefficient data; Lean proves whole-domain consequences.

### P17. Upper comparison and determinants

[Upper/LogdetCertificates.lean](SingularValueBounds/KL/Upper/LogdetCertificates.lean)
and its comparison, determinant and certificate dependencies prove the literal
\(C=R+P(\operatorname{tr}(RP)I-2R)\) comparison, PSD/trace bounds and n=1
zero case. They establish both norm bounds, actual \(\mathcal J_0,\mathcal J_1\),
six majorants and retained-largest-eigenvalue bounds. Python checks finite
polynomial/Taylor conditions on 165 adaptive rectangles; their whole-domain
matrix consequences are Lean-proved independently of later entropy witnesses.

### P18. Entropy integration

[Weighted/EntropyIntegration.lean](SingularValueBounds/KL/Weighted/EntropyIntegration.lean)
and [RationalIntegral.lean](SingularValueBounds/KL/Weighted/RationalIntegral.lean)
prove the entropy layer-cake formula, normalization/finiteness and the rational
bounds for \(I(x)=\int_0^\infty e^{-u}/(x+u)\,du\) from positive-square
remainders. They derive \(\mathbb EY\le1\) from \(D(W)+J/2\le wL\),
including the \(\mathbb EY<1\) case, without an external numerical premise.

### P19. Endpoint upper mean

[Upper/EndpointMean.lean](SingularValueBounds/KL/Upper/EndpointMean.lean)
proves the normalized exact-shift mean at 58/25. Its dependencies establish
entropy Riemann sums and tails beyond 40, separate convexity, bilinear
interpolation and all-domain coverage from 50 small-shape cells and 837 joint
rectangles. Python checks the determinant, corner/leaf and exact rounded data.

### P20. General upper mean

[Upper/GeneralMean.lean](SingularValueBounds/KL/Upper/GeneralMean.lean) proves
the mean at 47/20 for every real K≥1.
[GeneralMeanCellBridges.lean](SingularValueBounds/KL/Upper/GeneralMeanCellBridges.lean)
covers all 1,330 determinant rows with closed feasible coverage, including 26
degenerate leaves covered by existing rows. `GeneralMeanNumerics` and
`GeneralMeanTailEntropy` prove the decreasing/convex entropy argument for all
real L≥1, including L≥4. Two exact runners check the finite cell, witness,
chord/endpoint and rounded data.

### P21. Generic tail-to-moment estimates

[Upper/TailMoments.lean](SingularValueBounds/KL/Upper/TailMoments.lean) proves
cutoff integration, factorial recurrence/base cases, all p≥3 estimates,
the second moment for L≥5/4 and actual exponential integrability with
integral/series equality, including t=0. These estimates have no external
numerical premise.

### P22. Endpoint upper MGF

[Upper/EndpointFullApplication.lean](SingularValueBounds/KL/Upper/EndpointFullApplication.lean)
bundles the actual mean and MGF with factor 4, including exponential
integrability. The proof covers capped weights, three concentrated-spectrum
rare-event cases, restricted measures and the Gaussian majorant coefficients
\(g_p=2^{-p}\binom{2p}{p}\). Only explicit finite mean, determinant and
log-ratio certificate conditions remain. No independence of a rare event and
the random variable is assumed; Gaussian coefficient arguments are proved
separately from the full MGF comparison.

### P23. General upper MGF

[Upper/GeneralApplication.lean](SingularValueBounds/KL/Upper/GeneralApplication.lean)
and [GeneralMGF.lean](SingularValueBounds/KL/Upper/GeneralMGF.lean) give actual
exponential integrability and the MGF with factor \((9/2)K^2L\).
They prove retained-cosh fourth-moment exclusions and rare-event second
moments, with low-shape and small/large-L coverage, including L≤51/50 and
overlap with L≥5/4. Python checks 334 exclusions in \(y=(L-1)^{1/4}\) and
1,002 scalar row bounds. P21 supplies higher moments.

### P24. Conditional theorem assembly and hybrid audit

[Theorem.lean](SingularValueBounds/KL/Theorem.lean) proves all three public
results from the original row assumptions and `FinalCertificateConditions`.
[Lower/MixedApplication.lean](SingularValueBounds/KL/Lower/MixedApplication.lean)
supplies the actual lower process, including restoration of scale without
assuming homogeneity of the nonlinear exact shift.
[Upper/RowEstimates.lean](SingularValueBounds/KL/Upper/RowEstimates.lean)
supplies actual upper MGFs. Both quartets and all analytic budgets are supplied
internally; only the explicit finite rational bundle remains. The completion
run also built the earlier theorem; its exclusive modules have since been
retired. The complete checks and theorem-type/correspondence reviews are
recorded in [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md).

## 4. Measured timing record

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

## 5. Implemented hybrid interface and trust boundary

The analytic theorem is a Lean theorem conditional on `FinalCertificateConditions`.
Python's exact integer/rational arithmetic checks those conditions externally.
Python's implementation, execution and correspondence to the Lean predicates
are therefore part of the combined trust boundary. Exact arithmetic removes
floating-point error; correspondence still requires review.

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

`check_enclosure_interface.py` additionally checks the enclosure pilot;
`check_profile_integrals.py` repeats the original profile arithmetic, whose
comparisons are also proved directly in Lean. The original
`../check_main_constants.py` is unchanged and runs in full, including its
sharpness checks outside the theorem's dependency chain.

All eleven bundle fields unfold into bounded rational comparisons,
coefficient identities, finite subdivision/partition conditions or exact
rounded-arithmetic transcripts. The matrix, probability, integrability,
coverage, real-variable and inverse-integral implications are proved in Lean.
The large numerical recurrences are not replayed in the kernel. Source/data
comparison and independent review check that each runner establishes the
actual predicate. Reviewed-source hashes are drift guards, not proof exports.

Run from the repository root:

```sh
./supplementary/lean/check_hybrid.sh
```

This reuses the installed pinned toolchain and central dependencies, runs the
complete Lean build/audit, the original exact checker and all eleven runners.
Assertions must remain enabled. The finite runners reject optimized Python;
coefficient/margin/transcript mutations are rejected by their existing negative
checks. `check_axiom_audit.py` also rejects missing or duplicate targets,
unexpected axioms and incomplete reports, checks every KL source is imported,
retains the prior target checkpoint and requires the three final theorems.

An explicit numerical hypothesis does not appear as an axiom in
`#print axioms`. The clean axiom audit therefore establishes the conditional
analytic implication; the separate exact runs and correspondence audit
complete the agreed hybrid verification. There is no added axiom, `sorry`,
automatically supplied certificate instance or native-evaluation proof.

## 6. Reproduction and maintenance

The current library contains 147 KL modules and 32 shared supporting modules.
After retirement of the earlier theorem's 16 exclusive modules, the audit has
3,224 targets: 3,200 KL declarations and 24 shared principal targets. The retained
checkpoint has 3,015 targets, with the 17 retired targets removed from its former
3,032. Complete KL source/import coverage and the separate `#print axioms`
reports for the three final public results remain enforced. The allowed axioms
are only `propext`, `Classical.choice` and `Quot.sound`.

The original measured completion run built the earlier theorem as well as KL;
it audited 3,241 targets through 53,669 visited constants and passed the original
checker and all eleven interface runners. Those are historical measurements,
not the current audit inventory. [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md)
records the latest validation and visited-constant count after retirement.

The [source manifest](verification_manifest.json) pins the checked inventory;
hashes are provenance and drift guards, not proofs. Its recorded snapshot
supersedes the initial planning hashes.

The unchanged setup is Lean `leanprover/lean4:v4.19.0`, with Mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (`v4.19.0`). Sources remain
Git-ignored here. Dependencies and builds are central under
`~/Lean/SingularValueBounds/.lake/`; Elan is `~/.elan` and the Mathlib cache
is `~/Library/Caches/mathlib`. The canonical `srcDir` and central source/configuration
links preserve one editable source copy. No toolchain or dependency was
installed, upgraded or copied into OneDrive. See [README.md](README.md) for
storage details.

For future proof/certificate changes, compare theorem types and finite-premise
correspondence with the affected LaTeX statements, then run the complete hybrid
command before updating verification claims. Retain all four constants and
the current KL proof scope. Recheck non-strict events, domain
coverage, equality boundaries, degenerate cells, n=1, t=0 and zero lower thresholds.

The combined result is completed **hybrid verification**, not an unconditional
kernel proof of the numerical bundle. It does not resolve attribution or
novelty questions retained in the original paper checkout's `LITERATURE_AUDIT.md`;
see [the public provenance note](../docs/PROVENANCE.md).
