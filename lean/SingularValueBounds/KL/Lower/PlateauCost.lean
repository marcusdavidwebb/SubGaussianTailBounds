import SingularValueBounds.KL.Lower.PlateauCostData
import SingularValueBounds.KL.Lower.HigherEntropy

/-! # Whole-interval plateau cost and retained-spectrum entropy argument -/
open MeasureTheory Set Polynomial
open scoped Matrix BigOperators Polynomial
namespace SingularValueBounds.KL
open Certificates LowerCertificates
noncomputable section
set_option maxHeartbeats 1500000

def plateauRealD (u A c k : ℝ) : ℝ := 1-u*(k+A*k^2-c*k^3)
def plateauRealPsi (u v w k : ℝ) : ℝ := u*k+2*v*k^2-2*w*k^4
def plateauRealG (u A v w c k : ℝ) : ℝ :=
  plateauRealPsi u v w k+Real.log (plateauRealD u A c k)
def plateauRealE (u v w k : ℝ) : ℝ := v*(1-k^2)-4+w/2-u*k/2+w*k^4

theorem plateauCostD_eval (i : Fin 2) (k : ℝ) :
    realEval (plateauCostD i) k = plateauRealD (plateauCostU i)
      (realEval (plateauCostA i) k) (plateauCostC i) k := by
  simp [realEval,plateauCostD,plateauRealD,Polynomial.eval₂_pow,Polynomial.eval₂_sub]

theorem plateauCostE_eval (i : Fin 2) (k : ℝ) :
    realEval (plateauCostE i) k = plateauRealE (plateauCostU i)
      (realEval (plateauCostV i) k) (plateauCostW i) k := by
  simp [realEval,plateauCostE,plateauRealE,Polynomial.eval₂_pow,Polynomial.eval₂_sub]
  ring

theorem plateauCostMargin_eval (i : Fin 2) (k : ℝ) :
    realEval (plateauCostMargin i) k = realEval (plateauCostD i) k*
      expTaylor 24 (-2*realEval (plateauCostE i) k)-
        400/(9*(plateauCostW i : ℝ)^2*((plateauCostU i : ℝ)*(4137/1000)-4)^2) := by
  simp only [realEval,plateauCostMargin,Polynomial.eval₂_sub,Polynomial.eval₂_mul,Polynomial.eval₂_C]
  rw [show Polynomial.eval₂ (Rat.castHom ℝ) k (polynomialExpTaylor 24 (-C 2*plateauCostE i)) =
      expTaylor 24 (realEval (-C 2*plateauCostE i) k) from polynomialExpTaylor_eval _ _ _]
  simp [realEval,Polynomial.eval₂_mul,Polynomial.eval₂_neg,Polynomial.eval₂_C,Polynomial.eval₂_pow]

/-- The final exponential-over-square-root cost follows from a finite Taylor
polynomial lower bound. Every real-variable implication is proved here. -/
theorem plateau_cost_of_taylor {u w C E d : ℝ} (hu : 0 < u) (hw : 0 < w)
    (hC : 4 < u*C) (hd : 0 < d) (hE : E ≤ 0)
    (hcert : 400/(9*w^2*(u*C-4)^2) ≤ d*expTaylor 24 (-2*E)) :
    4/u+20/(3*u*w)*Real.exp E/Real.sqrt d ≤ C := by
  have ht := expTaylor_le_exp 24 (show 0 ≤ -2*E by linarith)
  have hh : 400/(9*w^2*(u*C-4)^2) ≤ d*Real.exp (-2*E) :=
    hcert.trans (mul_le_mul_of_nonneg_left ht hd.le)
  have hp := mul_le_mul_of_nonneg_right hh (sq_nonneg (Real.exp E))
  have he : Real.exp (-2*E)*Real.exp E^2=1 := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    norm_num
  have hmul : d*Real.exp (-2*E)*Real.exp E^2=d := by rw [mul_assoc,he,mul_one]
  rw [hmul] at hp
  have hdiff : 0 < u*C-4 := by linarith
  have hden : 0 < 3*w*(u*C-4) := by positivity
  have hs : Real.sqrt d^2=d := Real.sq_sqrt hd.le
  have hroot : 20*Real.exp E ≤ 3*w*(u*C-4)*Real.sqrt d := by
    have hsq : (20*Real.exp E)^2 ≤ (3*w*(u*C-4)*Real.sqrt d)^2 := by
      rw [div_mul_eq_mul_div] at hp
      have hp := (div_le_iff₀ (show 0 < 9*w^2*(u*C-4)^2 by positivity)).mp hp
      simp only [mul_pow,hs]
      nlinarith only [hp]
    nlinarith [Real.exp_pos E,Real.sqrt_pos.mpr hd,mul_pos hden (Real.sqrt_pos.mpr hd)]
  have hterm : 20/(3*u*w)*Real.exp E/Real.sqrt d ≤ C-4/u := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hd)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 3*u*w by positivity)).mpr
    have heq : (C-4/u)*Real.sqrt d*(3*u*w)=3*w*(u*C-4)*Real.sqrt d := by
      field_simp [hu.ne']
      ring
    rw [heq]
    exact hroot
  linarith

theorem plateau_whole_interval_cost (h : PlateauCostCertificateConditions) (i : Fin 2)
    {k : ℝ} (hk : k ∈ Icc (plateauCostLo i : ℝ) (plateauCostHi i : ℝ)) :
    4/(plateauCostU i : ℝ)+20/(3*(plateauCostU i : ℝ)*(plateauCostW i : ℝ))*
      Real.exp (realEval (plateauCostE i) k)/Real.sqrt (realEval (plateauCostD i) k) ≤ 4137/1000 := by
  have he := (h i).1.nonneg hk
  have hd := (h i).2.1.nonneg hk
  have hc := (h i).2.2.nonneg hk
  have he' : realEval (plateauCostE i) k ≤ 0 := by simpa [realEval] using he
  have hd' : 0 < realEval (plateauCostD i) k := by
    have hde : realEval (plateauCostD i-C (1/1000000)) k = realEval (plateauCostD i) k-1/1000000 := by
      simp [realEval,Polynomial.eval₂_sub]
    rw [hde] at hd
    linarith
  rw [plateauCostMargin_eval] at hc
  apply plateau_cost_of_taylor (d := realEval (plateauCostD i) k) (E := realEval (plateauCostE i) k)
  · fin_cases i <;> norm_num [plateauCostU]
  · fin_cases i <;> norm_num [plateauCostW]
  · fin_cases i <;> norm_num [plateauCostU]
  · exact hd'
  · exact he'
  · linarith

/-- Scalar entropy optimization in the spectral fourth moment. -/
theorem plateau_zeta_entropy {w ζ : ℝ} (hw : 0 < w) (hζ : 0 ≤ ζ) :
    Real.log (1+2*ζ)-w*ζ ≤ Real.log (2/w)-1+w/2 := by
  have hz : 0 < 1+2*ζ := by positivity
  have ht := Real.log_le_sub_one_of_pos (mul_pos (div_pos hw (by norm_num : (0:ℝ)<2)) hz)
  rw [Real.log_mul (by positivity) hz.ne',Real.log_div hw.ne' (by norm_num : (2:ℝ)≠0)] at ht
  rw [Real.log_div (by norm_num : (2:ℝ)≠0) hw.ne']
  nlinarith

/-- Exact optimization over every positive L, with no discretization. -/
theorem plateau_log_L_bound {L : ℝ} (hL : 0 < L) (C : ℝ) :
    Real.log L+C ≤ L*Real.exp (C-1) := by
  have h := Real.add_one_le_exp (Real.log L+C-1)
  rw [show Real.log L+C-1=Real.log L+(C-1) by ring,Real.exp_add,Real.exp_log hL] at h
  linarith

/-- The spectral fourth-moment entropy bound and retained determinant term
optimize to the explicit plateau cost for every K≥1. -/
theorem plateau_entropy_expression_bound {K u v w k d ζ : ℝ}
    (hK : 1 ≤ K) (hu : 0 < u) (hw : 0 < w) (hd : 0 < d) (hζ : 0 ≤ ζ) :
    Real.log ((5/3)*K^2*logParameter K*(1+2*ζ))+v-w*ζ-
      (plateauRealPsi u v w k+Real.log d)/2 ≤
        (u/2)*(4/u+20/(3*u*w)*Real.exp (plateauRealE u v w k)/Real.sqrt d)*logParameter K := by
  let L := logParameter K
  let G := plateauRealPsi u v w k+Real.log d
  let C := v-3+w/2+Real.log (10/(3*w))-G/2
  have hK0 : 0 < K := by linarith
  have hL : 0 < L := (zero_lt_one.trans_le (one_le_logParameter hK))
  have hz : 0 < 1+2*ζ := by positivity
  have hratio : 0 < 10/(3*w) := by positivity
  have hlog : Real.log ((5/3)*K^2*L*(1+2*ζ)) =
      Real.log (5/3)+2*Real.log K+Real.log L+Real.log (1+2*ζ) := by
    rw [Real.log_mul (by positivity) hz.ne',Real.log_mul (by positivity) hL.ne',
      Real.log_mul (by norm_num : (5/3:ℝ)≠0) (sq_pos_of_pos hK0).ne',Real.log_pow]
    ring
  have hconst : Real.log (5/3)+Real.log (2/w)=Real.log (10/(3*w)) := by
    rw [← Real.log_mul (by norm_num : (5/3:ℝ)≠0) (by positivity)]
    congr 1
    field_simp
    ring
  have hb : Real.log ((5/3)*K^2*L*(1+2*ζ))+v-w*ζ-G/2 ≤ 2*L+Real.log L+C := by
    rw [hlog]
    have hh := plateau_zeta_entropy hw hζ
    dsimp [C,L]
    rw [← hconst]
    dsimp [logParameter]
    linarith
  have hEL := plateau_log_L_bound hL C
  have hExp : Real.exp (C-1) = (10/(3*w))*Real.exp (plateauRealE u v w k)/Real.sqrt d := by
    have he : C-1=Real.log (10/(3*w))+plateauRealE u v w k-Real.log (Real.sqrt d) := by
      rw [Real.log_sqrt hd.le]
      dsimp [C,G,plateauRealPsi,plateauRealE]
      ring
    rw [he,Real.exp_sub,Real.exp_add,Real.exp_log hratio,Real.exp_log (Real.sqrt_pos.mpr hd)]
  rw [hExp] at hEL
  rw [add_assoc] at hb
  have hbound := hb.trans (add_le_add_left hEL (2*L))
  change Real.log ((5/3)*K^2*L*(1+2*ζ))+v-w*ζ-G/2 ≤ _
  convert hbound using 1
  dsimp [L]
  field_simp [hu.ne',hw.ne',(Real.sqrt_pos.mpr hd).ne']
  ring

/-- Retaining one eigenvalue exactly improves the determinant sum. -/
theorem plateau_retained_logdet {ι : Type*} [Fintype ι] (r : ι → ℝ) (top : ι)
    {u A v w c : ℝ} (h2 : ∑ i,r i^2=1)
    (hg : ∀ i, 0 ≤ plateauRealG u A v w c (r i)) :
    -u*(∑ i,r i)/2-(∑ i,Real.log (plateauRealD u A c (r i)))/2 ≤
      v-w*(∑ i,r i^4)-plateauRealG u A v w c (r top)/2 := by
  have hs := Finset.single_le_sum (s := Finset.univ) (fun i _ => hg i) (Finset.mem_univ top)
  have he : (∑ i,plateauRealG u A v w c (r i)) =
      u*(∑ i,r i)+2*v-2*w*(∑ i,r i^4)+(∑ i,Real.log (plateauRealD u A c (r i))) := by
    dsimp [plateauRealG,plateauRealPsi]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,h2,mul_one]
  rw [he] at hs
  linarith

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem plateau_normalized_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hF : frobenius R=1) (A c : ℝ) :
    lowerComparison R A c = (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)*
      Matrix.diagonal (fun i => hR.isHermitian.eigenvalues i+A*hR.isHermitian.eigenvalues i^2-
        c*hR.isHermitian.eigenvalues i^3)*star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  rw [lowerComparison_spectral hR,normalized_trace_square hR hF,hF]
  congr 2
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,div_one,mul_one]
    ring
  · simp [Matrix.diagonal,hij]

theorem plateau_weight_fourth_trace {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R=1) :
    Matrix.trace ((lowerWeight R)^2)=∑ i,hR.isHermitian.eigenvalues i^4 := by
  simp only [lowerWeight,normalized_trace_square hR hF,inv_one,one_smul]
  rw [pow_two (R^2)]
  rw [real_spectral_square hR.isHermitian,unitary_conjugate_mul,Matrix.diagonal_mul_diagonal,
    unitary_conjugate_trace,Matrix.trace_diagonal]
  congr 1
  ext i
  ring

/-- Actual centered Gaussian log-MGF with one largest resolvent eigenvalue retained. -/
theorem normalized_plateau_log_mgf {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R=1)
    {u A v w c : ℝ} (hu : 0 < u)
    (hprofile : LowerComparisonProfile (spectralMaximum R hR.isHermitian) A c)
    (hscalar : ∀ r ∈ Icc (0 : ℝ) (spectralMaximum R hR.isHermitian),
      0 < plateauRealD u A c r ∧ 0 ≤ plateauRealG u A v w c r) :
    Integrable (fun ω => Real.exp (u/(2*K^2)*(quadraticForm (lowerComparison R A c) X ω-
      K^2*Matrix.trace R))) μ ∧
    Real.log (∫ ω,Real.exp (u/(2*K^2)*(quadraticForm (lowerComparison R A c) X ω-
      K^2*Matrix.trace R)) ∂μ) ≤ v-w*Matrix.trace ((lowerWeight R)^2)-
        plateauRealG u A v w c (spectralMaximum R hR.isHermitian)/2 := by
  let U := hR.isHermitian.eigenvectorUnitary
  let r := hR.isHermitian.eigenvalues
  let B := lowerComparison R A c
  let lam := u/(2*K^2)
  have hP : (lowerComparison R A c).PosSemidef := lowerComparison_posSemidef hR (by simpa [hF] using hprofile)
  have hd (i : ι) : 0 < plateauRealD u A c (r i) :=
    (hscalar _ ⟨(hR.eigenvalues_pos i).le,eigenvalue_le_spectralMaximum hR.isHermitian i⟩).1
  have hh : 1-u • B = (U : Matrix ι ι ℝ)*Matrix.diagonal (fun i => plateauRealD u A c (r i))*
      star (U : Matrix ι ι ℝ) := by
    rw [show Matrix.diagonal (fun i => plateauRealD u A c (r i)) =
        1-u • Matrix.diagonal (fun i => r i+A*r i^2-c*r i^3) by
      ext i j
      by_cases hij : i=j <;> simp [Matrix.diagonal,plateauRealD,hij] <;> ring]
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,U.2.2,Matrix.mul_smul,
      smul_mul_assoc,← plateau_normalized_spectral hR hF]
  have hgap : (1-u • B).PosDef := by
    rw [hh]
    exact unitary_conjugate_posDef U _ (Matrix.PosDef.diagonal hd)
  have hdet : Matrix.det (1-u • B)=∏ i,plateauRealD u A c (r i) := by
    rw [hh,Matrix.det_mul_right_comm,U.2.2,one_mul,Matrix.det_diagonal]
  have hscale : 2*K^2*lam=u := by dsimp [lam]; field_simp
  have hgap' : (1-(2*K^2*lam) • B).PosDef := by rw [hscale]; exact hgap
  have hi := (quadratic_exponential_det_bound hsg hm B hP lam (by dsimp [lam]; positivity) hgap').1
  have hl := quadratic_log_mgf_le_logdet hsg hm B hP lam (by dsimp [lam]; positivity) hgap'
  rw [hscale,hdet,Real.log_prod Finset.univ _ (fun i _ => (hd i).ne')] at hl
  obtain ⟨top,_,htop⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty r
  have hr2 : ∑ i,r i^2=1 := by rw [← real_spectral_trace_square hR.isHermitian]; exact normalized_trace_square hR hF
  have hs := plateau_retained_logdet r top hr2 (fun i =>
    (hscalar _ ⟨(hR.eigenvalues_pos i).le,eigenvalue_le_spectralMaximum hR.isHermitian i⟩).2)
  have htop' : r top=spectralMaximum R hR.isHermitian := htop.symm
  rw [htop',← real_spectral_trace hR.isHermitian,← plateau_weight_fourth_trace hR hF] at hs
  have hpoint (ω : Ω) : Real.exp (lam*(quadraticForm B X ω-K^2*Matrix.trace R)) =
      Real.exp (-u*Matrix.trace R/2)*Real.exp (lam*quadraticForm B X ω) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [lam]
    field_simp
    <;> ring
  have hint : Integrable (fun ω => Real.exp (lam*(quadraticForm B X ω-K^2*Matrix.trace R))) μ := by
    simp_rw [hpoint]
    exact hi.const_mul _
  refine ⟨hint,?_⟩
  change Real.log (∫ ω,Real.exp (lam*(quadraticForm B X ω-K^2*Matrix.trace R)) ∂μ) ≤ _
  simp_rw [hpoint]
  rw [integral_const_mul,Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos hi).ne',Real.log_exp]
  linarith

theorem plateau_near_cost (h : PlateauCostCertificateConditions) {k : ℝ}
    (hk : k ∈ Icc (71/100 : ℝ) (147/200)) :
    4/(1207/1000)+20/(3*(1207/1000)*(26/25))*
      Real.exp (plateauRealE (1207/1000) (plateauV (plateauA k)) (26/25) k)/
      Real.sqrt (plateauRealD (1207/1000) (plateauA k) (17/10) k) ≤ (4137/1000 : ℝ) := by
  have hh := plateau_whole_interval_cost h (0 : Fin 2) (by simpa [plateauCostLo,plateauCostHi] using hk)
  have hE : realEval (plateauCostE (0 : Fin 2)) k =
      plateauRealE (1207/1000) (plateauV (plateauA k)) (26/25) k := by
    norm_num [realEval,plateauCostE,plateauCostV,plateauCostA,plateauCostU,plateauCostW,
      plateauRealE,plateauA,plateauV,Polynomial.eval₂_pow,Polynomial.eval₂_sub]
    ring
  have hD : realEval (plateauCostD (0 : Fin 2)) k =
      plateauRealD (1207/1000) (plateauA k) (17/10) k := by
    norm_num [realEval,plateauCostD,plateauCostA,plateauCostU,plateauCostC,
      plateauRealD,plateauA,Polynomial.eval₂_pow,Polynomial.eval₂_sub]
    all_goals try ring
    all_goals simp_all
  norm_num [plateauCostU,plateauCostW] at hh ⊢
  rwa [hE,hD] at hh

theorem plateau_far_cost (h : PlateauCostCertificateConditions) {k : ℝ}
    (hk : k ∈ Icc (147/200 : ℝ) 1) :
    4/(6/5)+20/(3*(6/5)*(21/20))*Real.exp (plateauRealE (6/5) (27/16) (21/20) k)/
      Real.sqrt (plateauRealD (6/5) (74/55) (19/10) k) ≤ (4137/1000 : ℝ) := by
  have hh := plateau_whole_interval_cost h (1 : Fin 2) (by simpa [plateauCostLo,plateauCostHi] using hk)
  have hE : realEval (plateauCostE (1 : Fin 2)) k = plateauRealE (6/5) (27/16) (21/20) k := by
    norm_num [realEval,plateauCostE,plateauCostV,plateauCostA,plateauCostU,plateauCostW,
      plateauRealE,Polynomial.eval₂_pow,Polynomial.eval₂_sub]
    ring
  have hD : realEval (plateauCostD (1 : Fin 2)) k = plateauRealD (6/5) (74/55) (19/10) k := by
    norm_num [realEval,plateauCostD,plateauCostA,plateauCostU,plateauCostC,
      plateauRealD,Polynomial.eval₂_pow,Polynomial.eval₂_sub]
    all_goals try ring
    all_goals simp_all
  norm_num [plateauCostU,plateauCostW] at hh ⊢
  rwa [hE,hD] at hh

/-- The actual plateau comparison matrix satisfies its mixed-cost bound. -/
theorem normalized_plateau_mixed_cost {X : Ω → ι → ℝ} {K C : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R=1)
    {u A v w c : ℝ} (hu : 0 < u) (hw : 0 < w)
    (hprofile : LowerComparisonProfile (spectralMaximum R hR.isHermitian) A c)
    (hscalar : ∀ r ∈ Icc (0 : ℝ) (spectralMaximum R hR.isHermitian),
      0 < plateauRealD u A c r ∧ 0 ≤ plateauRealG u A v w c r)
    (hcost : 4/u+20/(3*u*w)*Real.exp (plateauRealE u v w (spectralMaximum R hR.isHermitian))/
      Real.sqrt (plateauRealD u A c (spectralMaximum R hR.isHermitian)) ≤ C) :
    (∫ ω,quadraticForm (lowerWeight R) X ω*quadraticForm (lowerComparison R A c) X ω ∂μ)-
      K^2*Matrix.trace R ≤ C*K^2*logParameter K := by
  let P := lowerWeight R
  let B := lowerComparison R A c
  let lam := u/(2*K^2)
  let ζ := Matrix.trace (P^2)
  have hK0 : 0 < K := by linarith
  have hL : 0 < logParameter K := zero_lt_one.trans_le (one_le_logParameter hK)
  have hP : P.PosSemidef := by
    have he : P=R^2 := by simp [P,lowerWeight,normalized_trace_square hR hF]
    rw [he,pow_two]
    simpa only [hR.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self R
  have htr : Matrix.trace P=1 := by simp [P,lowerWeight,normalized_trace_square hR hF]
  have hζ : 0 ≤ ζ := by dsimp [ζ]; rw [real_spectral_trace_square hP.isHermitian]; positivity
  have hT := hsg.quadratic_memLp_two P
  have hQ := hsg.quadratic_memLp_two B
  have hT0 := quadraticForm_nonneg hP X
  have hTi := hT.integrable (by norm_num)
  have hMean := (hiso.quadratic_mean P).trans htr
  have hEnt := entropy_integrable_of_second_moment hT.aestronglyMeasurable.aemeasurable hT0 hT.integrable_sq
  have hPow : Integrable (fun ω => quadraticForm P X ω^(2:ℝ)) μ := by
    simpa only [Real.rpow_two] using hT.integrable_sq
  have hPowPos := positive_real_moment_of_mean_one hT0 hMean hPow (by norm_num : (0:ℝ)<2)
  have hRenyi := renyi_entropy_bound hT0 hTi hMean hEnt hPow hPowPos (by norm_num : (1:ℝ)<2)
  simp only [Real.rpow_two] at hRenyi hPowPos
  norm_num at hRenyi
  have hSecond := quadratic_second_lower_general_strong hsg hiso hK P hP htr
  have hD : (∫ ω,quadraticForm P X ω*Real.log (quadraticForm P X ω) ∂μ) ≤
      Real.log ((5/3)*K^2*logParameter K*(1+2*ζ)) :=
    hRenyi.trans (Real.log_le_log hPowPos hSecond)
  have hExp := normalized_plateau_log_mgf hsg hiso.measurable hK0 hR hF hu hprofile hscalar
  have hWZ : Integrable (fun ω => quadraticForm P X ω*(lam*(quadraticForm B X ω-K^2*Matrix.trace R))) μ := by
    have hi := ((hT.integrable_mul hQ).sub (hTi.mul_const (K^2*Matrix.trace R))).const_mul lam
    convert hi using 1
    ext ω
    simp only [Pi.sub_apply,Pi.mul_apply]
    ring
  have h := weighted_entropy (Filter.Eventually.of_forall hT0) hTi hMean hEnt hWZ hExp.1
  have hid : (∫ ω,quadraticForm P X ω*(lam*(quadraticForm B X ω-K^2*Matrix.trace R)) ∂μ) =
      lam*((∫ ω,quadraticForm P X ω*quadraticForm B X ω ∂μ)-K^2*Matrix.trace R) := by
    have hp (ω : Ω) : quadraticForm P X ω*(lam*(quadraticForm B X ω-K^2*Matrix.trace R)) =
        lam*(quadraticForm P X ω*quadraticForm B X ω-quadraticForm P X ω*(K^2*Matrix.trace R)) := by ring
    simp_rw [hp]
    rw [integral_const_mul,integral_sub (f := fun ω => quadraticForm P X ω*quadraticForm B X ω)
      (hT.integrable_mul hQ) (hTi.mul_const _),integral_mul_const,hMean,one_mul]
  rw [hid] at h
  have hk0 : 0 ≤ spectralMaximum R hR.isHermitian :=
    (hR.eigenvalues_pos (Classical.arbitrary ι)).le.trans (eigenvalue_le_spectralMaximum hR.isHermitian _)
  have hd := (hscalar _ ⟨hk0,le_rfl⟩).1
  have hopt := plateau_entropy_expression_bound (u := u) (v := v) (k := spectralMaximum R hR.isHermitian)
    hK hu hw hd hζ
  have hscalarcost := mul_le_mul_of_nonneg_right hcost (mul_nonneg (show 0 ≤ u/2 by positivity) hL.le)
  have hright : (∫ ω,quadraticForm P X ω*Real.log (quadraticForm P X ω) ∂μ)+
      Real.log (∫ ω,Real.exp (lam*(quadraticForm B X ω-K^2*Matrix.trace R)) ∂μ) ≤
        (u/2)*C*logParameter K := by
    dsimp [plateauRealG] at hExp
    dsimp [ζ] at hopt
    dsimp [ζ] at hζ
    dsimp [P,B,lam] at *
    nlinarith only [hD,hExp.2,hopt,hscalarcost]
  have hfinal := h.trans hright
  have hpos : 0 < lam := by dsimp [lam]; positivity
  have heq : lam*(C*K^2*logParameter K)=(u/2)*C*logParameter K := by dsimp [lam]; field_simp; ring
  rw [← heq] at hfinal
  exact (mul_le_mul_left hpos).mp hfinal

/-- The complete concentrated-spectrum comparison in the printed plateau lemma.
Only the explicit finite rational certificate conditions remain external. -/
theorem normalized_lower_plateau {X : Ω → ι → ℝ} {K : ℝ}
    (hcert : PlateauCertificateConditions) (hcost : PlateauCostCertificateConditions)
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R=1)
    (hk : 71/100 ≤ spectralMaximum R hR.isHermitian) :
    ∃ B : Matrix ι ι ℝ, B.PosDef ∧
      (∀ x : ι → ℝ, x ⬝ᵥ (lowerWeight R *ᵥ x) ≤ (1+x ⬝ᵥ (B *ᵥ x))*lowerShift R hR x) ∧
      (∫ ω,quadraticForm (lowerWeight R) X ω*quadraticForm B X ω ∂μ)-K^2*Matrix.trace R ≤
        (4137/1000)*K^2*logParameter K := by
  let k := spectralMaximum R hR.isHermitian
  have hk1 : k ≤ 1 := by simpa only [hF] using spectralMaximum_le_frobenius hR.posSemidef
  by_cases hnear : k ≤ 147/200
  · have hkr : k ∈ Icc (71/100 : ℝ) (147/200) := ⟨hk,hnear⟩
    have hprofile := plateau_near_profile hkr
    have hpos := plateau_comparison_posDef hR hF (A := plateauA k) (c := 17/10)
      (by norm_num) (by have ha := (plateauA_bounds hkr).1; linarith)
    refine ⟨lowerComparison R (plateauA k) (17/10),hpos,?_,?_⟩
    · intro x
      exact lowerShift_quadratic_comparison hR x (by simpa only [hF,div_one] using hprofile)
    · apply normalized_plateau_mixed_cost hsg hiso hK hR hF
        (u := 1207/1000) (v := plateauV (plateauA k)) (w := 26/25) (by norm_num) (by norm_num) hprofile
      · intro r hr
        exact plateau_near_scalar hcert (plateauA_bounds hkr) ⟨hr.1,hr.2.trans hnear⟩
      · exact plateau_near_cost hcost hkr
  · have hfar : (147/200 : ℝ) ≤ k := (le_of_not_ge hnear)
    have hprofile := plateau_far_profile k
    have hpos := plateau_comparison_posDef hR hF (A := 74/55) (c := 19/10)
      (by norm_num) (by norm_num)
    refine ⟨lowerComparison R (74/55) (19/10),hpos,?_,?_⟩
    · intro x
      exact lowerShift_quadratic_comparison hR x (by simpa only [hF,div_one] using hprofile)
    · apply normalized_plateau_mixed_cost hsg hiso hK hR hF
        (u := 6/5) (v := 27/16) (w := 21/20) (by norm_num) (by norm_num) hprofile
      · intro r hr
        exact plateau_far_scalar hcert ⟨hr.1,hr.2.trans hk1⟩
      · exact plateau_far_cost hcost ⟨hfar,hk1⟩

end
end SingularValueBounds.KL
