import SingularValueBounds.Shifts.UpperTail
import SingularValueBounds.Shifts.UpperMatrixUpdate
import SingularValueBounds.KL.Weighted.Gaussian

/-! # Exact upper shifts and tails (supplementary S1.6.1)
The matrix `upperTailMatrix` is the supplement's `B_h`, rather than the old
criterion `B_h / h`. The definitions include `h=0`. -/
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The normalising denominator `tr(R R_h)`. -/
def upperTailDenominator (R : Matrix ι ι ℝ) (h : ℝ) : ℝ :=
  Matrix.trace (R * upperResolvent R h)

/-- The exact quadratic tail matrix of supplementary `eq:app-up-event`. -/
def upperTailMatrix (R : Matrix ι ι ℝ) (h : ℝ) : Matrix ι ι ℝ :=
  h • upperResolvent R h + (upperTailDenominator R h)⁻¹ • upperResolvent R h ^ 2

/-- The normalised resolvent-square weights in S1.6.1. -/
def upperTailWeight (r : ι → ℝ) (h : ℝ) (i : ι) : ℝ :=
  (r i ^ 2 / (1 + h * r i)) / (∑ j, r j ^ 2 / (1 + h * r j))

theorem upperTailDenominator_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 ≤ h) :
    upperTailDenominator R h =
      ∑ i, hR.isHermitian.eigenvalues i ^ 2 / (1 + h * hR.isHermitian.eigenvalues i) := by
  unfold upperTailDenominator
  rw [upperResolvent_spectral hR hh]
  conv_lhs => arg 1; lhs; rw [real_spectral_decomposition hR.isHermitian]
  rw [
    unitary_conjugate_mul, Matrix.diagonal_mul_diagonal,
    unitary_conjugate_trace, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem upperTailDenominator_pos {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 ≤ h) : 0 < upperTailDenominator R h := by
  rw [upperTailDenominator_spectral hR hh]
  exact Finset.sum_pos (fun i _ => div_pos (sq_pos_of_pos (hR.eigenvalues_pos i))
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hR.eigenvalues_pos i).le))) Finset.univ_nonempty

/-- For positive shifts the old criterion is exactly `B_h/h`. -/
theorem upperTailMatrix_eq_smul_criterion {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 < h) : upperTailMatrix R h = h • upperCriterion R h := by
  have hd : Matrix.trace (R - upperResolvent R h) = h * upperTailDenominator R h := by
    rw [upperResolvent_trace_drop hR hh.le, upperTailDenominator_spectral hR hh.le]
  unfold upperTailMatrix upperCriterion
  rw [hd, smul_add, smul_smul]
  congr 1
  congr 1
  field_simp [hh.ne', (upperTailDenominator_pos hR hh.le).ne']

/-- Exact quadratic event, including the strict inequality of the printed tail. -/
theorem upperShift_tail_event {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : ι → ℝ) {h : ℝ} (hh : 0 < h) :
    h < upperShift R hR x ↔ h < x ⬝ᵥ (upperTailMatrix R h *ᵥ x) := by
  rw [upperTailMatrix_eq_smul_criterion hR hh, Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [upperShift_lt_iff hR x hh]
  constructor <;> intro hq <;> nlinarith

/-- The quadratic identity at the chosen exact shift, with the zero row handled. -/
theorem upperShift_tail_equation {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    x ⬝ᵥ (upperTailMatrix R (upperShift R hR x) *ᵥ x) = upperShift R hR x := by
  by_cases hx : x = 0
  · subst x
    simp [upperShift_zero]
  · rw [upperTailMatrix_eq_smul_criterion hR (upperShift_pos hR hx),
      Matrix.smul_mulVec, dotProduct_smul, upperShift_equation hR hx, smul_eq_mul, mul_one]

/-- Every tail weight is positive, their sum is one, and each is at most one. -/
theorem upperTailWeight_properties {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {h : ℝ} (hh : 0 ≤ h) :
    (∀ i, 0 < upperTailWeight r h i) ∧ (∑ i, upperTailWeight r h i) = 1 ∧
      ∀ i, upperTailWeight r h i ≤ 1 := by
  have hd : ∀ i, 0 < 1 + h * r i := fun i => add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le)
  have hS : 0 < ∑ i, r i ^ 2 / (1 + h * r i) :=
    Finset.sum_pos (fun i _ => div_pos (sq_pos_of_pos (hr i)) (hd i)) Finset.univ_nonempty
  refine ⟨fun i => div_pos (div_pos (sq_pos_of_pos (hr i)) (hd i)) hS, ?_, ?_⟩
  · simp only [upperTailWeight, ← Finset.sum_div, div_self hS.ne']
  · intro i
    apply (div_le_one hS).2
    exact Finset.single_le_sum (fun j _ => div_nonneg (sq_nonneg _) (hd j).le)
      (Finset.mem_univ i)

/-- Spectral-shape bound for the time-dependent weights. -/
theorem upperTailWeight_le_shape {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {h M : ℝ} (hh : 0 ≤ h) (hM : ∀ i, r i ≤ M) (i : ι) :
    upperTailWeight r h i ≤ M ^ 2 / (∑ j, r j ^ 2) := by
  have hMi : 0 < M := (hr i).trans_le (hM i)
  have hD : 0 < 1 + h * M := by positivity
  have hdi : ∀ j, 0 < 1 + h * r j := fun j => add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr j).le)
  have hS : 0 < ∑ j, r j ^ 2 :=
    Finset.sum_pos (fun j _ => sq_pos_of_pos (hr j)) Finset.univ_nonempty
  have hT : 0 < ∑ j, r j ^ 2 / (1 + h * r j) :=
    Finset.sum_pos (fun j _ => div_pos (sq_pos_of_pos (hr j)) (hdi j)) Finset.univ_nonempty
  have hl : (∑ j, r j ^ 2) / (1 + h * M) ≤ ∑ j, r j ^ 2 / (1 + h * r j) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro j _
    exact div_le_div_of_nonneg_left (sq_nonneg _) (hdi j)
      (by nlinarith [mul_le_mul_of_nonneg_left (hM j) hh])
  have hu : r i ^ 2 / (1 + h * r i) ≤ M ^ 2 / (1 + h * M) := by
    apply (div_le_div_iff₀ (hdi i) hD).2
    have hsq : r i ^ 2 ≤ M ^ 2 := by nlinarith [hr i, hM i]
    have hm := mul_nonneg (sub_nonneg.mpr (hM i))
      (mul_nonneg hh (mul_nonneg (hr i).le hMi.le))
    nlinarith
  unfold upperTailWeight
  calc
    _ ≤ (M ^ 2 / (1 + h * M)) / ((∑ j, r j ^ 2) / (1 + h * M)) :=
      div_le_div₀ (by positivity) hu (div_pos hS hD) hl
    _ = _ := by field_simp

/-- Supplementary determinant tail bound for arbitrary `0<q<1`. -/
theorem upperTailMatrix_determinant {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h q : ℝ} (hh : 0 < h) (hq : 0 < q) (hq1 : q < 1) :
    ((1 : Matrix ι ι ℝ) - q • upperTailMatrix R h).PosDef ∧
      Real.exp (-(q * h * Matrix.trace R)) * (1 - q) ≤
        Matrix.det ((1 : Matrix ι ι ℝ) - q • upperTailMatrix R h) := by
  have ht := upperCriterion_determinant_bound hR (mul_pos hq hh) (by nlinarith : q * h < h)
  rw [upperTailMatrix_eq_smul_criterion hR hh, smul_smul]
  simpa [mul_div_cancel_right₀ q hh.ne', mul_assoc] using ht


/-- The scalar eigenvalues of the supplement's exact tail matrix. -/
def upperTailEigenvalue (r : ι → ℝ) (h : ℝ) (i : ι) : ℝ :=
  (h*r i+upperTailWeight r h i)/(1+h*r i)

/-- The logarithmic chord estimate used for the spectral-shape refinement. -/
theorem upper_log_chord {p q s : ℝ} (hp : 0 ≤ p) (hps : p ≤ s)
    (hs : 0 < s) (hq : 0 ≤ q) (hqs : q*s < 1) :
    (p/s)*Real.log (1-q*s) ≤ Real.log (1-q*p) := by
  have hw : p/s ≤ 1 := (div_le_one hs).2 hps
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (show (1:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1-q*s ∈ Set.Ioi 0 by change 0 < 1-q*s; linarith)
    (show 0 ≤ 1-p/s by linarith) (div_nonneg hp hs.le) (by ring : (1-p/s)+p/s = 1)
  simp only [smul_eq_mul,Real.log_one,mul_zero,zero_add] at hc
  convert! hc using 1
  congr 1
  field_simp [hs.ne'] <;> ring

/-- A bound on the sum and maximum of positive weights gives a determinant
bound. This includes the endpoint `q=1` whenever the shape is strictly below one. -/
theorem upper_weight_product_shape {p : ι → ℝ} {q s : ℝ}
    (hp : ∀ i,0 ≤ p i) (hpsum : ∑ i,p i ≤ 1) (hps : ∀ i,p i ≤ s)
    (hs : 0 < s) (hq : 0 ≤ q) (hqs : q*s < 1) :
    Real.exp (Real.log (1-q*s)/s) ≤ ∏ i,(1-q*p i) := by
  have hpos : ∀ i,0 < 1-q*p i := fun i => by
    have hm := mul_le_mul_of_nonneg_left (hps i) hq
    linarith
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => upper_log_chord (hp i) (hps i) hs hq hqs)
  have he : (∑ i,(p i/s)*Real.log (1-q*s)) = (∑ i,p i)/s*Real.log (1-q*s) := by
    rw [← Finset.sum_mul, ← Finset.sum_div]
  rw [he] at hl
  have hlog : Real.log (1-q*s) ≤ 0 := Real.log_nonpos (by linarith) (by nlinarith)
  have hsdiv : (∑ i,p i)/s ≤ 1/s := div_le_div_of_nonneg_right hpsum hs.le
  have hbase := mul_le_mul_of_nonpos_right hsdiv hlog
  have hh : Real.log (1-q*s)/s ≤ ∑ i,Real.log (1-q*p i) := by
    simpa only [one_div_mul_eq_div] using hbase.trans hl
  have hm := Real.exp_le_exp.2 hh
  rw [Real.exp_sum] at hm
  simpa only [Real.exp_log (hpos _)] using hm

theorem upper_first_factor_exp_rate {r h q : ℝ} (hr : 0 < r)
    (hh : 0 ≤ h) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.exp (-(q*h*r)) ≤ (1+(1-q)*h*r)/(1+h*r) := by
  have hdt : 0 < 1+q*h*r := by positivity
  have hdh : 0 < 1+h*r := by positivity
  have hexp : Real.exp (-(q*h*r)) ≤ 1/(1+q*h*r) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le hdt
      (show 1+q*h*r ≤ Real.exp (q*h*r) by linarith [Real.add_one_le_exp (q*h*r)])
  apply hexp.trans
  apply (div_le_div_iff₀ hdt hdh).2
  have hm := mul_nonneg (mul_nonneg hq (sub_nonneg.mpr hq1)) (sq_nonneg (h*r))
  nlinarith


/-- Spectral determinant estimate with the full shape parameter. -/
theorem upper_tail_spectral_shape {r : ι → ℝ} (hr : ∀ i,0 < r i)
    {h q s : ℝ} (hh : 0 ≤ h) (hq : 0 < q) (hq1 : q ≤ 1)
    (hs : 0 < s) (hps : ∀ i,upperTailWeight r h i ≤ s) (hqs : q*s < 1) :
    (∀ i,0 < 1-q*upperTailEigenvalue r h i) ∧
      Real.exp (-(q*h*∑ i,r i))*Real.exp (Real.log (1-q*s)/s) ≤
        ∏ i,(1-q*upperTailEigenvalue r h i) := by
  let f := fun i => (1+(1-q)*h*r i)/(1+h*r i)
  let v := fun i => upperTailWeight r h i/(1+(1-q)*h*r i)
  obtain ⟨hp,hpsum,_⟩ := upperTailWeight_properties hr hh
  have hden : ∀ i,1 ≤ 1+(1-q)*h*r i := fun i => by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hq1) hh) (hr i).le]
  have hv : ∀ i,0 ≤ v i := fun i => div_nonneg (hp i).le (by linarith [hden i])
  have hvp : ∀ i,v i ≤ upperTailWeight r h i := fun i => by
    exact div_le_self (hp i).le (hden i)
  have hvs : ∀ i,v i ≤ s := fun i => (hvp i).trans (hps i)
  have hsum : ∑ i,v i ≤ 1 := by
    calc
      _ ≤ ∑ i,upperTailWeight r h i := Finset.sum_le_sum (fun i _ => hvp i)
      _ = 1 := hpsum
  have hvpos : ∀ i,0 < 1-q*v i := fun i => by
    have hm := mul_le_mul_of_nonneg_left (hvs i) hq.le
    linarith
  have hf : ∀ i,Real.exp (-(q*h*r i)) ≤ f i := fun i =>
    upper_first_factor_exp_rate (hr i) hh hq.le hq1
  have hfpos : ∀ i,0 < f i := fun i => (Real.exp_pos _).trans_le (hf i)
  have hfac (i : ι) : 1-q*upperTailEigenvalue r h i = f i*(1-q*v i) := by
    dsimp [upperTailEigenvalue,f,v]
    have hd : 1+(1-q)*h*r i ≠ 0 := by linarith [hden i]
    have hdr : 1+h*r i ≠ 0 := (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le)).ne'
    field_simp (disch := nlinarith [hden i, mul_nonneg hh (hr i).le]) <;> ring
  constructor
  · intro i
    rw [hfac]
    exact mul_pos (hfpos i) (hvpos i)
  · simp_rw [hfac]
    rw [Finset.prod_mul_distrib]
    apply mul_le_mul _ (upper_weight_product_shape hv hsum hvs hs hq.le hqs)
      (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ => (hfpos i).le))
    have hp := Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => (Real.exp_pos (-(q*h*r i))).le) (fun i _ => hf i)
    rw [← Real.exp_sum] at hp
    convert! hp using 1
    congr 1
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]


/-- The supplement's eigenvalue expression agrees with its actual matrix. -/
theorem upperTailMatrix_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 < h) :
    upperTailMatrix R h = (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (upperTailEigenvalue hR.isHermitian.eigenvalues h) *
        star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  rw [upperTailMatrix_eq_smul_criterion hR hh,upperCriterion_spectral hR hh.le,
    ← Matrix.smul_mul,← Matrix.mul_smul]
  congr 2
  rw [← Matrix.diagonal_smul]
  apply congrArg Matrix.diagonal
  funext i
  change h*(hR.isHermitian.eigenvalues i/(1+h*hR.isHermitian.eigenvalues i)+
    (hR.isHermitian.eigenvalues i/(1+h*hR.isHermitian.eigenvalues i))^2/
      (h*∑ j,hR.isHermitian.eigenvalues j^2/(1+h*hR.isHermitian.eigenvalues j))) = _
  have hd : 0 < ∑ j,hR.isHermitian.eigenvalues j^2/(1+h*hR.isHermitian.eigenvalues j) :=
    Finset.sum_pos (fun j _ => div_pos (sq_pos_of_pos (hR.eigenvalues_pos j))
      (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh.le (hR.eigenvalues_pos j).le))) Finset.univ_nonempty
  have hi : 1+h*hR.isHermitian.eigenvalues i ≠ 0 :=
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh.le (hR.eigenvalues_pos i).le)).ne'
  unfold upperTailEigenvalue upperTailWeight
  field_simp [hh.ne',hd.ne',hi] <;> ring

private theorem upper_prod_inv_sqrt_log {a : ι → ℝ} (ha : ∀ i,0 < a i) :
    (∏ i,(Real.sqrt (a i))⁻¹) = Real.exp (-(∑ i,Real.log (a i))/2) := by
  have he (i : ι) : (Real.sqrt (a i))⁻¹ = Real.exp (-Real.log (a i)/2) := by
    rw [← Real.exp_log (inv_pos.mpr (Real.sqrt_pos.2 (ha i))),Real.log_inv,
      Real.log_sqrt (ha i).le]
    congr 1
    ring
  simp_rw [he]
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div,Finset.sum_neg_distrib]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Equation `eq:app-up-tail-family`, using the actual exact upper root. -/
theorem upperShift_tail_family {X : Ω → ι → ℝ} {K b q u : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hcap : K ^ 2 * Matrix.trace R ≤ b)
    (hb : b < 1) (hq : 0 < q) (hq1 : q < 1) (hu : 0 ≤ u) :
    μ.real {ω | u < (1 - b) * upperShift R hR (X ω)} ≤
      (Real.sqrt (1 - q))⁻¹ * Real.exp (-(q * u / (2 * K ^ 2))) := by
  have hK2 : 0 < K ^ 2 := sq_pos_of_pos hK
  have ht : Matrix.trace R ≤ b / K ^ 2 := (le_div_iff₀ hK2).2 (by nlinarith)
  have hid : K ^ 2 * (b / K ^ 2) = b := by field_simp
  have hh := upperShift_tail hsg hm hK hR ht (by rw [hid]; linarith)
    (by positivity : 0 < q / 2) (by linarith : q / 2 < 1 / 2) u hu
  rw [hid] at hh
  convert! hh using 1 <;> congr 2 <;> ring
/-- Chernoff interpretation of a proved scalar spectral log-determinant bound.
This is an analytic helper; numerical certificates contain no such premise. -/
theorem upperShift_tail_of_spectral_logdet {X : Ω → ι → ℝ} {K h q A : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hh : 0 < h) (hq : 0 < q)
    (hgap : ∀ i,0 < 1-q*upperTailEigenvalue hR.isHermitian.eigenvalues h i)
    (hlog : -(∑ i,Real.log (1-q*upperTailEigenvalue hR.isHermitian.eigenvalues h i)) ≤
      q*h*Matrix.trace R+A) :
    μ.real {ω | h < upperShift R hR (X ω)} ≤
      Real.exp (A/2-q*h*(1-K^2*Matrix.trace R)/(2*K^2)) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let b := upperTailEigenvalue hR.isHermitian.eigenvalues h
  let lam := q/(2*K^2)
  have hK2 : 0 < K^2 := sq_pos_of_pos hK
  have hlam : 0 < lam := div_pos hq (by positivity)
  have hlamid : 2*K^2*lam = q := by dsimp [lam];field_simp
  have hb : ∀ i,0 ≤ b i := by
    intro i
    have hi := hR.eigenvalues_pos i
    have hp := (upperTailWeight_properties hR.eigenvalues_pos hh.le).1 i
    dsimp [b,upperTailEigenvalue]
    positivity
  have hmg := unitary_quadratic_exponential_bound hsg hm U b hb lam hlam.le
    (by simpa only [hlamid] using hgap)
  rw [← upperTailMatrix_spectral hR hh] at hmg
  have hmark := measure_ge_le_exp_mul_mgf (μ := μ)
    (X := quadraticForm (upperTailMatrix R h) X) h hlam.le hmg.1
  have hevent : μ.real {ω | h < upperShift R hR (X ω)} ≤
      μ.real {ω | h ≤ quadraticForm (upperTailMatrix R h) X ω} := by
    apply measureReal_mono
    · exact fun ω hω => ((upperShift_tail_event hR (X ω) hh).1 hω).le
    · exact measure_ne_top _ _
  have hprod := upper_prod_inv_sqrt_log hgap
  have hbound : (∏ i,(Real.sqrt (1-2*K^2*lam*b i))⁻¹) ≤
      Real.exp ((q*h*Matrix.trace R+A)/2) := by
    rw [hlamid]
    rw [hprod]
    exact Real.exp_le_exp.2 (by linarith)
  calc
    _ ≤ Real.exp (-lam*h)*(∫ ω,Real.exp (lam*quadraticForm (upperTailMatrix R h) X ω) ∂μ) :=
      hevent.trans (by simpa only [mgf] using hmark)
    _ ≤ Real.exp (-lam*h)*Real.exp ((q*h*Matrix.trace R+A)/2) :=
      mul_le_mul_of_nonneg_left (hmg.2.trans hbound) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      field_simp
      ring

/-- Shape-sensitive normalized upper tail, including its endpoint rate. -/
theorem upperShift_tail_shape {X : Ω → ι → ℝ} {K b q s u : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hcap : K^2*Matrix.trace R ≤ b) (hb : b < 1)
    (hq : 0 < q) (hq1 : q ≤ 1) (hs : 0 < s) (hqs : q*s < 1)
    (hshape : ∀ h,0 ≤ h → ∀ i,upperTailWeight hR.isHermitian.eigenvalues h i ≤ s)
    (hu : 0 ≤ u) :
    μ.real {ω | u < (1-b)*upperShift R hR (X ω)} ≤
      Real.exp (-Real.log (1-q*s)/(2*s)-q*u/(2*K^2)) := by
  have hK2 : 0 < K^2 := sq_pos_of_pos hK
  have hb0 : 0 < 1-b := by linarith
  rcases hu.eq_or_lt with rfl | hu
  · have hlog : Real.log (1-q*s) ≤ 0 := Real.log_nonpos (by linarith) (by nlinarith [mul_nonneg hq.le hs.le])
    have he : 1 ≤ Real.exp (-Real.log (1-q*s)/(2*s)) :=
      Real.one_le_exp_iff.2 (div_nonneg (by linarith) (by positivity))
    simpa using (measureReal_le_one (μ := μ)).trans he
  let h := u/(1-b)
  have hh : 0 < h := div_pos hu hb0
  obtain ⟨hgap,hdet⟩ := upper_tail_spectral_shape hR.eigenvalues_pos hh.le hq hq1 hs
    (hshape h hh.le) hqs
  have hp : 0 < ∏ i,(1-q*upperTailEigenvalue hR.isHermitian.eigenvalues h i) :=
    Finset.prod_pos (fun i _ => hgap i)
  have hl := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hdet
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp,
    Real.log_prod (fun i _ => (hgap i).ne')] at hl
  have htr := real_spectral_trace hR.isHermitian
  have hlog : -(∑ i,Real.log (1-q*upperTailEigenvalue hR.isHermitian.eigenvalues h i)) ≤
      q*h*Matrix.trace R-Real.log (1-q*s)/s := by rw [htr];linarith
  have ht := upperShift_tail_of_spectral_logdet hsg hm hK hR hh hq hgap hlog
  have hevent : {ω | u < (1-b)*upperShift R hR (X ω)} =
      {ω | h < upperShift R hR (X ω)} := by
    ext ω
    change u < (1-b)*upperShift R hR (X ω) ↔ u/(1-b) < upperShift R hR (X ω)
    rw [div_lt_iff₀ hb0,mul_comm]
  rw [hevent]
  apply ht.trans
  apply Real.exp_le_exp.2
  have hm := mul_le_mul_of_nonneg_left (show 1-b ≤ 1-K^2*Matrix.trace R by linarith) hh.le
  have he : h*(1-b) = u := by dsimp [h];field_simp
  have hmul := mul_le_mul_of_nonneg_left hm hq.le
  have hdiv := div_le_div_of_nonneg_right hmul (show 0 ≤ 2*K^2 by positivity)
  rw [he] at hdiv
  have hdiv' : q*u/(2*K^2) ≤ q*h*(1-K^2*Matrix.trace R)/(2*K^2) := by
    convert! hdiv using 1 <;> ring
  have heq : -(Real.log (1-q*s)/s)/2 = -Real.log (1-q*s)/(2*s) := by ring
  rw [heq]
  linarith

end
end SingularValueBounds.KL
