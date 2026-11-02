import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import SingularValueBounds.QuadraticForms.Basic

/-!
# Gaussian integration for quadratic forms

The auxiliary Gaussian measure is explicitly constructed as a finite product
of standard real Gaussian measures. All exponential identities below are
derived from the Gaussian density and finite-product integration.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators ENNReal NNReal

namespace SingularValueBounds

noncomputable section

/-- An explicit independent standard Gaussian vector. -/
def standardGaussian (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

instance standardGaussian_probability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (standardGaussian ι) := by
  unfold standardGaussian
  infer_instance

theorem standardGaussian_integral_exp (t : ℝ) :
    (∫ x : ℝ, Real.exp (t * x) ∂gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
  simpa [mgf] using mgf_gaussianReal (μ := 0) (v := 1)
    (X := id) (Measure.map_id) t

theorem standardGaussian_integrable_exp (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gaussianReal 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [standardGaussian_integral_exp]
  exact (Real.exp_pos _).ne'

theorem standardGaussian_integral_exp_sq (s : ℝ) (hs : 0 < 1 - 2 * s) :
    (∫ x : ℝ, Real.exp (s * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * s))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  calc
    (∫ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (s * x ^ 2)) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-((1 - 2 * s) / 2) * x ^ 2) := by
      simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
        smul_eq_mul, mul_assoc, ← Real.exp_add, ← integral_const_mul]
      congr 1
      funext x
      congr 2
      ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / ((1 - 2 * s) / 2)) := by
      rw [integral_gaussian]
    _ = (Real.sqrt (1 - 2 * s))⁻¹ := by
      rw [show Real.pi / ((1 - 2 * s) / 2) =
        (2 * Real.pi) / (1 - 2 * s) by field_simp]
      rw [Real.sqrt_div (by positivity), div_eq_mul_inv]
      rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne', one_mul]

theorem standardGaussian_integral_prod {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) :
    (∫ g, ∏ i, f i (g i) ∂standardGaussian ι) =
      ∏ i, ∫ x, f i x ∂gaussianReal 0 1 := by
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  haveI : SigmaFinite (volume : Measure ℝ) :=
    inferInstanceAs (SigmaFinite (gaussianReal 0 1))
  exact integral_fintype_prod_eq_prod f

theorem standardGaussian_integral_exp_sum {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∫ g, Real.exp (∑ i, a i * g i) ∂standardGaussian ι) =
      Real.exp ((∑ i, (a i) ^ 2) / 2) := by
  simp_rw [Real.exp_sum]
  rw [standardGaussian_integral_prod (fun i x => Real.exp (a i * x))]
  simp_rw [standardGaussian_integral_exp]
  rw [← Real.exp_sum, ← Finset.sum_div]

theorem standardGaussian_integrable_exp_sum {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Integrable (fun g => Real.exp (∑ i, a i * g i)) (standardGaussian ι) := by
  apply Integrable.of_integral_ne_zero
  rw [standardGaussian_integral_exp_sum]
  exact (Real.exp_pos _).ne'

theorem standardGaussian_integral_exp_sum_sq {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 0 < 1 - 2 * s i) :
    (∫ g, Real.exp (∑ i, s i * (g i) ^ 2) ∂standardGaussian ι) =
      ∏ i, (Real.sqrt (1 - 2 * s i))⁻¹ := by
  simp_rw [Real.exp_sum]
  rw [standardGaussian_integral_prod (fun i x => Real.exp (s i * x ^ 2))]
  apply Finset.prod_congr rfl
  intro i _
  exact standardGaussian_integral_exp_sq (s i) (hs i)

theorem standardGaussian_integrable_exp_sum_sq {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (hs : ∀ i, 0 < 1 - 2 * s i) :
    Integrable (fun g => Real.exp (∑ i, s i * (g i) ^ 2)) (standardGaussian ι) := by
  apply Integrable.of_integral_ne_zero
  rw [standardGaussian_integral_exp_sum_sq s hs]
  exact Finset.prod_ne_zero_iff.2 (fun i _ => inv_ne_zero (Real.sqrt_pos.2 (hs i)).ne')

set_option maxHeartbeats 1000000 in
/-- The Gaussian comparison for a diagonal positive semidefinite quadratic
form. Tonelli is applied to nonnegative integrands before integrability of the
quadratic exponential has been established. -/
theorem diagonal_quadratic_exponential_bound {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ι → ℝ} {K : ℝ} (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) (hf : ∀ i, 0 < 1 - 2 * K ^ 2 * t * b i) :
    Integrable (fun ω => Real.exp (t * ∑ i, b i * (X ω i) ^ 2)) μ ∧
      (∫ ω, Real.exp (t * ∑ i, b i * (X ω i) ^ 2) ∂μ) ≤
        ∏ i, (Real.sqrt (1 - 2 * K ^ 2 * t * b i))⁻¹ := by
  classical
  let a : ι → ℝ := fun i => Real.sqrt (2 * t * b i)
  have ha : ∀ i, (a i) ^ 2 = 2 * t * b i :=
    fun i => Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) ht) (hb i))
  let F : Ω → (ι → ℝ) → ℝ := fun ω g => Real.exp (∑ i, a i * g i * X ω i)
  have hF : Measurable (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    fun_prop
  have hid (ω : Ω) :
      (∫⁻ g, ENNReal.ofReal (F ω g) ∂standardGaussian ι) =
        ENNReal.ofReal (Real.exp (t * ∑ i, b i * (X ω i) ^ 2)) := by
    have heq : (fun g => F ω g) =
        (fun g => Real.exp (∑ i, (a i * X ω i) * g i)) := by
      funext g
      change Real.exp (∑ i, a i * g i * X ω i) = _
      apply congrArg Real.exp
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [show ∀ g, F ω g = Real.exp (∑ i, (a i * X ω i) * g i) from
      fun g => congrFun heq g]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (standardGaussian_integrable_exp_sum (fun i => a i * X ω i))
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
      standardGaussian_integral_exp_sum]
    apply congrArg ENNReal.ofReal
    apply congrArg Real.exp
    simp only [mul_pow, ha, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hinner (g : ι → ℝ) :
      (∫⁻ ω, ENNReal.ofReal (F ω g) ∂μ) ≤
        ENNReal.ofReal (Real.exp (∑ i, (K ^ 2 * t * b i) * (g i) ^ 2)) := by
    have hi : Integrable (F · g) μ := by
      simpa only [F, dotProduct, one_mul] using
        hsg.integrable_exp (fun i => a i * g i) 1
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
    apply ENNReal.ofReal_le_ofReal
    calc
      (∫ ω, F ω g ∂μ) ≤
          Real.exp (K ^ 2 * ((fun i => a i * g i) ⬝ᵥ (fun i => a i * g i)) / 2) := by
        simpa only [F, dotProduct, one_mul, one_pow] using
          hsg.mgf_bound (fun i => a i * g i) 1
      _ = _ := by
        congr 1
        simp only [dotProduct, ← sq, mul_pow, ha, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hfs : ∀ i, 0 < 1 - 2 * (K ^ 2 * t * b i) := by
    intro i
    nlinarith only [hf i]
  have hbound :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (t * ∑ i, b i * (X ω i) ^ 2)) ∂μ) ≤
        ENNReal.ofReal (∏ i, (Real.sqrt (1 - 2 * K ^ 2 * t * b i))⁻¹) := by
    calc
      _ = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (F ω g) ∂standardGaussian ι ∂μ := by
        apply lintegral_congr
        intro ω
        exact (hid ω).symm
      _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (F ω g) ∂μ ∂standardGaussian ι :=
        lintegral_lintegral_swap hF.ennreal_ofReal.aemeasurable
      _ ≤ ∫⁻ g, ENNReal.ofReal (Real.exp
          (∑ i, (K ^ 2 * t * b i) * (g i) ^ 2)) ∂standardGaussian ι :=
        lintegral_mono hinner
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          (standardGaussian_integrable_exp_sum_sq (fun i => K ^ 2 * t * b i) hfs)
          (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
          standardGaussian_integral_exp_sum_sq _ hfs]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        congr 3
        ring
  have hint : Integrable (fun ω => Real.exp (t * ∑ i, b i * (X ω i) ^ 2)) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (show Measurable (fun ω => Real.exp (t * ∑ i, b i * (X ω i) ^ 2)) from
        by fun_prop).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))).1
    exact ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound

/-- The same bound in an arbitrary supplied orthogonal eigenbasis. -/
theorem unitary_quadratic_exponential_bound {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ι → ℝ} {K : ℝ} (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) (U : Matrix.unitaryGroup ι ℝ)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) (hf : ∀ i, 0 < 1 - 2 * K ^ 2 * t * b i) :
    Integrable (fun ω => Real.exp (t * quadraticForm
      ((U : Matrix ι ι ℝ) * Matrix.diagonal b * star (U : Matrix ι ι ℝ)) X ω)) μ ∧
      (∫ ω, Real.exp (t * quadraticForm
        ((U : Matrix ι ι ℝ) * Matrix.diagonal b * star (U : Matrix ι ι ℝ)) X ω) ∂μ) ≤
          ∏ i, (Real.sqrt (1 - 2 * K ^ 2 * t * b i))⁻¹ := by
  have hm' : Measurable (fun ω => star (U : Matrix ι ι ℝ) *ᵥ X ω) := by
    change Measurable (fun ω i => ∑ j, (star (U : Matrix ι ι ℝ)) i j * X ω j)
    fun_prop
  simpa only [quadraticForm, quadratic_conjugate_diagonal, mul_comm (b _)] using
    diagonal_quadratic_exponential_bound (hsg.unitary U) hm' b hb t ht hf

/-- The quadratic exponential comparison from the directional sub-Gaussian
MGF assumption, expressed using the eigenvalues of the given matrix. -/
theorem quadratic_exponential_bound {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ι → ℝ} {K : ℝ} (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) (B : Matrix ι ι ℝ) (hB : B.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t)
    (hf : ∀ i, 0 < 1 - 2 * K ^ 2 * t * hB.isHermitian.eigenvalues i) :
    Integrable (fun ω => Real.exp (t * quadraticForm B X ω)) μ ∧
      (∫ ω, Real.exp (t * quadraticForm B X ω) ∂μ) ≤
        ∏ i, (Real.sqrt (1 - 2 * K ^ 2 * t * hB.isHermitian.eigenvalues i))⁻¹ := by
  have hs : B = (hB.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal hB.isHermitian.eigenvalues *
        star (hB.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hB.isHermitian.spectral_theorem
  have h := unitary_quadratic_exponential_bound hsg hm hB.isHermitian.eigenvectorUnitary
    hB.isHermitian.eigenvalues hB.eigenvalues_nonneg t ht hf
  rwa [← hs] at h

end
end SingularValueBounds
