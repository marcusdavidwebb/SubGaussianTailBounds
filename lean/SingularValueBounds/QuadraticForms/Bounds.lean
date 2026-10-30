import SingularValueBounds.QuadraticForms.GaussianMoments

/-!
# Quadratic-form moment bounds from the original hypotheses

This file derives the fourth-moment and endpoint variance conclusions of
Lemma 4.2 by averaging the proved directional moment bound over an explicit
independent standard Gaussian vector.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators ENNReal NNReal

namespace SingularValueBounds

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ} {K : ℝ}

theorem directional_fourth_of_unit (hsg : SubGaussianMGF μ X K)
    (hiso : CentredIsotropic μ X) (hK : 1 ≤ K) (u : ι → ℝ) (hu : u ⬝ᵥ u = 1) :
    (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) ≤ fourthMomentConstant K := by
  have hs : HasSubgaussianMGF (fun ω => u ⬝ᵥ X ω) ⟨K ^ 2, sq_nonneg K⟩ μ := by
    simpa only [hu, mul_one] using hsg.directional u
  have hm : (∫ ω, (u ⬝ᵥ X ω) ^ 2 ∂μ) = 1 := (hiso.second_moment u).trans hu
  unfold fourthMomentConstant
  split_ifs with hK1
  · subst K
    change HasSubgaussianMGF (fun ω => u ⬝ᵥ X ω) (NNReal.mk ((1 : ℝ) ^ 2) _) μ at hs
    exact scalar_fourth_unit (by simpa using hs) hm
  · exact scalar_fourth_general hs hK hm

/-- The scalar estimate scales homogeneously to every direction, including
the zero direction. -/
theorem directional_fourth (hsg : SubGaussianMGF μ X K)
    (hiso : CentredIsotropic μ X) (hK : 1 ≤ K) (u : ι → ℝ) :
    (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) ≤ fourthMomentConstant K * (u ⬝ᵥ u) ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  have hu2 : 0 < u ⬝ᵥ u := by
    simpa only [star_trivial] using Matrix.dotProduct_star_self_pos_iff.mpr hu
  let r := Real.sqrt (u ⬝ᵥ u)
  have hr : 0 < r := Real.sqrt_pos.2 hu2
  have hr2 : r ^ 2 = u ⬝ᵥ u := Real.sq_sqrt hu2.le
  let v : ι → ℝ := r⁻¹ • u
  have hv : v ⬝ᵥ v = 1 := by
    simp only [v, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    calc
      r⁻¹ * (r⁻¹ * (u ⬝ᵥ u)) = (u ⬝ᵥ u) / r ^ 2 := by ring
      _ = 1 := by rw [hr2, div_self hu2.ne']
  have hpoint (ω : Ω) : (u ⬝ᵥ X ω) ^ 4 = r ^ 4 * (v ⬝ᵥ X ω) ^ 4 := by
    simp only [v, smul_dotProduct, smul_eq_mul, mul_pow]
    field_simp [hr.ne']
  calc
    _ = r ^ 4 * (∫ ω, (v ⬝ᵥ X ω) ^ 4 ∂μ) := by
      simp_rw [hpoint]
      rw [integral_const_mul]
    _ ≤ r ^ 4 * fourthMomentConstant K :=
      mul_le_mul_of_nonneg_left (directional_fourth_of_unit hsg hiso hK v hv) (by positivity)
    _ = fourthMomentConstant K * (u ⬝ᵥ u) ^ 2 := by
      rw [← hr2]
      ring

set_option maxHeartbeats 800000 in
/-- Gaussian averaging gives the stronger diagonal quadratic moment bound,
which retains the sum of squared eigenvalues needed at the endpoint. -/
theorem diagonal_quadratic_second_strong (hsg : SubGaussianMGF μ X K)
    (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    3 * (∫ ω, (∑ i, b i * (X ω i) ^ 2) ^ 2 ∂μ) ≤
      fourthMomentConstant K * ((∑ i, b i) ^ 2 + 2 * ∑ i, (b i) ^ 2) := by
  classical
  let a : ι → ℝ := fun i => Real.sqrt (b i)
  have ha : ∀ i, (a i) ^ 2 = b i := fun i => Real.sq_sqrt (hb i)
  let F : Ω → (ι → ℝ) → ℝ := fun ω g => (∑ i, a i * g i * X ω i) ^ 4
  have hF : Measurable (Function.uncurry F) := by
    have hm := hiso.measurable
    dsimp [F, Function.uncurry]
    fun_prop
  have hid (ω : Ω) : (∫⁻ g, ENNReal.ofReal (F ω g) ∂standardGaussian ι) =
      ENNReal.ofReal (3 * (∑ i, b i * (X ω i) ^ 2) ^ 2) := by
    have hp (g : ι → ℝ) : F ω g = (∑ i, (a i * X ω i) * g i) ^ 4 := by
      dsimp only [F]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hp]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (standardGaussian_linear_pow_integrable (fun i => a i * X ω i) 4)
      (Filter.Eventually.of_forall (fun _ => by positivity)),
      (standardGaussian_linear_moments (fun i => a i * X ω i)).2]
    simp only [mul_pow, ha]
  have hinner (g : ι → ℝ) : (∫⁻ ω, ENNReal.ofReal (F ω g) ∂μ) ≤
      ENNReal.ofReal (fourthMomentConstant K * (∑ i, b i * (g i) ^ 2) ^ 2) := by
    have hi : Integrable (F · g) μ := by
      simpa only [F, dotProduct] using hsg.directional_integrable_pow (fun i => a i * g i) 4
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => by dsimp [F]; positivity))]
    apply ENNReal.ofReal_le_ofReal
    have h := directional_fourth hsg hiso hK (fun i => a i * g i)
    simpa only [F, dotProduct, ← sq, mul_pow, ha] using h
  have hM : 0 ≤ fourthMomentConstant K := (fourthMomentConstant_pos hK).le
  have hbound :
      (∫⁻ ω, ENNReal.ofReal (3 * (∑ i, b i * (X ω i) ^ 2) ^ 2) ∂μ) ≤
        ENNReal.ofReal (fourthMomentConstant K *
          ((∑ i, b i) ^ 2 + 2 * ∑ i, (b i) ^ 2)) := by
    calc
      _ = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (F ω g) ∂standardGaussian ι ∂μ := by
        apply lintegral_congr
        intro ω
        exact (hid ω).symm
      _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (F ω g) ∂μ ∂standardGaussian ι :=
        lintegral_lintegral_swap hF.ennreal_ofReal.aemeasurable
      _ ≤ ∫⁻ g, ENNReal.ofReal (fourthMomentConstant K *
          (∑ i, b i * (g i) ^ 2) ^ 2) ∂standardGaussian ι := lintegral_mono hinner
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((standardGaussian_quadratic_sq_integrable b).const_mul (fourthMomentConstant K))
          (Filter.Eventually.of_forall (fun _ => mul_nonneg hM (sq_nonneg _))),
          integral_const_mul, standardGaussian_quadratic_second]
  have hint : Integrable (fun ω => (∑ i, b i * (X ω i) ^ 2) ^ 2) μ := by
    have h := (hsg.quadratic_memLp_two (Matrix.diagonal b)).integrable_sq
    have he : quadraticForm (Matrix.diagonal b) X = fun ω => ∑ i, b i * (X ω i) ^ 2 := by
      funext ω
      simp only [quadraticForm, Matrix.mulVec_diagonal, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rwa [he] at h
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul 3)
    (Filter.Eventually.of_forall (fun _ => by positivity)), integral_const_mul] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound

variable [DecidableEq ι]

/-- The stronger quadratic moment inequality underlying both moment
conclusions of Lemma 4.2. -/
theorem quadratic_second_strong (hsg : SubGaussianMGF μ X K)
    (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    3 * (∫ ω, quadraticForm B X ω ^ 2 ∂μ) ≤
      fourthMomentConstant K * ((Matrix.trace B) ^ 2 + 2 * Matrix.trace (B ^ 2)) := by
  let U := hB.isHermitian.eigenvectorUnitary
  let b := hB.isHermitian.eigenvalues
  have hq : quadraticForm B X = fun ω =>
      ∑ i, b i * ((star (U : Matrix ι ι ℝ) *ᵥ X ω) i) ^ 2 := by
    funext ω
    change X ω ⬝ᵥ (B *ᵥ X ω) = _
    rw [real_spectral_decomposition hB.isHermitian, quadratic_conjugate_diagonal]
    simp only [U, b, mul_comm]
  have h := diagonal_quadratic_second_strong (hsg.unitary U) (hiso.unitary U) hK b
    hB.eigenvalues_nonneg
  simp_rw [← show ∀ ω, quadraticForm B X ω =
    ∑ i, b i * ((star (U : Matrix ι ι ℝ) *ᵥ X ω) i) ^ 2 from fun ω => congrFun hq ω] at h
  simpa only [real_spectral_trace hB.isHermitian,
    real_spectral_trace_square hB.isHermitian, b] using h

theorem quadratic_second_moment (hsg : SubGaussianMGF μ X K)
    (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    (∫ ω, quadraticForm B X ω ^ 2 ∂μ) ≤
      fourthMomentConstant K * (Matrix.trace B) ^ 2 := by
  have hs : Matrix.trace (B ^ 2) ≤ (Matrix.trace B) ^ 2 := by
    rw [real_spectral_trace hB.isHermitian, real_spectral_trace_square hB.isHermitian]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hB.eigenvalues_nonneg i)
  have h := quadratic_second_strong hsg hiso hK B hB
  have hM := fourthMomentConstant_pos hK
  nlinarith [mul_le_mul_of_nonneg_left hs hM.le]

theorem quadratic_endpoint_variance (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    (∫ ω, (quadraticForm B X ω - Matrix.trace B) ^ 2 ∂μ) ≤
      2 * Matrix.trace (B ^ 2) := by
  have h := quadratic_second_strong hsg hiso (by norm_num) B hB
  norm_num [fourthMomentConstant] at h
  have hqi := hiso.quadratic_integrable B
  have hq2i := (hsg.quadratic_memLp_two B).integrable_sq
  have he : (∫ ω, (quadraticForm B X ω - Matrix.trace B) ^ 2 ∂μ) =
      (∫ ω, quadraticForm B X ω ^ 2 ∂μ) - (Matrix.trace B) ^ 2 := by
    calc
      _ = ∫ ω, quadraticForm B X ω ^ 2 -
          2 * Matrix.trace B * quadraticForm B X ω + (Matrix.trace B) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = _ := by
        rw [integral_add (f := fun ω => quadraticForm B X ω ^ 2 -
            2 * Matrix.trace B * quadraticForm B X ω)
          (hq2i.sub (hqi.const_mul (2 * Matrix.trace B))) (integrable_const _),
          integral_sub hq2i (hqi.const_mul _), integral_const_mul,
          hiso.quadratic_mean]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        ring
  rw [he]
  linarith

/-- The quadratic moments used by both exponential shifts follow from the
original centering, isotropy and directional sub-Gaussian MGF assumptions. -/
theorem quadraticFormEstimates_of_subGaussian (hK : 1 ≤ K)
    (hiso : CentredIsotropic μ X) (hsg : SubGaussianMGF μ X K) :
    QuadraticFormEstimates μ X K := by
  constructor
  · intro B _
    exact hsg.quadratic_memLp_two B
  · intro B _
    exact hiso.quadratic_mean B
  · exact quadratic_second_moment hsg hiso hK
  · intro hK1 B hB
    subst K
    exact quadratic_endpoint_variance hsg hiso B hB

end
end SingularValueBounds
