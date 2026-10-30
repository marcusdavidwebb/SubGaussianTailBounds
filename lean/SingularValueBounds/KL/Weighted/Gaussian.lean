import SingularValueBounds.QuadraticForms.Bounds

/-!
# Gaussian comparison and averaging for the KL proof

This module supplies the determinant and log-determinant forms of supplementary
Lemma S1.3 (`app:gaussian-comparison`), a normalization of the comparison attributed
there to Hsu--Kakade--Zhang, Remark 2.3. The analytic comparison is reused from
`QuadraticForms.GaussianComparison`; no independence of coordinates is assumed.
The Gaussian averaging argument also accepts any supplied homogeneous directional
fourth-moment bound, as used in supplementary `eq:app-low-Tmoment`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators ENNReal NNReal

namespace SingularValueBounds.KL

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ} {K : ℝ}

variable [DecidableEq ι]

/-- A scalar spectral shift has precisely the expected eigenvalue factors. -/
theorem det_one_sub_smul_eq_prod (B : Matrix ι ι ℝ) (hB : B.IsHermitian) (c : ℝ) :
    Matrix.det (1 - c • B) = ∏ i, (1 - c * hB.eigenvalues i) := by
  let U := hB.eigenvectorUnitary
  have hd : Matrix.diagonal (fun i => 1 - c * hB.eigenvalues i) =
      1 - c • Matrix.diagonal hB.eigenvalues := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, ← Matrix.diagonal_sub]
    rfl
  have he : (U : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => 1 - c * hB.eigenvalues i) *
        star (U : Matrix ι ι ℝ) = 1 - c • B := by
    rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, U.2.2,
      Matrix.mul_smul, smul_mul_assoc]
    rw [← real_spectral_decomposition hB]
  rw [← he, Matrix.det_mul_right_comm, U.2.2, one_mul, Matrix.det_diagonal]

/-- The Gaussian eigenvalue product equals the inverse square root of the
spectral-shift determinant. Every square root has a strictly positive argument. -/
theorem gaussian_product_eq_inv_sqrt_det (B : Matrix ι ι ℝ)
    (hB : B.IsHermitian) (c : ℝ)
    (hf : ∀ i, 0 < 1 - c * hB.eigenvalues i) :
    (∏ i, (Real.sqrt (1 - c * hB.eigenvalues i))⁻¹) =
      (Real.sqrt (Matrix.det (1 - c • B)))⁻¹ := by
  rw [det_one_sub_smul_eq_prod B hB c]
  have hs (s : Finset ι) :
      (∏ i ∈ s, (Real.sqrt (1 - c * hB.eigenvalues i))⁻¹) =
        (Real.sqrt (∏ i ∈ s, (1 - c * hB.eigenvalues i)))⁻¹ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, ih]
      rw [Real.sqrt_mul (hf a).le, mul_inv_rev, mul_comm]
  exact hs Finset.univ

/-- Supplementary Lemma S1.3 (`app:gaussian-comparison`), retaining the
integrability conclusion from the original eigenvalue-product comparison. -/
theorem quadratic_exponential_det_bound (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) (B : Matrix ι ι ℝ) (hB : B.PosSemidef)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hgap : (1 - (2 * K ^ 2 * lam) • B).PosDef) :
    Integrable (fun ω => Real.exp (lam * quadraticForm B X ω)) μ ∧
      (∫ ω, Real.exp (lam * quadraticForm B X ω) ∂μ) ≤
        (Real.sqrt (Matrix.det (1 - (2 * K ^ 2 * lam) • B)))⁻¹ := by
  have hf : ∀ i, 0 < 1 - 2 * K ^ 2 * lam * hB.isHermitian.eigenvalues i := by
    intro i
    simpa only [one_smul] using eigenvalue_gap_pos hB.isHermitian (by simpa only [one_smul] using hgap) i
  have h := quadratic_exponential_bound hsg hm B hB lam hlam hf
  rw [gaussian_product_eq_inv_sqrt_det B hB.isHermitian (2 * K ^ 2 * lam) hf] at h
  exact h

/-- The logarithmic Gaussian comparison, for subsequent weighted entropy
arguments. The determinant is positive by the supplied positive-definite gap. -/
theorem quadratic_log_mgf_le_logdet (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) (B : Matrix ι ι ℝ) (hB : B.PosSemidef)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hgap : (1 - (2 * K ^ 2 * lam) • B).PosDef) :
    Real.log (∫ ω, Real.exp (lam * quadraticForm B X ω) ∂μ) ≤
      -(Real.log (Matrix.det (1 - (2 * K ^ 2 * lam) • B))) / 2 := by
  obtain ⟨hi, hb⟩ := quadratic_exponential_det_bound hsg hm B hB lam hlam hgap
  have hlog := Real.log_le_log (integral_exp_pos hi) hb
  rw [Real.log_inv, Real.log_sqrt hgap.det_pos.le] at hlog
  simpa only [neg_div] using hlog

/-- The same logarithmic comparison written as a sum of scalar eigenvalue
costs. Positivity of every factor is derived from the matrix gap. -/
theorem quadratic_log_mgf_le_sum (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) (B : Matrix ι ι ℝ) (hB : B.PosSemidef)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hgap : (1 - (2 * K ^ 2 * lam) • B).PosDef) :
    Real.log (∫ ω, Real.exp (lam * quadraticForm B X ω) ∂μ) ≤
      -(∑ i, Real.log (1 - 2 * K ^ 2 * lam * hB.isHermitian.eigenvalues i)) / 2 := by
  have hf : ∀ i, 0 < 1 - 2 * K ^ 2 * lam * hB.isHermitian.eigenvalues i := by
    intro i
    simpa only [one_smul] using eigenvalue_gap_pos hB.isHermitian (by simpa only [one_smul] using hgap) i
  have h := quadratic_log_mgf_le_logdet hsg hm B hB lam hlam hgap
  rwa [det_one_sub_smul_eq_prod B hB.isHermitian (2 * K ^ 2 * lam),
    Real.log_prod (fun i _ => (hf i).ne')] at h

set_option maxHeartbeats 800000 in
/-- Gaussian averaging gives the stronger diagonal quadratic moment bound,
which retains the sum of squared eigenvalues needed at the endpoint. -/
theorem diagonal_quadratic_second_of_directional_fourth (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) {m4 : ℝ} (hm4 : 0 ≤ m4)
    (hfourth : ∀ u : ι → ℝ, (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) ≤ m4 * (u ⬝ᵥ u) ^ 2)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    3 * (∫ ω, (∑ i, b i * (X ω i) ^ 2) ^ 2 ∂μ) ≤
      m4 * ((∑ i, b i) ^ 2 + 2 * ∑ i, (b i) ^ 2) := by
  classical
  let a : ι → ℝ := fun i => Real.sqrt (b i)
  have ha : ∀ i, (a i) ^ 2 = b i := fun i => Real.sq_sqrt (hb i)
  let F : Ω → (ι → ℝ) → ℝ := fun ω g => (∑ i, a i * g i * X ω i) ^ 4
  have hF : Measurable (Function.uncurry F) := by
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
      ENNReal.ofReal (m4 * (∑ i, b i * (g i) ^ 2) ^ 2) := by
    have hi : Integrable (F · g) μ := by
      simpa only [F, dotProduct] using hsg.directional_integrable_pow (fun i => a i * g i) 4
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => by dsimp [F]; positivity))]
    apply ENNReal.ofReal_le_ofReal
    have h := hfourth (fun i => a i * g i)
    simpa only [F, dotProduct, ← sq, mul_pow, ha] using h
  have hbound :
      (∫⁻ ω, ENNReal.ofReal (3 * (∑ i, b i * (X ω i) ^ 2) ^ 2) ∂μ) ≤
        ENNReal.ofReal (m4 *
          ((∑ i, b i) ^ 2 + 2 * ∑ i, (b i) ^ 2)) := by
    calc
      _ = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (F ω g) ∂standardGaussian ι ∂μ := by
        apply lintegral_congr
        intro ω
        exact (hid ω).symm
      _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (F ω g) ∂μ ∂standardGaussian ι :=
        lintegral_lintegral_swap hF.ennreal_ofReal.aemeasurable
      _ ≤ ∫⁻ g, ENNReal.ofReal (m4 *
          (∑ i, b i * (g i) ^ 2) ^ 2) ∂standardGaussian ι := lintegral_mono hinner
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((standardGaussian_quadratic_sq_integrable b).const_mul (m4))
          (Filter.Eventually.of_forall (fun _ => mul_nonneg hm4 (sq_nonneg _))),
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

/-- The stronger quadratic moment inequality underlying both moment
conclusions of Lemma 4.2. -/
theorem quadratic_second_of_directional_fourth (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) {m4 : ℝ} (hm4 : 0 ≤ m4)
    (hfourth : ∀ u : ι → ℝ, (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) ≤ m4 * (u ⬝ᵥ u) ^ 2)
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    3 * (∫ ω, quadraticForm B X ω ^ 2 ∂μ) ≤
      m4 * ((Matrix.trace B) ^ 2 + 2 * Matrix.trace (B ^ 2)) := by
  let U := hB.isHermitian.eigenvectorUnitary
  let b := hB.isHermitian.eigenvalues
  have hq : quadraticForm B X = fun ω =>
      ∑ i, b i * ((star (U : Matrix ι ι ℝ) *ᵥ X ω) i) ^ 2 := by
    funext ω
    change X ω ⬝ᵥ (B *ᵥ X ω) = _
    rw [real_spectral_decomposition hB.isHermitian, quadratic_conjugate_diagonal]
    simp only [U, b, mul_comm]
  have hm' : Measurable (fun ω => star (U : Matrix ι ι ℝ) *ᵥ X ω) := by
    change Measurable (fun ω i => ∑ j, (star (U : Matrix ι ι ℝ)) i j * X ω j)
    fun_prop
  have hf' : ∀ u : ι → ℝ,
      (∫ ω, (u ⬝ᵥ (star (U : Matrix ι ι ℝ) *ᵥ X ω)) ^ 4 ∂μ) ≤
        m4 * (u ⬝ᵥ u) ^ 2 := by
    intro u
    simpa only [dot_unitary_star_mulVec, unitary_mulVec_dot] using
      hfourth ((U : Matrix ι ι ℝ) *ᵥ u)
  have h := diagonal_quadratic_second_of_directional_fourth (hsg.unitary U)
    hm' hm4 hf' b hB.eigenvalues_nonneg
  simp_rw [← show ∀ ω, quadraticForm B X ω =
    ∑ i, b i * ((star (U : Matrix ι ι ℝ) *ᵥ X ω) i) ^ 2 from fun ω => congrFun hq ω] at h
  simpa only [real_spectral_trace hB.isHermitian,
    real_spectral_trace_square hB.isHermitian, b] using h

/-- The trace-one specialization retains the spectral square trace. -/
theorem quadratic_second_trace_one_of_directional_fourth
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X)
    {m4 : ℝ} (hm4 : 0 ≤ m4)
    (hfourth : ∀ u : ι → ℝ, (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) ≤ m4 * (u ⬝ᵥ u) ^ 2)
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (htrace : Matrix.trace B = 1) :
    3 * (∫ ω, quadraticForm B X ω ^ 2 ∂μ) ≤
      m4 * (1 + 2 * Matrix.trace (B ^ 2)) := by
  simpa only [htrace, one_pow] using
    quadratic_second_of_directional_fourth hsg hm hm4 hfourth B hB

end
end SingularValueBounds.KL
