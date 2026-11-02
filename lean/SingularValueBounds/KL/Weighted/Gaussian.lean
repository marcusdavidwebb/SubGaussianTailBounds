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
  rw [Finset.prod_inv_distrib, Real.sqrt_prod Finset.univ (fun i _ => (hf i).le)]

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

omit [DecidableEq ι] in
/-- Gaussian averaging gives the stronger diagonal quadratic moment bound,
which retains the sum of squared eigenvalues needed at the endpoint. -/
theorem diagonal_quadratic_second_of_directional_fourth (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) {m4 : ℝ} (hm4 : 0 ≤ m4)
    (hfourth : ∀ u : ι → ℝ, (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) ≤ m4 * (u ⬝ᵥ u) ^ 2)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    3 * (∫ ω, (∑ i, b i * (X ω i) ^ 2) ^ 2 ∂μ) ≤
      m4 * ((∑ i, b i) ^ 2 + 2 * ∑ i, (b i) ^ 2) := by
  exact SingularValueBounds.diagonal_quadratic_second_of_directional_fourth hsg hm hm4 hfourth b hb

/-- The stronger quadratic moment inequality underlying both moment
conclusions of Lemma 4.2. -/
theorem quadratic_second_of_directional_fourth (hsg : SubGaussianMGF μ X K)
    (hm : Measurable X) {m4 : ℝ} (hm4 : 0 ≤ m4)
    (hfourth : ∀ u : ι → ℝ, (∫ ω, (u ⬝ᵥ X ω) ^ 4 ∂μ) ≤ m4 * (u ⬝ᵥ u) ^ 2)
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    3 * (∫ ω, quadraticForm B X ω ^ 2 ∂μ) ≤
      m4 * ((Matrix.trace B) ^ 2 + 2 * Matrix.trace (B ^ 2)) := by
  exact SingularValueBounds.quadratic_second_of_directional_fourth hsg hm hm4 hfourth B hB

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
