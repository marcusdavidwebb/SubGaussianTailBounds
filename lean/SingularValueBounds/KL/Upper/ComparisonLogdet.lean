import SingularValueBounds.KL.Upper.ComparisonNormMatrices
import SingularValueBounds.KL.Upper.NormDeterminants

/-! # The norm determinant bounds for the actual comparison matrix

This module applies the finite Taylor certificate interface to the actual
matrix determinant. All diagonalization, positivity and logarithm/product
identities are proved in Lean.
-/
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The scale-invariant determinant quantity `J` for the actual matrix `C`. -/
def upperComparisonMatrixLogdet (R : Matrix ι ι ℝ) : ℝ :=
  -Real.log (Matrix.det (upperComparisonNormalizedGap R)) -
    2 * (Matrix.trace R / frobenius R)

/-- The scalar log-determinant formula is an equality for the actual matrix. -/
theorem upperComparisonMatrixLogdet_eq_normalized {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    upperComparisonMatrixLogdet R = normalizedLogdet (upperNormalizedSpectrum R hR) := by
  obtain ⟨hx, h2⟩ := upperNormalizedSpectrum_properties hR
  have hfactor : ∀ i, 0 < 1 - 2 * normalizedUpperEigenvalue (upperNormalizedSpectrum R hR) i := by
    intro i
    have hb := normalized_upper_eigenvalue_lt hx h2 i
    linarith
  unfold upperComparisonMatrixLogdet normalizedLogdet
  rw [upperComparisonNormalizedGap_det hR,
    Real.log_prod Finset.univ _ (fun i _ => (hfactor i).ne'),
    trace_div_frobenius_eq_normalized_sum hR, Finset.sum_neg_distrib]

/-- The general norm-based `J₀` bound, with the finite numerical premise
explicit and every matrix/logarithm argument proved. -/
theorem upperComparisonMatrixLogdet_J0
    (h : NormDeterminantCertificateConditions) {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    upperComparisonMatrixLogdet R ≤ -2 * upperComparisonShapeMean R hR +
      (671 / 100) * (1 - upperComparisonShapeMean R hR ^ 2 -
        upperComparisonShapeMean R hR ^ 2 * (1 - upperComparisonShapeMean R hR) ^ 2) := by
  rw [upperComparisonMatrixLogdet_eq_normalized hR]
  obtain ⟨hx, h2⟩ := upperNormalizedSpectrum_properties hR
  exact normalized_logdet_J0 h hx h2

/-- The improved `J₁` bound for concentrated spectra, under the same two
finite Taylor comparisons. -/
theorem upperComparisonMatrixLogdet_J1
    (h : NormDeterminantCertificateConditions) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hκ : (37 : ℝ) / 40 ≤ spectralRatio R hR) :
    upperComparisonMatrixLogdet R ≤ -2 * upperComparisonShapeMean R hR +
      (563 / 100) * (1 - upperComparisonShapeMean R hR ^ 2 -
        upperComparisonShapeMean R hR ^ 2 * (1 - upperComparisonShapeMean R hR) ^ 2) := by
  rw [upperComparisonMatrixLogdet_eq_normalized hR]
  obtain ⟨hx, h2⟩ := upperNormalizedSpectrum_properties hR
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty hR.isHermitian.eigenvalues
  have hk' : (37 : ℝ) / 40 ≤ upperNormalizedSpectrum R hR k := by
    change (37 : ℝ) / 40 ≤ hR.isHermitian.eigenvalues k / frobenius R
    change (37 : ℝ) / 40 ≤ spectralMaximum R hR.isHermitian / frobenius R at hκ
    simpa only [spectralMaximum, hk] using hκ
  exact normalized_logdet_J1 h hx h2 hk'

end
end SingularValueBounds.KL
