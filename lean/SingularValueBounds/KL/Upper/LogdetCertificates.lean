import SingularValueBounds.KL.Upper.CertificateBridges
import SingularValueBounds.KL.Upper.ComparisonLogdet

/-! # The six determinant certificates for the actual comparison matrix
Includes the largest-eigenvalue excess used in the joint spectral witnesses.
-/
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem upperNormalizedSpectrum_le_ratio {R : Matrix ι ι ℝ} (hR : R.PosDef) (j : ι) :
    upperNormalizedSpectrum R hR j ≤ spectralRatio R hR :=
  (div_le_div_iff_of_pos_right (frobenius_pos hR)).2
    (eigenvalue_le_spectralMaximum hR.isHermitian j)

theorem upper_majorant_matrix_domain (i : Fin 6) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (ha : upperComparisonShapeMean R hR ∈
      Set.Icc ((majorantBoxes i).left : ℝ) ((majorantBoxes i).right : ℝ))
    (hκ : spectralRatio R hR ≤ ((majorantBoxes i).top : ℝ)) (j : ι) :
    (majorantBoxes i).contains (upperComparisonShapeMean R hR) (upperNormalizedSpectrum R hR j) := by
  refine ⟨ha, ?_, (upperNormalizedSpectrum_le_ratio hR j).trans hκ⟩
  have hz : (majorantBoxes i).bottom = 0 := by fin_cases i <;> norm_num [majorantBoxes]
  rw [hz, Rat.cast_zero]
  exact (upperNormalizedSpectrum_properties hR).1 j

theorem upperComparisonMatrixLogdet_six (h : MajorantCertificateConditions) (i : Fin 6)
    {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (ha : upperComparisonShapeMean R hR ∈
      Set.Icc ((majorantBoxes i).left : ℝ) ((majorantBoxes i).right : ℝ))
    (hκ : spectralRatio R hR ≤ ((majorantBoxes i).top : ℝ)) :
    upperComparisonMatrixLogdet R ≤ upperMajorantB i (upperComparisonShapeMean R hR) := by
  have h := upper_six_logdet_majorants h i (upperNormalizedSpectrum R hR)
    (upperNormalizedSpectrum_properties hR).2 (upper_majorant_matrix_domain i hR ha hκ)
  rw [upperComparisonMatrixLogdet_eq_normalized hR]
  simpa only [normalizedLogdet, normalizedUpperEigenvalue, normalizedUpperMean,
    upperComparisonShapeMean, upperComparisonZ] using h

theorem upperComparisonMatrixLogdet_joint (h : MajorantCertificateConditions) (i : Fin 6)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (top : ι)
    (ha : upperComparisonShapeMean R hR ∈
      Set.Icc ((majorantBoxes i).left : ℝ) ((majorantBoxes i).right : ℝ))
    (hκ : spectralRatio R hR ≤ ((majorantBoxes i).top : ℝ)) :
    upperComparisonMatrixLogdet R ≤ upperMajorantB i (upperComparisonShapeMean R hR)-
      upperMajorantH i (upperComparisonShapeMean R hR) (upperNormalizedSpectrum R hR top)+
      upperPadeN (upperComparisonZ (upperComparisonShapeMean R hR) (upperNormalizedSpectrum R hR top))/
        upperPadeD (upperComparisonZ (upperComparisonShapeMean R hR) (upperNormalizedSpectrum R hR top)) := by
  have h := upper_joint_logdet_majorants h i (upperNormalizedSpectrum R hR) top
    (upperNormalizedSpectrum_properties hR).2 (upper_majorant_matrix_domain i hR ha hκ)
  rw [upperComparisonMatrixLogdet_eq_normalized hR]
  simpa only [normalizedLogdet, normalizedUpperEigenvalue, normalizedUpperMean,
    upperComparisonShapeMean, upperComparisonZ] using h

/-- The joint bound in its printed form, with `κ` a largest normalized
eigenvalue, rather than an arbitrary distinguished coordinate. -/
theorem upperComparisonMatrixLogdet_joint_max (h : MajorantCertificateConditions) (i : Fin 6)
    {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (ha : upperComparisonShapeMean R hR ∈
      Set.Icc ((majorantBoxes i).left : ℝ) ((majorantBoxes i).right : ℝ))
    (hκ : spectralRatio R hR ≤ ((majorantBoxes i).top : ℝ)) :
    upperComparisonMatrixLogdet R ≤ upperMajorantB i (upperComparisonShapeMean R hR)-
      upperMajorantH i (upperComparisonShapeMean R hR) (spectralRatio R hR)+
      upperPadeN (upperComparisonZ (upperComparisonShapeMean R hR) (spectralRatio R hR))/
        upperPadeD (upperComparisonZ (upperComparisonShapeMean R hR) (spectralRatio R hR)) := by
  obtain ⟨top, _, ht⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty hR.isHermitian.eigenvalues
  have he : upperNormalizedSpectrum R hR top = spectralRatio R hR := by
    unfold upperNormalizedSpectrum spectralRatio spectralMaximum
    rw [← ht]
  simpa only [he] using upperComparisonMatrixLogdet_joint h i hR top ha hκ

end
end SingularValueBounds.KL
