import SingularValueBounds.KL.Upper.Comparison
import SingularValueBounds.KL.Upper.ComparisonNorms

/-! # Matrix consequences of the normalized upper-comparison norm bounds -/
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def upperNormalizedSpectrum (R : Matrix ι ι ℝ) (hR : R.PosDef) (i : ι) : ℝ :=
  hR.isHermitian.eigenvalues i / frobenius R

def upperComparisonShapeMean (R : Matrix ι ι ℝ) (hR : R.PosDef) : ℝ :=
  normalizedUpperMean (upperNormalizedSpectrum R hR)

theorem upperNormalizedSpectrum_properties {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (∀ i, 0 ≤ upperNormalizedSpectrum R hR i) ∧
      (∑ i, upperNormalizedSpectrum R hR i ^ 2) = 1 := by
  refine ⟨fun i => div_nonneg (hR.eigenvalues_pos i).le (frobenius_pos hR).le, ?_⟩
  simp only [upperNormalizedSpectrum, div_pow, ← Finset.sum_div]
  rw [← real_spectral_trace_square hR.isHermitian,
    frobenius_eq_sqrt_trace_square hR.isHermitian, Real.sq_sqrt (trace_square_pos hR).le]
  exact div_self (trace_square_pos hR).ne'

theorem upperFixedEigenvalue_normalized {R : Matrix ι ι ℝ} (hR : R.PosDef) (i : ι) :
    upperFixedEigenvalue hR.isHermitian.eigenvalues i = frobenius R *
      normalizedUpperEigenvalue (upperNormalizedSpectrum R hR) i := by
  have hη := frobenius_pos hR
  have hf := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian] at hf
  have hw : ∀ j, upperWeight hR.isHermitian.eigenvalues j = upperNormalizedSpectrum R hR j ^ 2 := by
    intro j
    unfold upperWeight upperNormalizedSpectrum
    rw [← real_spectral_trace_square hR.isHermitian, ← hf]
    field_simp [hη.ne']
  have ha : upperWeightedMean hR.isHermitian.eigenvalues =
      frobenius R * upperComparisonShapeMean R hR := by
    unfold upperWeightedMean upperComparisonShapeMean normalizedUpperMean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hw]
    unfold upperNormalizedSpectrum
    field_simp [hη.ne']
  unfold upperFixedEigenvalue normalizedUpperEigenvalue
  rw [hw, ha]
  change hR.isHermitian.eigenvalues i + _ = frobenius R *
    (upperNormalizedSpectrum R hR i + upperComparisonShapeMean R hR *
      upperNormalizedSpectrum R hR i ^ 2 - 2 * upperNormalizedSpectrum R hR i ^ 3)
  unfold upperNormalizedSpectrum
  field_simp [hη.ne']
  ring

theorem upperFixedComparison_frobenius_square {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    frobenius (upperFixedComparison R) ^ 2 = frobenius R ^ 2 *
      ∑ i, normalizedUpperEigenvalue (upperNormalizedSpectrum R hR) i ^ 2 := by
  have hC := upperFixedComparison_posSemidef hR
  have hs := congrArg (fun A : Matrix ι ι ℝ => Matrix.trace (A ^ 2))
    (upperFixedComparison_spectral hR)
  simp only [pow_two] at hs
  rw [unitary_conjugate_mul, Matrix.diagonal_mul_diagonal,
    unitary_conjugate_trace, Matrix.trace_diagonal] at hs
  have hf := frobenius_sq (upperFixedComparison R)
  rw [← trace_square_eq_sum_sq hC.isHermitian] at hf
  simp only [pow_two] at hf
  rw [pow_two (frobenius (upperFixedComparison R)), hf, hs]
  simp_rw [upperFixedEigenvalue_normalized hR, ← pow_two, mul_pow]
  rw [← Finset.mul_sum]

/-- The first bound in `eq:app-up-comparison-norms`, with its original scale. -/
theorem upperFixedComparison_frobenius_bound {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    frobenius (upperFixedComparison R) ^ 2 ≤ frobenius R ^ 2 *
      (1 - upperComparisonShapeMean R hR ^ 2 - upperComparisonShapeMean R hR ^ 2 *
        (1 - upperComparisonShapeMean R hR) ^ 2) := by
  rw [upperFixedComparison_frobenius_square hR]
  obtain ⟨hx, h2⟩ := upperNormalizedSpectrum_properties hR
  exact mul_le_mul_of_nonneg_left (normalized_upper_frobenius_bound hx h2) (sq_nonneg _)

/-- A scalar strict bound on every comparison eigenvalue gives a positive gap. -/
lemma upperFixedComparison_gap_posDef {R : Matrix ι ι ℝ} (hR : R.PosDef) {b : ℝ}
    (hb : ∀ i, upperFixedEigenvalue hR.isHermitian.eigenvalues i < b) :
    (b • (1 : Matrix ι ι ℝ) - upperFixedComparison R).PosDef := by
  let U := hR.isHermitian.eigenvectorUnitary
  let d := upperFixedEigenvalue hR.isHermitian.eigenvalues
  have hd : Matrix.diagonal (fun i => b - d i) = b • (1 : Matrix ι ι ℝ) - Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have hs : b • (1 : Matrix ι ι ℝ) - upperFixedComparison R =
      (U : Matrix ι ι ℝ) * Matrix.diagonal (fun i => b - d i) * star (U : Matrix ι ι ℝ) := by
    rw [hd, Matrix.mul_sub, Matrix.sub_mul, unitary_conjugate_scalar,
      upperFixedComparison_spectral hR]
  rw [hs]
  exact unitary_conjugate_posDef U _ (Matrix.PosDef.diagonal (fun i => sub_pos.mpr (hb i)))

lemma upperFixedComparison_maximum_lt {R : Matrix ι ι ℝ} (hR : R.PosDef) {b : ℝ}
    (hb : ∀ i, upperFixedEigenvalue hR.isHermitian.eigenvalues i < b) :
    spectralMaximum (upperFixedComparison R) (upperFixedComparison_posSemidef hR).isHermitian < b := by
  have hgap := upperFixedComparison_gap_posDef hR hb
  apply (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
  intro i _
  have hi := eigenvalue_gap_pos (upperFixedComparison_posSemidef hR).isHermitian
    (a := b) (ε := 1) (by simpa only [one_smul] using hgap) i
  linarith

/-- The strict `223/500` operator bound, interpreted spectrally. -/
theorem upperFixedComparison_maximum_bound {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    spectralMaximum (upperFixedComparison R) (upperFixedComparison_posSemidef hR).isHermitian <
      (223 : ℝ) / 500 * frobenius R := by
  obtain ⟨hx, h2⟩ := upperNormalizedSpectrum_properties hR
  apply upperFixedComparison_maximum_lt hR
  intro i
  rw [upperFixedEigenvalue_normalized hR]
  have hb := mul_lt_mul_of_pos_left (normalized_upper_eigenvalue_lt hx h2 i) (frobenius_pos hR)
  nlinarith only [hb]

/-- The positive gap needed for the comparison determinant. -/
theorem upperFixedComparison_half_gap {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    ((frobenius R / 2) • (1 : Matrix ι ι ℝ) - upperFixedComparison R).PosDef := by
  obtain ⟨hx, h2⟩ := upperNormalizedSpectrum_properties hR
  apply upperFixedComparison_gap_posDef hR
  intro i
  rw [upperFixedEigenvalue_normalized hR]
  have hb := mul_lt_mul_of_pos_left (normalized_upper_eigenvalue_lt hx h2 i) (frobenius_pos hR)
  nlinarith [frobenius_pos hR]

/-- The concentrated-spectrum operator bound. -/
theorem upperFixedComparison_maximum_bound_concentrated {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (hκ : (37 : ℝ) / 40 ≤ spectralRatio R hR) :
    spectralMaximum (upperFixedComparison R) (upperFixedComparison_posSemidef hR).isHermitian ≤
      (21 : ℝ) / 50 * frobenius R := by
  obtain ⟨hx, h2⟩ := upperNormalizedSpectrum_properties hR
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty hR.isHermitian.eigenvalues
  have hk' : (37 : ℝ) / 40 ≤ upperNormalizedSpectrum R hR k := by
    change (37 : ℝ) / 40 ≤ hR.isHermitian.eigenvalues k / frobenius R
    change (37 : ℝ) / 40 ≤ spectralMaximum R hR.isHermitian / frobenius R at hκ
    simpa only [spectralMaximum, hk] using hκ
  apply le_of_forall_pos_le_add
  intro ε hε
  apply le_of_lt
  apply upperFixedComparison_maximum_lt hR
  intro i
  rw [upperFixedEigenvalue_normalized hR]
  have hb := mul_le_mul_of_nonneg_left
    (normalized_upper_eigenvalue_le_of_concentrated hx h2 hk' i) (frobenius_pos hR).le
  nlinarith only [hb, hε]

/-- The normalized spectral representation of the actual comparison matrix. -/
theorem upperFixedComparison_normalized_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    upperFixedComparison R = frobenius R •
      ((hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
        Matrix.diagonal (normalizedUpperEigenvalue (upperNormalizedSpectrum R hR)) *
          star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)) := by
  rw [upperFixedComparison_spectral hR]
  have hd : Matrix.diagonal (upperFixedEigenvalue hR.isHermitian.eigenvalues) =
      frobenius R • Matrix.diagonal (normalizedUpperEigenvalue (upperNormalizedSpectrum R hR)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul] using
        upperFixedEigenvalue_normalized hR i
    · simp [Matrix.diagonal, hij]
  rw [hd, Matrix.mul_smul, Matrix.smul_mul]

theorem trace_div_frobenius_eq_normalized_sum {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix.trace R / frobenius R = ∑ i, upperNormalizedSpectrum R hR i := by
  rw [real_spectral_trace hR.isHermitian, Finset.sum_div]
  rfl

def upperComparisonNormalizedGap (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 : Matrix ι ι ℝ) - (2 / frobenius R) • upperFixedComparison R

/-- Actual matrix diagonalization underlying the determinant comparison. -/
theorem upperComparisonNormalizedGap_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    upperComparisonNormalizedGap R =
      (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
        Matrix.diagonal (fun i => 1 - 2 * normalizedUpperEigenvalue (upperNormalizedSpectrum R hR) i) *
          star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let d := upperFixedEigenvalue hR.isHermitian.eigenvalues
  have hd : Matrix.diagonal (fun i => 1 - 2 * normalizedUpperEigenvalue (upperNormalizedSpectrum R hR) i) =
      (1 : Matrix ι ι ℝ) - (2 / frobenius R) • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul]
      dsimp [d]
      rw [upperFixedEigenvalue_normalized hR]
      field_simp [(frobenius_pos hR).ne']
    · simp [Matrix.diagonal, Matrix.one_apply, hij]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, U.2.2]
  exact congrArg (fun A : Matrix ι ι ℝ => (1 : Matrix ι ι ℝ) - (2 / frobenius R) • A)
    (upperFixedComparison_spectral hR)

theorem upperComparisonNormalizedGap_posDef {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (upperComparisonNormalizedGap R).PosDef := by
  rw [upperComparisonNormalizedGap_spectral hR]
  apply unitary_conjugate_posDef
  apply Matrix.PosDef.diagonal
  intro i
  obtain ⟨hx, h2⟩ := upperNormalizedSpectrum_properties hR
  have hb := normalized_upper_eigenvalue_lt hx h2 i
  linarith

/-- The product is the determinant of the matrix used in the theorem. -/
theorem upperComparisonNormalizedGap_det {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix.det (upperComparisonNormalizedGap R) =
      ∏ i, (1 - 2 * normalizedUpperEigenvalue (upperNormalizedSpectrum R hR) i) := by
  rw [upperComparisonNormalizedGap_spectral hR, unitary_conjugate_det, Matrix.det_diagonal]

end
end SingularValueBounds.KL
