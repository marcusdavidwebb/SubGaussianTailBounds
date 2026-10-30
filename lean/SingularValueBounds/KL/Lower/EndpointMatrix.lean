import SingularValueBounds.KL.Lower.EndpointMixed

/-! # Endpoint mixed costs for actual comparison matrices -/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ}

lemma endpointComparisonEigen_nonneg_of_profile {k A c x : ℝ}
    (hk : 0 ≤ k) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hp : LowerComparisonProfile k A c) :
    0 ≤ endpointComparisonEigen A c x := by
  have hs := hp x hx hx1
  have hm : 0 ≤ min k (Real.sqrt (1-x^2)) := le_min hk (Real.sqrt_nonneg _)
  have ha : (c-1)*x ≤ A := by linarith
  have he := mul_le_mul_of_nonneg_right ha hx
  have hr : 0 ≤ 1-x^2 := by nlinarith
  dsimp [endpointComparisonEigen]
  nlinarith [mul_nonneg hx hr, mul_nonneg hx (sub_nonneg.mpr he)]

theorem normalized_resolvent_spectrum {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hF : frobenius R = 1) :
    spectralMoment hR.isHermitian.eigenvalues 2 = 1 := by
  have hf := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian, hF] at hf
  rw [real_spectral_trace_square hR.isHermitian] at hf
  simpa only [one_pow, spectralMoment] using hf.symm

theorem lowerComparison_normalized_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hF : frobenius R = 1) (A c : ℝ) :
    lowerComparison R A c =
      (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
        Matrix.diagonal (fun i => endpointComparisonEigen A c (hR.isHermitian.eigenvalues i)) *
        star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  have hs : Matrix.trace (R^2) = 1 := by
    rw [real_spectral_trace_square hR.isHermitian]
    exact normalized_resolvent_spectrum hR hF
  rw [lowerComparison_spectral hR, hs, hF]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, div_one, mul_one, endpointComparisonEigen]
    ring
  · simp [Matrix.diagonal, hij]

theorem endpoint_normalized_matrix_mixed_cost (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hF : frobenius R = 1) {A c : ℝ}
    (hp : LowerComparisonProfile (spectralMaximum R hR.isHermitian) A c) :
    (∫ ω, quadraticForm (lowerWeight R) X ω *
      quadraticForm (lowerComparison R A c) X ω ∂μ) - Matrix.trace R ≤
      endpointOrdinaryCost hR.isHermitian.eigenvalues A c := by
  let U := hR.isHermitian.eigenvectorUnitary
  let XR := fun ω => star (U : Matrix ι ι ℝ) *ᵥ X ω
  have h2 := normalized_resolvent_spectrum hR hF
  have hs : Matrix.trace (R^2) = 1 := by
    rw [real_spectral_trace_square hR.isHermitian]
    exact h2
  have hqP (ω : Ω) : quadraticForm (lowerWeight R) X ω =
      diagonalQuadratic (fun i => hR.isHermitian.eigenvalues i ^ 2) XR ω := by
    simp only [lowerWeight, hs, inv_one, one_smul, quadraticForm]
    rw [real_spectral_square hR.isHermitian, quadratic_conjugate_diagonal]
    simp only [diagonalQuadratic, XR, U, mul_comm]
  have hqB (ω : Ω) : quadraticForm (lowerComparison R A c) X ω =
      diagonalQuadratic (fun i => endpointComparisonEigen A c (hR.isHermitian.eigenvalues i)) XR ω := by
    dsimp only [quadraticForm]
    rw [lowerComparison_normalized_spectral hR hF, quadratic_conjugate_diagonal]
    simp only [diagonalQuadratic, XR, U, mul_comm]
  have hk0 : 0 ≤ spectralMaximum R hR.isHermitian := (hR.eigenvalues_pos (Classical.arbitrary ι)).le.trans
    (eigenvalue_le_spectralMaximum hR.isHermitian _)
  have hk1 : spectralMaximum R hR.isHermitian ≤ 1 := by
    simpa only [hF] using spectralMaximum_le_frobenius hR.posSemidef
  have hf (i : ι) : 0 ≤ endpointComparisonEigen A c (hR.isHermitian.eigenvalues i) :=
    endpointComparisonEigen_nonneg_of_profile hk0 (hR.eigenvalues_pos i).le
      ((eigenvalue_le_spectralMaximum hR.isHermitian i).trans hk1) hp
  have he := endpoint_diagonal_mixed_cost (hsg.unitary U) (hiso.unitary U)
    hR.isHermitian.eigenvalues A c h2 hf
  change (∫ ω, diagonalQuadratic (fun i => hR.isHermitian.eigenvalues i^2) XR ω *
      diagonalQuadratic (fun i => endpointComparisonEigen A c (hR.isHermitian.eigenvalues i)) XR ω ∂μ) -
      (∑ i, hR.isHermitian.eigenvalues i) ≤ _ at he
  simp_rw [← hqP, ← hqB] at he
  simpa only [real_spectral_trace hR.isHermitian] using he

/-- The actual canonical comparison has mixed cost `2κ` in the entire
low-operator-ratio regime, including all finite dimensions. -/
theorem endpoint_normalized_operator_mixed_cost (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hF : frobenius R = 1)
    (hkmax : spectralMaximum R hR.isHermitian ≤ 73/100) :
    (∫ ω, quadraticForm (lowerWeight R) X ω *
      quadraticForm (lowerComparison0 R hR) X ω ∂μ) ≤
      Matrix.trace R + 2*spectralMaximum R hR.isHermitian := by
  let k := spectralMaximum R hR.isHermitian
  have hp : LowerComparisonProfile k k 1 := by
    intro z _ _
    simp only [sub_self, zero_mul, add_zero]
    exact min_le_left _ _
  have he := endpoint_normalized_matrix_mixed_cost hsg hiso hR hF hp
  obtain ⟨top, _, ht⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty hR.isHermitian.eigenvalues
  have ht' : hR.isHermitian.eigenvalues top = k := ht.symm
  have hb := endpoint_operator_cost hR.isHermitian.eigenvalues
    ((hR.eigenvalues_pos (Classical.arbitrary ι)).le.trans
      (eigenvalue_le_spectralMaximum hR.isHermitian _)) hkmax
    (fun i => ⟨(hR.eigenvalues_pos i).le, eigenvalue_le_spectralMaximum hR.isHermitian i⟩)
    (normalized_resolvent_spectrum hR hF) top ht'
  have hc : lowerComparison0 R hR = lowerComparison R k 1 := by
    simp only [lowerComparison0, hF, div_one]
    rfl
  rw [hc]
  dsimp [endpointOrdinaryCost] at he
  norm_num only [sub_self, zero_mul, add_zero, one_mul] at he
  linarith

end
end SingularValueBounds.KL
