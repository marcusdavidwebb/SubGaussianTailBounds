import SingularValueBounds.KL.Barrier.Roots
import SingularValueBounds.KL.Barrier.Norms

/-! # Deterministic exact lower-shift comparisons

Supplementary S1.3, equations `eq:app-low-comparison` and
`eq:app-low-two-comparisons`. All rows are allowed; the division by the exact
shift is used only in the nonzero-row lemmas. `frobenius` and
`spectralMaximum` are the Euclidean/spectral quantities from `KL.Statement`.
-/

open scoped BigOperators Matrix

namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The unshifted, rank-one updated resolvent. -/
def lowerUnshifted (R : Matrix ι ι ℝ) (x : ι → ℝ) :=
  (R⁻¹ + Matrix.vecMulVec x x)⁻¹

/-- The scalar inverse-trace drop. -/
def lowerDrop (R : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (x ⬝ᵥ ((R ^ 2) *ᵥ x)) / (1 + x ⬝ᵥ (R *ᵥ x))

/-- The row-weighted spectral mean denoted `c_X` in the supplement. -/
def lowerRowMean (R : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (x ⬝ᵥ ((R ^ 3) *ᵥ x)) / (x ⬝ᵥ ((R ^ 2) *ᵥ x))

/-- The normalized square-resolvent matrix `P`. -/
def lowerWeight (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (Matrix.trace (R ^ 2))⁻¹ • R ^ 2

/-- The two-parameter family `R + P (A η I - c R)`. -/
def lowerComparison (R : Matrix ι ι ℝ) (A c : ℝ) : Matrix ι ι ℝ :=
  R + lowerWeight R * ((A * frobenius R) • (1 : Matrix ι ι ℝ) - c • R)

lemma quadratic_square_pos {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ ((R ^ 2) *ᵥ x) := by
  rw [real_spectral_square hR.isHermitian, quadratic_conjugate_diagonal]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (upper_coordinates_ne_zero hR hx)
  exact lt_of_lt_of_le (mul_pos (sq_pos_of_ne_zero hi)
    (sq_pos_of_pos (hR.eigenvalues_pos i)))
    (Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.mem_univ i))

lemma real_spectral_cube {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    R ^ 3 = (hR.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => hR.eigenvalues i ^ 3) *
        star (hR.eigenvectorUnitary : Matrix ι ι ℝ) := by
  calc
    R ^ 3 = R ^ 2 * R := pow_succ R 2
    _ = _ := by
      have h := congrArg₂ (fun A B : Matrix ι ι ℝ => A * B)
        (real_spectral_square hR) (real_spectral_decomposition hR)
      rw [unitary_conjugate_mul, Matrix.diagonal_mul_diagonal] at h
      convert! h using 1 <;> simp only [pow_succ]

lemma lowerDenominator_pos {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    0 < 1 + x ⬝ᵥ (R *ᵥ x) := by
  have : 0 ≤ x ⬝ᵥ (R *ᵥ x) := by simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
  linarith

theorem lowerDrop_pos {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < lowerDrop R x :=
  div_pos (quadratic_square_pos hR hx) (lowerDenominator_pos hR x)

theorem lowerDrop_eq_trace {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    lowerDrop R x = Matrix.trace R - Matrix.trace (lowerUnshifted R x) := by
  rw [lowerUnshifted, rankOne_trace hR]
  dsimp [lowerDrop]
  ring

theorem lowerUnshifted_posDef {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    (lowerUnshifted R x).PosDef :=
  (hR.inv.add_posSemidef (outer_posSemidef x)).inv

/-- Cauchy--Schwarz for the three row-weighted spectral moments. -/
theorem quadratic_moment_cauchy {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    (x ⬝ᵥ ((R ^ 2) *ᵥ x)) ^ 2 ≤
      (x ⬝ᵥ (R *ᵥ x)) * (x ⬝ᵥ ((R ^ 3) *ᵥ x)) := by
  have hq1 := congrArg (fun A : Matrix ι ι ℝ => x ⬝ᵥ (A *ᵥ x))
    (real_spectral_decomposition hR.isHermitian)
  rw [quadratic_conjugate_diagonal] at hq1
  rw [hq1, real_spectral_square hR.isHermitian, real_spectral_cube hR.isHermitian]
  simp only [quadratic_conjugate_diagonal]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro i _
    exact mul_nonneg (sq_nonneg _) (hR.eigenvalues_pos i).le
  · intro i _
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (hR.eigenvalues_pos i).le _)
  · intro i _
    ring

/-- `q ≤ c_X ≤ M ≤ η`, with no distributional assumptions. -/
theorem lowerDrop_le_rowMean {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) : lowerDrop R x ≤ lowerRowMean R x := by
  have hn := quadratic_square_pos hR hx
  have hd := lowerDenominator_pos hR x
  have hc := quadratic_moment_cauchy hR x
  have h3 : 0 ≤ x ⬝ᵥ ((R ^ 3) *ᵥ x) := by
    rw [real_spectral_cube hR.isHermitian, quadratic_conjugate_diagonal]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _)
      (pow_nonneg (hR.eigenvalues_pos i).le _))
  exact (div_le_div_iff₀ hd hn).mpr (by nlinarith)

theorem lowerRowMean_le_maximum {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) :
    lowerRowMean R x ≤ spectralMaximum R hR.isHermitian := by
  apply (div_le_iff₀ (quadratic_square_pos hR hx)).mpr
  rw [real_spectral_cube hR.isHermitian, real_spectral_square hR.isHermitian]
  simp only [quadratic_conjugate_diagonal, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (eigenvalue_le_spectralMaximum hR.isHermitian i)
    (mul_nonneg (sq_nonneg ((star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x) i))
      (sq_nonneg (hR.isHermitian.eigenvalues i)))
  convert! h using 1 <;> ring

lemma trace_outer (x y : ι → ℝ) : Matrix.trace (Matrix.vecMulVec x y) = y ⬝ᵥ x := by
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma trace_mul_outer (R : Matrix ι ι ℝ) (x : ι → ℝ) :
    Matrix.trace (R * Matrix.vecMulVec x x) = x ⬝ᵥ (R *ᵥ x) := by
  rw [mul_outer, trace_outer]

/-- Exact square-trace identity after the unshifted row update. -/
theorem lowerUnshifted_trace_square {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) :
    Matrix.trace (lowerUnshifted R x ^ 2) = Matrix.trace (R ^ 2) -
      2 * lowerDrop R x * lowerRowMean R x + lowerDrop R x ^ 2 := by
  have hn := quadratic_square_pos hR hx
  have hd := lowerDenominator_pos hR x
  have hs : x ᵥ* R = R *ᵥ x := by
    have ht : R.transpose = R := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
    rw [← Matrix.mulVec_transpose, ht]
  have h2 : (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = x ⬝ᵥ ((R ^ 2) *ᵥ x) := by
    symm
    rw [pow_two, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hs]
  have h3 : (R *ᵥ x) ⬝ᵥ (R *ᵥ (R *ᵥ x)) = x ⬝ᵥ ((R ^ 3) *ᵥ x) := by
    symm
    rw [pow_succ, pow_two, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, hs]
  rw [lowerUnshifted, rankOne_inverse hR, pow_two]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, Matrix.trace_sub, Matrix.trace_smul]
  rw [Matrix.trace_mul_comm (Matrix.vecMulVec _ _) R, trace_mul_outer,
    outer_mul_outer, Matrix.trace_smul, trace_outer]
  simp only [smul_eq_mul]
  rw [← dotProduct, h2, h3]
  rw [← pow_two R]
  dsimp [lowerDrop, lowerRowMean]
  field_simp [hn.ne', hd.ne']
  ring

/-- Spectral description of a lower resolvent gap. -/
lemma lowerResolvent_spectral {G : Matrix ι ι ℝ} (hG : G.PosDef) {δ : ℝ}
    (hgap : (G⁻¹ - δ • (1 : Matrix ι ι ℝ)).PosDef) :
    (∀ i, 0 < 1 - δ * hG.isHermitian.eigenvalues i) ∧
    (G⁻¹ - δ • (1 : Matrix ι ι ℝ))⁻¹ =
      (hG.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
        Matrix.diagonal (fun i => hG.isHermitian.eigenvalues i /
          (1 - δ * hG.isHermitian.eigenvalues i)) *
        star (hG.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let U := hG.isHermitian.eigenvectorUnitary
  let g := hG.isHermitian.eigenvalues
  have hg : ∀ i, 0 < g i := hG.eigenvalues_pos
  have hd : Matrix.diagonal (fun i => (g i)⁻¹ - δ) =
      Matrix.diagonal (fun i => (g i)⁻¹) - δ • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have hs : G⁻¹ - δ • (1 : Matrix ι ι ℝ) = (U : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => (g i)⁻¹ - δ) * star (U : Matrix ι ι ℝ) := by
    have hi := congrArg (fun A : Matrix ι ι ℝ => A⁻¹)
      (real_spectral_decomposition hG.isHermitian)
    rw [unitary_conjugate_inverse, positive_diagonal_inverse _ hg] at hi
    rw [hi, hd, Matrix.mul_sub, Matrix.sub_mul, unitary_conjugate_scalar]
  have hdp : ∀ i, 0 < (g i)⁻¹ - δ :=
    Matrix.posDef_diagonal_iff.mp ((unitary_conjugate_posDef_iff U _).mp (hs ▸ hgap))
  have hden : ∀ i, 0 < 1 - δ * g i := by
    intro i
    have h := mul_pos (hdp i) (hg i)
    rw [sub_mul, inv_mul_cancel₀ (hg i).ne'] at h
    exact h
  refine ⟨hden, ?_⟩
  rw [hs, unitary_conjugate_inverse, positive_diagonal_inverse _ hdp]
  have he : (fun i => ((g i)⁻¹ - δ)⁻¹) = (fun i => g i / (1 - δ * g i)) := by
    funext i
    have hi : (g i)⁻¹ - δ = (1 - δ * g i) / g i := by
      rw [sub_div, one_div, mul_div_cancel_right₀ _ (hg i).ne']
    rw [hi, inv_div]
  rw [he]


/-- The trace-increment/resolvent bound. `H` is any upper bound for the
spectrum of the unshifted resolvent, so both its spectral and Frobenius
bounds may be substituted. -/
theorem resolvent_trace_ratio_bound {G : Matrix ι ι ℝ} (hG : G.PosDef)
    {δ H : ℝ} (hδ : 0 < δ) (hgap : (G⁻¹ - δ • (1 : Matrix ι ι ℝ)).PosDef)
    (hH : ∀ i, hG.isHermitian.eigenvalues i ≤ H) :
    (Matrix.trace (G⁻¹ - δ • (1 : Matrix ι ι ℝ))⁻¹ - Matrix.trace G) / δ ≤
      Matrix.trace (G ^ 2) +
        (Matrix.trace (G⁻¹ - δ • (1 : Matrix ι ι ℝ))⁻¹ - Matrix.trace G) * H := by
  obtain ⟨hd, hs⟩ := lowerResolvent_spectral hG hgap
  rw [hs, unitary_conjugate_trace, Matrix.trace_diagonal,
    real_spectral_trace hG.isHermitian, real_spectral_trace_square hG.isHermitian]
  let g := hG.isHermitian.eigenvalues
  let f := fun i => g i / (1 - δ * g i)
  change ((∑ i, f i) - ∑ i, g i) / δ ≤
    (∑ i, g i ^ 2) + ((∑ i, f i) - ∑ i, g i) * H
  have hdiff : ∀ i, f i - g i = δ * g i * f i := by
    intro i
    change g i / (1 - δ * g i) - g i = δ * g i * (g i / (1 - δ * g i))
    rw [div_sub' (hd i).ne', ← mul_div_assoc]
    congr 1
    ring
  have hn : ∀ i, 0 ≤ f i - g i := by
    intro i
    rw [hdiff]
    exact mul_nonneg (mul_nonneg hδ.le (hG.eigenvalues_pos i).le)
      (div_nonneg (hG.eigenvalues_pos i).le (hd i).le)
  have heq : ((∑ i, f i) - ∑ i, g i) / δ = ∑ i, g i * f i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [hdiff, mul_assoc, mul_div_cancel_left₀ _ hδ.ne']
  rw [heq, ← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right (hH i) (hn i)
  nlinarith only [h]

/-- Rank-one addition decreases every spectral upper bound for the resolvent. -/
theorem lowerUnshifted_eigenvalue_le_maximum {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (x : ι → ℝ) (i : ι) :
    (lowerUnshifted_posDef hR x).isHermitian.eigenvalues i ≤
      spectralMaximum R hR.isHermitian := by
  let G := lowerUnshifted R x
  let hG := lowerUnshifted_posDef hR x
  let v : ι → ℝ := hG.isHermitian.eigenvectorBasis i
  have hv : v ≠ 0 := by simpa [v] using hG.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
  have hvnorm : 0 < v ⬝ᵥ v := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    have hs := Finset.single_le_sum (s := Finset.univ)
      (fun k (_ : k ∈ Finset.univ) => sq_nonneg (v k)) (Finset.mem_univ j)
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hj) (by simpa only [dotProduct, pow_two] using hs)
  have hquad : v ⬝ᵥ (G *ᵥ v) ≤ v ⬝ᵥ (R *ᵥ v) := by
    change v ⬝ᵥ (lowerUnshifted R x *ᵥ v) ≤ _
    rw [lowerUnshifted, rankOne_inverse hR, Matrix.sub_mulVec,
      Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, outer_quadratic]
    simp only [smul_eq_mul]
    exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr (lowerDenominator_pos hR x).le)
      (sq_nonneg _))
  have heig := hG.isHermitian.mulVec_eigenvectorBasis i
  change G *ᵥ v = _ at heig
  rw [heig, dotProduct_smul] at hquad
  have hb := hquad.trans (quadratic_le_spectralMaximum hR.isHermitian v)
  simp only [smul_eq_mul] at hb
  exact (mul_le_mul_iff_left₀ hvnorm).mp hb

/-- The exact trace ratio using either spectral upper bound for `G`. -/
lemma lowerDrop_ratio_bound {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) {H : ℝ}
    (hH : ∀ i, (lowerUnshifted_posDef hR x).isHermitian.eigenvalues i ≤ H) :
    lowerDrop R x / lowerShift R hR x ≤
      Matrix.trace (lowerUnshifted R x ^ 2) + lowerDrop R x * H := by
  have hA := hR.inv.add_posSemidef (outer_posSemidef x)
  have hinv : (lowerUnshifted R x)⁻¹ = R⁻¹ + Matrix.vecMulVec x x := by
    exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)
  have hp := lowerShift_preserves hR x
  have hgap : ((lowerUnshifted R x)⁻¹ - lowerShift R hR x • (1 : Matrix ι ι ℝ)).PosDef := by
    rw [hinv]
    exact hp.1
  have hb := resolvent_trace_ratio_bound (lowerUnshifted_posDef hR x)
    (lowerShift_pos hR hx) hgap hH
  rw [hinv, hp.2, ← lowerDrop_eq_trace hR] at hb
  exact hb

/-- The first, operator-spectrum comparison in S1.3. -/
theorem lowerDrop_ratio_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) :
    lowerDrop R x / lowerShift R hR x ≤
      frobenius R ^ 2 + lowerDrop R x *
        (spectralMaximum R hR.isHermitian - lowerRowMean R x) := by
  have hb := lowerDrop_ratio_bound hR hx (lowerUnshifted_eigenvalue_le_maximum hR x)
  rw [lowerUnshifted_trace_square hR hx] at hb
  have hf := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian] at hf
  have hq := mul_le_mul_of_nonneg_left (lowerDrop_le_rowMean hR hx) (lowerDrop_pos hR hx).le
  nlinarith only [hb, hf, hq]

/-- The scalar square-root reduction, written without differentiation. -/
lemma lower_sqrt_reduction {η q d : ℝ} (hη : 0 ≤ η)
    (hq : 0 ≤ q) (hqd : q ≤ d) (hdη : d ≤ η) :
    q - 2 * d + Real.sqrt (η ^ 2 - 2 * q * d + q ^ 2) ≤
      Real.sqrt (η ^ 2 - d ^ 2) - d := by
  have hd : 0 ≤ d := hq.trans hqd
  have ha : 0 ≤ η ^ 2 - d ^ 2 :=
    sub_nonneg.mpr (pow_le_pow_left₀ hd hdη 2)
  have hroot : Real.sqrt (η ^ 2 - 2 * q * d + q ^ 2) ≤
      Real.sqrt (η ^ 2 - d ^ 2) + (d - q) := by
    refine Real.sqrt_le_iff.mpr ⟨add_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hqd), ?_⟩
    nlinarith only [Real.sq_sqrt ha,
      mul_nonneg (Real.sqrt_nonneg (η ^ 2 - d ^ 2)) (sub_nonneg.mpr hqd)]
  linarith only [hroot]

/-- The second, Frobenius-spectrum comparison in S1.3. -/
theorem lowerDrop_ratio_frobenius {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) :
    lowerDrop R x / lowerShift R hR x ≤
      frobenius R ^ 2 + lowerDrop R x *
        (Real.sqrt (frobenius R ^ 2 - lowerRowMean R x ^ 2) - lowerRowMean R x) := by
  have hG := lowerUnshifted_posDef hR x
  have hb := lowerDrop_ratio_bound hR hx (fun i =>
    (eigenvalue_le_spectralMaximum hG.isHermitian i).trans
      (spectralMaximum_le_frobenius hG.posSemidef))
  have hgs : frobenius (lowerUnshifted R x) =
      Real.sqrt (frobenius R ^ 2 - 2 * lowerDrop R x * lowerRowMean R x + lowerDrop R x ^ 2) := by
    rw [frobenius_eq_sqrt_trace_square hG.isHermitian,
      lowerUnshifted_trace_square hR hx]
    have hf := frobenius_sq R
    rw [← trace_square_eq_sum_sq hR.isHermitian] at hf
    rw [hf]
  rw [lowerUnshifted_trace_square hR hx, hgs] at hb
  have hf := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian] at hf
  have hs := lower_sqrt_reduction (frobenius_nonneg R) (lowerDrop_pos hR hx).le
    (lowerDrop_le_rowMean hR hx)
    ((lowerRowMean_le_maximum hR hx).trans (spectralMaximum_le_frobenius hR.posSemidef))
  have hmul := mul_le_mul_of_nonneg_left hs (lowerDrop_pos hR hx).le
  nlinarith only [hb, hf, hmul]

/-- Both exact lower comparisons, before normalizing `z = c_X / η`. -/
theorem lowerDrop_ratio_two_comparisons {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) :
    lowerDrop R x / lowerShift R hR x ≤
      frobenius R ^ 2 + lowerDrop R x *
        (min (spectralMaximum R hR.isHermitian)
          (Real.sqrt (frobenius R ^ 2 - lowerRowMean R x ^ 2)) - lowerRowMean R x) := by
  rcases le_total (spectralMaximum R hR.isHermitian)
      (Real.sqrt (frobenius R ^ 2 - lowerRowMean R x ^ 2)) with h | h
  · rw [min_eq_left h]
    exact lowerDrop_ratio_spectral hR hx
  · rw [min_eq_right h]
    exact lowerDrop_ratio_frobenius hR hx

lemma sqrt_lower_normalization {η d : ℝ} (hη : 0 < η) :
    Real.sqrt (η ^ 2 - d ^ 2) = η * Real.sqrt (1 - (d / η) ^ 2) := by
  have hid : η ^ 2 - d ^ 2 = η ^ 2 * (1 - (d / η) ^ 2) := by
    field_simp [hη.ne'] <;> ring
  rw [hid, Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le]

/-- Equation `eq:app-low-two-comparisons`, with `κ=M/η`, `z=c_X/η`. -/
theorem lowerDrop_ratio_normalized {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) :
    lowerDrop R x / lowerShift R hR x ≤
      frobenius R ^ 2 + lowerDrop R x * frobenius R *
        (min (spectralMaximum R hR.isHermitian / frobenius R)
          (Real.sqrt (1 - (lowerRowMean R x / frobenius R) ^ 2)) -
          lowerRowMean R x / frobenius R) := by
  have hb := lowerDrop_ratio_two_comparisons hR hx
  have hη := frobenius_pos hR
  rw [sqrt_lower_normalization hη] at hb
  have hm : min (spectralMaximum R hR.isHermitian)
      (frobenius R * Real.sqrt (1 - (lowerRowMean R x / frobenius R) ^ 2)) =
      frobenius R * min (spectralMaximum R hR.isHermitian / frobenius R)
        (Real.sqrt (1 - (lowerRowMean R x / frobenius R) ^ 2)) := by
    rw [mul_min_of_nonneg _ _ hη.le, mul_div_cancel₀ _ hη.ne']
  rw [hm] at hb
  convert! hb using 1 <;> field_simp [hη.ne'] <;> ring

lemma lowerComparison_polynomial (R : Matrix ι ι ℝ) (A c : ℝ) :
    lowerComparison R A c = R + (Matrix.trace (R ^ 2))⁻¹ •
      ((A * frobenius R) • R ^ 2 - c • R ^ 3) := by
  unfold lowerComparison lowerWeight
  rw [Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one,
    ← pow_succ]

/-- The comparison quadratic form in terms of the second and third row moments. -/
theorem lowerComparison_quadratic (R : Matrix ι ι ℝ) (x : ι → ℝ) (A c : ℝ) :
    x ⬝ᵥ (lowerComparison R A c *ᵥ x) = x ⬝ᵥ (R *ᵥ x) +
      ((A * frobenius R) * (x ⬝ᵥ ((R ^ 2) *ᵥ x)) -
        c * (x ⬝ᵥ ((R ^ 3) *ᵥ x))) / Matrix.trace (R ^ 2) := by
  rw [lowerComparison_polynomial]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

/-- Spectral form of the polynomial comparison matrix. -/
lemma lowerComparison_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef) (A c : ℝ) :
    lowerComparison R A c = (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => hR.isHermitian.eigenvalues i +
        hR.isHermitian.eigenvalues i ^ 2 / Matrix.trace (R ^ 2) *
          (A * frobenius R - c * hR.isHermitian.eigenvalues i)) *
        star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let r := hR.isHermitian.eigenvalues
  let S := Matrix.trace (R ^ 2)
  let η := frobenius R
  have h1 : R = (U : Matrix ι ι ℝ) * Matrix.diagonal r * star (U : Matrix ι ι ℝ) :=
    real_spectral_decomposition hR.isHermitian
  have h2 : R ^ 2 = (U : Matrix ι ι ℝ) * Matrix.diagonal (fun i => r i ^ 2) *
      star (U : Matrix ι ι ℝ) := real_spectral_square hR.isHermitian
  have h3 : R ^ 3 = (U : Matrix ι ι ℝ) * Matrix.diagonal (fun i => r i ^ 3) *
      star (U : Matrix ι ι ℝ) := real_spectral_cube hR.isHermitian
  rw [lowerComparison_polynomial]
  change R + S⁻¹ • ((A * η) • R ^ 2 - c • R ^ 3) =
    (U : Matrix ι ι ℝ) * Matrix.diagonal (fun i => r i + r i ^ 2 / S * (A * η - c * r i)) *
      star (U : Matrix ι ι ℝ)
  have hd : Matrix.diagonal (fun i => r i + r i ^ 2 / S * (A * η - c * r i)) =
      Matrix.diagonal r + S⁻¹ •
        ((A * η) • Matrix.diagonal (fun i => r i ^ 2) -
          c • Matrix.diagonal (fun i => r i ^ 3)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
        Matrix.sub_apply, smul_eq_mul]
      ring
    · simp [Matrix.diagonal, hij]
  rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [← h1, ← h2, ← h3]

/-- A sufficient scalar profile condition for every comparison matrix. -/
def LowerComparisonProfile (κ A c : ℝ) : Prop :=
  ∀ z : ℝ, 0 ≤ z → z ≤ 1 → min κ (Real.sqrt (1 - z ^ 2)) + (c - 1) * z ≤ A

/-- Every matrix satisfying the scalar profile condition controls the exact
lower shift; this includes the zero row without any division by its shift. -/
theorem lowerShift_quadratic_comparison {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : ι → ℝ) {A c : ℝ}
    (hprofile : LowerComparisonProfile (spectralMaximum R hR.isHermitian / frobenius R) A c) :
    x ⬝ᵥ (lowerWeight R *ᵥ x) ≤
      (1 + x ⬝ᵥ (lowerComparison R A c *ᵥ x)) * lowerShift R hR x := by
  by_cases hx : x = 0
  · subst x
    simp only [Matrix.mulVec_zero, dotProduct_zero, lowerShift_zero, mul_zero, le_refl]
  have hη := frobenius_pos hR
  have hn := quadratic_square_pos hR hx
  have hd := lowerDenominator_pos hR x
  have hz0 : 0 ≤ lowerRowMean R x / frobenius R :=
    div_nonneg ((lowerDrop_pos hR hx).le.trans (lowerDrop_le_rowMean hR hx)) hη.le
  have hz1 : lowerRowMean R x / frobenius R ≤ 1 := (div_le_one hη).mpr
    ((lowerRowMean_le_maximum hR hx).trans (spectralMaximum_le_frobenius hR.posSemidef))
  have hp := hprofile _ hz0 hz1
  have hscaled : frobenius R *
      (min (spectralMaximum R hR.isHermitian / frobenius R)
        (Real.sqrt (1 - (lowerRowMean R x / frobenius R) ^ 2)) -
          lowerRowMean R x / frobenius R) ≤ A * frobenius R - c * lowerRowMean R x := by
    have hs := mul_le_mul_of_nonneg_right hp hη.le
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hη.ne'] at hs
    rw [mul_sub, mul_div_cancel₀ _ hη.ne']
    nlinarith only [hs]
  have hbound : frobenius R ^ 2 + lowerDrop R x * frobenius R *
      (min (spectralMaximum R hR.isHermitian / frobenius R)
        (Real.sqrt (1 - (lowerRowMean R x / frobenius R) ^ 2)) -
          lowerRowMean R x / frobenius R) ≤
      frobenius R ^ 2 + lowerDrop R x * (A * frobenius R - c * lowerRowMean R x) := by
    simpa only [mul_assoc] using add_le_add (le_refl (frobenius R ^ 2))
      (mul_le_mul_of_nonneg_left hscaled (lowerDrop_pos hR hx).le)
  have hb := (lowerDrop_ratio_normalized hR hx).trans hbound
  have hf := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian] at hf
  have hidentity : frobenius R ^ 2 + lowerDrop R x *
      (A * frobenius R - c * lowerRowMean R x) =
      frobenius R ^ 2 * (1 + x ⬝ᵥ (lowerComparison R A c *ᵥ x)) /
        (1 + x ⬝ᵥ (R *ᵥ x)) := by
    rw [lowerComparison_quadratic]
    dsimp [lowerDrop, lowerRowMean]
    rw [← hf]
    field_simp [hn.ne', hd.ne', hη.ne']
    ring
  rw [hidentity] at hb
  have hb' := (div_le_iff₀ (lowerShift_pos hR hx)).mp hb
  have hnum : x ⬝ᵥ ((R ^ 2) *ᵥ x) ≤
      frobenius R ^ 2 * (1 + x ⬝ᵥ (lowerComparison R A c *ᵥ x)) * lowerShift R hR x := by
    have hh : (x ⬝ᵥ ((R ^ 2) *ᵥ x)) / (1 + x ⬝ᵥ (R *ᵥ x)) ≤
        (frobenius R ^ 2 * (1 + x ⬝ᵥ (lowerComparison R A c *ᵥ x)) * lowerShift R hR x) /
          (1 + x ⬝ᵥ (R *ᵥ x)) := by
      convert! hb' using 1 <;> ring
    exact (div_le_div_iff_of_pos_right hd).mp hh
  unfold lowerWeight
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [← hf]
  have hfinal := (div_le_iff₀ (sq_pos_of_pos hη)).mpr
    (show x ⬝ᵥ ((R ^ 2) *ᵥ x) ≤
      ((1 + x ⬝ᵥ (lowerComparison R A c *ᵥ x)) * lowerShift R hR x) * frobenius R ^ 2 by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hnum)
  simpa only [div_eq_mul_inv, mul_comm] using hfinal

/-- The profile condition guarantees positive semidefiniteness. Degenerate
one-dimensional choices may give the zero matrix, so strict positivity is
asserted separately for the canonical comparison. -/
theorem lowerComparison_posSemidef {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {A c : ℝ}
    (hprofile : LowerComparisonProfile (spectralMaximum R hR.isHermitian / frobenius R) A c) :
    (lowerComparison R A c).PosSemidef := by
  rw [lowerComparison_spectral hR]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  have hη := frobenius_pos hR
  have hs := trace_square_pos hR
  have hf := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian] at hf
  let r := hR.isHermitian.eigenvalues
  have hri : 0 < r i := hR.eigenvalues_pos i
  have hrη : r i ≤ frobenius R :=
    (eigenvalue_le_spectralMaximum hR.isHermitian i).trans
      (spectralMaximum_le_frobenius hR.posSemidef)
  have hκ : 0 ≤ spectralMaximum R hR.isHermitian / frobenius R :=
    div_nonneg ((hri.le).trans (eigenvalue_le_spectralMaximum hR.isHermitian i)) hη.le
  have hz0 : 0 ≤ r i / frobenius R := div_nonneg hri.le hη.le
  have hz1 : r i / frobenius R ≤ 1 := (div_le_one hη).mpr hrη
  have hp := hprofile (r i / frobenius R) hz0 hz1
  have hm : 0 ≤ min (spectralMaximum R hR.isHermitian / frobenius R)
      (Real.sqrt (1 - (r i / frobenius R) ^ 2)) :=
    le_min hκ (Real.sqrt_nonneg _)
  have ha : (c - 1) * r i ≤ A * frobenius R := by
    have hp' : (c - 1) * (r i / frobenius R) ≤ A :=
      (le_add_of_nonneg_left hm).trans hp
    exact (div_le_iff₀ hη).mp (by simpa only [mul_div_assoc] using hp')
  have hpi0 : 0 ≤ r i ^ 2 / Matrix.trace (R ^ 2) := div_nonneg (sq_nonneg _) hs.le
  have hpi1 : r i ^ 2 / Matrix.trace (R ^ 2) ≤ 1 := by
    apply (div_le_one hs).mpr
    exact (pow_le_pow_left₀ hri.le hrη 2).trans_eq hf
  have hmul := mul_le_mul_of_nonneg_left
    (show -r i ≤ A * frobenius R - c * r i by linarith) hpi0
  have hsmall := mul_le_mul_of_nonneg_right hpi1 hri.le
  change 0 ≤ r i + r i ^ 2 / Matrix.trace (R ^ 2) * (A * frobenius R - c * r i)
  nlinarith only [hmul, hsmall]

/-- The canonical comparison `B₀=R+P(M I-R)`. -/
def lowerComparison0 (R : Matrix ι ι ℝ) (hR : R.PosDef) : Matrix ι ι ℝ :=
  lowerComparison R (spectralMaximum R hR.isHermitian / frobenius R) 1

theorem lowerComparison0_eq {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    lowerComparison0 R hR = R + lowerWeight R *
      (spectralMaximum R hR.isHermitian • (1 : Matrix ι ι ℝ) - R) := by
  unfold lowerComparison0 lowerComparison
  rw [div_mul_cancel₀ _ (frobenius_pos hR).ne', one_smul]

theorem lowerComparison0_posDef {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (lowerComparison0 R hR).PosDef := by
  unfold lowerComparison0
  rw [lowerComparison_spectral hR]
  apply unitary_conjugate_posDef
  apply Matrix.PosDef.diagonal
  intro i
  rw [div_mul_cancel₀ _ (frobenius_pos hR).ne', one_mul]
  exact add_pos_of_pos_of_nonneg (hR.eigenvalues_pos i)
    (mul_nonneg (div_nonneg (sq_nonneg _) (trace_square_pos hR).le)
      (sub_nonneg.mpr (eigenvalue_le_spectralMaximum hR.isHermitian i)))

theorem lowerShift_comparison0 {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    x ⬝ᵥ (lowerWeight R *ᵥ x) ≤
      (1 + x ⬝ᵥ (lowerComparison0 R hR *ᵥ x)) * lowerShift R hR x := by
  apply lowerShift_quadratic_comparison hR x
  intro z hz0 hz1
  simp only [sub_self, zero_mul, add_zero]
  exact min_le_left _ _

end
end SingularValueBounds.KL
