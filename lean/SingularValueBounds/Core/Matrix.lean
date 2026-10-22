import Mathlib

/-! # Shared real matrix and rank-one algebra -/

open scoped BigOperators Matrix

namespace SingularValueBounds

theorem positive_diagonal_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    (Matrix.diagonal r)⁻¹ = Matrix.diagonal (fun i => (r i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => r i * (r i)⁻¹) = (fun _ => (1 : ℝ)) := by
    funext i
    exact mul_inv_cancel₀ (ne_of_gt (hr i))
  rw [h, Matrix.diagonal_one]

theorem unitary_conjugate_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A B : Matrix ι ι ℝ) :
    ((U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ)) *
        ((U : Matrix ι ι ℝ) * B * star (U : Matrix ι ι ℝ)) =
      (U : Matrix ι ι ℝ) * (A * B) * star (U : Matrix ι ι ℝ) := by
  calc
    _ = (U : Matrix ι ι ℝ) * A *
      (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) * B *
      star (U : Matrix ι ι ℝ) := by noncomm_ring
    _ = _ := by rw [U.2.1]; simp only [mul_one, Matrix.mul_assoc]

theorem unitary_conjugate_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    Matrix.trace ((U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ)) =
      Matrix.trace A := by
  rw [Matrix.trace_mul_cycle, U.2.1, one_mul]

/-- The real spectral theorem, with the scalar coercions removed. -/
theorem real_spectral_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    R = (hR.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal hR.eigenvalues *
      star (hR.eigenvectorUnitary : Matrix ι ι ℝ) := by
  simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hR.spectral_theorem

theorem real_spectral_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    R ^ 2 = (hR.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => hR.eigenvalues i ^ 2) *
        star (hR.eigenvectorUnitary : Matrix ι ι ℝ) := by
  calc
    R ^ 2 = ((hR.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal hR.eigenvalues *
      star (hR.eigenvectorUnitary : Matrix ι ι ℝ)) ^ 2 :=
      congrArg (fun A : Matrix ι ι ℝ => A ^ 2) (real_spectral_decomposition hR)
    _ = _ := by
      rw [pow_two, unitary_conjugate_mul, Matrix.diagonal_mul_diagonal]
      simp only [pow_two]

theorem real_spectral_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    Matrix.trace R = ∑ i, hR.eigenvalues i := by
  have h := congrArg Matrix.trace (real_spectral_decomposition hR)
  simpa only [unitary_conjugate_trace, Matrix.trace_diagonal] using h

theorem real_spectral_trace_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    Matrix.trace (R ^ 2) = ∑ i, hR.eigenvalues i ^ 2 := by
  have h := congrArg Matrix.trace (real_spectral_square hR)
  simpa only [unitary_conjugate_trace, Matrix.trace_diagonal] using h

theorem eigenvalue_gap_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian) {a ε : ℝ}
    (hgap : (a • (1 : Matrix ι ι ℝ) - ε • H).PosDef) (j : ι) :
    0 < a - ε * hH.eigenvalues j := by
  have hq := hgap.re_dotProduct_pos (hH.eigenvectorBasis.orthonormal.ne_zero j)
  have hv : (star ⇑(hH.eigenvectorBasis j)) ⬝ᵥ ⇑(hH.eigenvectorBasis j) = (1 : ℝ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hH.eigenvectorBasis.orthonormal.1 j]
    norm_num
  change 0 < (star ⇑(hH.eigenvectorBasis j)) ⬝ᵥ
    ((a • (1 : Matrix ι ι ℝ) - ε • H) *ᵥ ⇑(hH.eigenvectorBasis j)) at hq
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, hH.mulVec_eigenvectorBasis, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, dotProduct_smul, hv] at hq
  simpa only [mul_one, smul_eq_mul] using hq

theorem unitary_conjugate_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    ((U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ))⁻¹ =
      (U : Matrix ι ι ℝ) * A⁻¹ * star (U : Matrix ι ι ℝ) := by
  have hU : (U : Matrix ι ι ℝ)⁻¹ = star (U : Matrix ι ι ℝ) :=
    Matrix.inv_eq_right_inv U.2.2
  have hUs : (star (U : Matrix ι ι ℝ))⁻¹ = (U : Matrix ι ι ℝ) :=
    Matrix.inv_eq_right_inv U.2.1
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hU, hUs, Matrix.mul_assoc]

theorem unitary_conjugate_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    ((U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ)).PosDef := by
  have hinj : Function.Injective (Matrix.mulVec (star (U : Matrix ι ι ℝ))) := by
    intro a b hab
    have h := congrArg (Matrix.mulVec (U : Matrix ι ι ℝ)) hab
    simpa only [Matrix.mulVec_mulVec, U.2.2, Matrix.one_mulVec] using h
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
    hA.conjTranspose_mul_mul_same hinj

theorem mul_outer {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (b c : ι → ℝ) :
    A * Matrix.vecMulVec b c = Matrix.vecMulVec (A *ᵥ b) c := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem outer_mul {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (C : Matrix ι ι ℝ) :
    Matrix.vecMulVec a b * C = Matrix.vecMulVec a (b ᵥ* C) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem unitary_conjugate_outer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (y : ι → ℝ) :
    (U : Matrix ι ι ℝ) * Matrix.vecMulVec y y * star (U : Matrix ι ι ℝ) =
      Matrix.vecMulVec ((U : Matrix ι ι ℝ) *ᵥ y) ((U : Matrix ι ι ℝ) *ᵥ y) := by
  rw [mul_outer, outer_mul]
  apply congrArg (Matrix.vecMulVec ((U : Matrix ι ι ℝ) *ᵥ y))
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.vecMul_transpose (U : Matrix ι ι ℝ) y

theorem quadratic_conjugate_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (r x : ι → ℝ) :
    x ⬝ᵥ (((U : Matrix ι ι ℝ) * Matrix.diagonal r *
      star (U : Matrix ι ι ℝ)) *ᵥ x) =
      ∑ i, (star (U : Matrix ι ι ℝ) *ᵥ x) i ^ 2 * r i := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hv : x ᵥ* (U : Matrix ι ι ℝ) = star (U : Matrix ι ι ℝ) *ᵥ x := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mulVec_transpose (U : Matrix ι ι ℝ) x).symm
  rw [hv]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem diagonal_mul_outer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c : ι → ℝ) :
    Matrix.diagonal a * Matrix.vecMulVec b c =
      Matrix.vecMulVec (fun i => a i * b i) c := by
  ext i j
  simp [Matrix.diagonal_mul, Matrix.vecMulVec, mul_assoc]

theorem outer_mul_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c : ι → ℝ) :
    Matrix.vecMulVec a b * Matrix.diagonal c =
      Matrix.vecMulVec a (fun i => b i * c i) := by
  ext i j
  simp [Matrix.mul_diagonal, Matrix.vecMulVec, mul_assoc]

theorem outer_mul_outer {ι : Type*} [Fintype ι]
    (a b c d : ι → ℝ) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d =
      (∑ i, b i * c i) • Matrix.vecMulVec a d := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The outer product of a real vector with itself is positive semidefinite. -/
theorem outer_posSemidef {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (Matrix.vecMulVec x x).PosSemidef := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec, mul_comm]
  · intro y
    have hid : star y ⬝ᵥ Matrix.vecMulVec x x *ᵥ y = (∑ i, x i * y i) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Pi.star_apply,
        star_trivial, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hid]
    exact sq_nonneg _

/-- A fully explicit Sherman--Morrison identity for a positive diagonal matrix. -/
theorem diagonal_rankOne_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a x : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (Matrix.diagonal a + Matrix.vecMulVec x x)⁻¹ =
      Matrix.diagonal (fun i => (a i)⁻¹) -
        (1 + ∑ i, x i ^ 2 / a i)⁻¹ •
          Matrix.vecMulVec (fun i => x i / a i) (fun i => x i / a i) := by
  have hq : 0 ≤ ∑ i, x i ^ 2 / a i :=
    Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (le_of_lt (ha i)))
  have hz : 1 + ∑ i, x i ^ 2 / a i ≠ 0 := by positivity
  apply Matrix.inv_eq_right_inv
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
  rw [Matrix.diagonal_mul_diagonal, diagonal_mul_outer, outer_mul_diagonal,
    outer_mul_outer]
  have hab : (fun i => a i * (a i)⁻¹) = (fun _ => (1 : ℝ)) := by
    funext i
    exact mul_inv_cancel₀ (ne_of_gt (ha i))
  have hax : (fun i => a i * (x i / a i)) = x := by
    funext i
    field_simp [ne_of_gt (ha i)]
  have hxx : (fun i => x i * (a i)⁻¹) = (fun i => x i / a i) := by
    funext i
    rw [div_eq_mul_inv]
  have hsum : (∑ i, x i * (x i / a i)) = ∑ i, x i ^ 2 / a i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hab, Matrix.diagonal_one, hax, hxx, hsum]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp [hz]
  ring


end SingularValueBounds
