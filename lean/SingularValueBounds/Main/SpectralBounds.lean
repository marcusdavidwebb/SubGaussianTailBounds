import SingularValueBounds.Main.Statement
import SingularValueBounds.Core.Matrix

/-! # Passing from positive definite gaps to actual singular values -/

open scoped Matrix BigOperators

namespace SingularValueBounds

noncomputable section

theorem singularValues_sq {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    singularValues S j ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self S).eigenvalues j := by
  exact Real.sq_sqrt ((Matrix.posSemidef_conjTranspose_mul_self S).eigenvalues_nonneg j)

theorem smallestSingularValue_sq_gt {m n : ℕ} [NeZero n]
    (S : Matrix (Fin m) (Fin n) ℝ) {a : ℝ}
    (hgap : (a • (1 : Matrix (Fin n) (Fin n) ℝ) - (-1 : ℝ) • (Sᴴ * S)).PosDef) :
    -a < smallestSingularValue S ^ 2 := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    Finset.univ_nonempty (singularValues S)
  change smallestSingularValue S = singularValues S j at hj
  rw [hj, singularValues_sq]
  have h := eigenvalue_gap_pos (Matrix.isHermitian_conjTranspose_mul_self S) hgap j
  linarith

theorem largestSingularValue_sq_lt {m n : ℕ} [NeZero n]
    (S : Matrix (Fin m) (Fin n) ℝ) {a : ℝ}
    (hgap : (a • (1 : Matrix (Fin n) (Fin n) ℝ) - (1 : ℝ) • (Sᴴ * S)).PosDef) :
    largestSingularValue S ^ 2 < a := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (singularValues S)
  change largestSingularValue S = singularValues S j at hj
  rw [hj, singularValues_sq]
  have h := eigenvalue_gap_pos (Matrix.isHermitian_conjTranspose_mul_self S) hgap j
  linarith

theorem gram_eq_sum_outer {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) :
    Sᴴ * S = ∑ i : Fin m, Matrix.vecMulVec (S i) (S i) := by
  ext j k
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.sum_apply]

end
end SingularValueBounds
