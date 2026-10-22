import SingularValueBounds.KL.Statement

/-! # Euclidean interpretation of the barrier norms

`frobenius` is the Euclidean norm of all matrix entries. The spectral maximum
is attained by a Euclidean unit eigenvector and bounds every Rayleigh
quotient. This supplies the Euclidean Rayleigh characterization of the
operator norm used for positive semidefinite resolvents.
-/

open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma quadratic_le_spectralMaximum {R : Matrix ι ι ℝ} (hR : R.IsHermitian)
    (x : ι → ℝ) :
    x ⬝ᵥ (R *ᵥ x) ≤ spectralMaximum R hR * (x ⬝ᵥ x) := by
  let U := hR.eigenvectorUnitary
  have hsum : (∑ i, (star (U : Matrix ι ι ℝ) *ᵥ x) i ^ 2) = x ⬝ᵥ x := by
    have h := quadratic_conjugate_diagonal U (fun _ => (1 : ℝ)) x
    simpa only [Matrix.diagonal_one, mul_one, U.2.2, Matrix.one_mulVec,
      mul_one] using h.symm
  have hq := congrArg (fun A : Matrix ι ι ℝ => x ⬝ᵥ (A *ᵥ x)) (real_spectral_decomposition hR)
  dsimp only at hq
  rw [quadratic_conjugate_diagonal] at hq
  rw [hq, ← hsum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [mul_le_mul_of_nonneg_left (eigenvalue_le_spectralMaximum hR i)
    (sq_nonneg ((star (U : Matrix ι ι ℝ) *ᵥ x) i))]


lemma euclidean_dot_self (x : EuclideanSpace ℝ ι) :
    (x : ι → ℝ) ⬝ᵥ (x : ι → ℝ) = ‖x‖ ^ 2 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
    (real_inner_self_eq_norm_sq x)

/-- Every Euclidean Rayleigh quotient is bounded by the spectral maximum. -/
theorem euclidean_quadratic_le_spectralMaximum {R : Matrix ι ι ℝ}
    (hR : R.IsHermitian) (x : EuclideanSpace ℝ ι) :
    (x : ι → ℝ) ⬝ᵥ (R *ᵥ (x : ι → ℝ)) ≤ spectralMaximum R hR * ‖x‖ ^ 2 := by
  rw [← euclidean_dot_self]
  exact quadratic_le_spectralMaximum hR x

/-- The spectral maximum is attained on the Euclidean unit sphere. -/
theorem spectralMaximum_attained {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    ∃ x : EuclideanSpace ℝ ι, ‖x‖ = 1 ∧
      (x : ι → ℝ) ⬝ᵥ (R *ᵥ (x : ι → ℝ)) = spectralMaximum R hR := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty hR.eigenvalues
  refine ⟨hR.eigenvectorBasis i, hR.eigenvectorBasis.orthonormal.norm_eq_one i, ?_⟩
  have he := hR.mulVec_eigenvectorBasis i
  change R *ᵥ (hR.eigenvectorBasis i : ι → ℝ) =
    hR.eigenvalues i • (hR.eigenvectorBasis i : ι → ℝ) at he
  rw [he, dotProduct_smul]
  simp only [smul_eq_mul]
  have hn := euclidean_dot_self (hR.eigenvectorBasis i)
  rw [hR.eigenvectorBasis.orthonormal.norm_eq_one i] at hn
  rw [hn]
  simpa only [one_pow, mul_one] using hi.symm

/-- Rayleigh characterization, with the Euclidean norm made explicit. -/
theorem spectralMaximum_le_iff_euclidean_quadratic {R : Matrix ι ι ℝ}
    (hR : R.IsHermitian) (b : ℝ) :
    spectralMaximum R hR ≤ b ↔ ∀ x : EuclideanSpace ℝ ι,
      (x : ι → ℝ) ⬝ᵥ (R *ᵥ (x : ι → ℝ)) ≤ b * ‖x‖ ^ 2 := by
  constructor
  · intro hb x
    exact (euclidean_quadratic_le_spectralMaximum hR x).trans
      (mul_le_mul_of_nonneg_right hb (sq_nonneg _))
  · intro hb
    obtain ⟨x, hx, hq⟩ := spectralMaximum_attained hR
    have h := hb x
    simpa only [hq, hx, one_pow, mul_one] using h

end
end SingularValueBounds.KL
