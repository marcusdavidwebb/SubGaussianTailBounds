import NLAlib.Matrix.Spectral.SingularValues

/-!
# Compatibility of the singular-value definitions

The preceding canonical statement used the minimum and maximum of the square
roots of the Gram eigenvalues. NLA-lib instead supplies the singular values as
a decreasing sequence, padded with zeros. The following equivalences justify
using its entries `n - 1` and `0`, including for rank-deficient matrices.

The proof uses NLA-lib's permutation between the Gram eigenvalues and its
ordered eigenvalue sequence, and `NLAlib.singularValues_sq`. No relation between
the number of rows and columns is needed.
-/

namespace SubGaussian.Previous

/-- The minimum used by the preceding canonical statement. -/
noncomputable def smallestSingularValue {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (Finset.univ.image (fun j =>
    √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j))).min' (by
      classical
      exact ⟨_, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩)

/-- The maximum used by the preceding canonical statement. -/
noncomputable def largestSingularValue {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (Finset.univ.image (fun j =>
    √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j))).max' (by
      classical
      exact ⟨_, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩)

private theorem exists_equiv_sqrt_eigenvalues_eq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ e : Fin n ≃ Fin (Fintype.card (Fin n)), ∀ j,
      √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j) =
        NLAlib.singularValues A (e j) := by
  have h := (Matrix.isHermitian_conjTranspose_mul_self A).exists_equiv_eigenvalue_eq
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun j => ?_⟩
  rw [he j, ← NLAlib.singularValues_sq, Real.sqrt_sq (NLAlib.singularValues_nonneg A _)]

/-- The old minimum is the last singular value indexed by the columns,
including zeros when the matrix does not have full column rank. -/
theorem smallestSingularValue_eq_nla {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    smallestSingularValue hn A = NLAlib.singularValues A (n - 1) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_sqrt_eigenvalues_eq A
  let j : Fin (Fintype.card (Fin n)) := ⟨n - 1, by simp only [Fintype.card_fin]; omega⟩
  apply le_antisymm
  · unfold smallestSingularValue
    apply Finset.min'_le
    refine Finset.mem_image.mpr ⟨e.symm j, Finset.mem_univ _, ?_⟩
    simpa only [Equiv.apply_symm_apply] using he (e.symm j)
  · unfold smallestSingularValue
    apply Finset.le_min'
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [he i]
    apply NLAlib.singularValues_antitone A
    have hi : (e i).val < n := by simpa only [Fintype.card_fin] using (e i).isLt
    omega

/-- The old maximum is NLA-lib's zeroth singular value. -/
theorem largestSingularValue_eq_nla {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    largestSingularValue hn A = NLAlib.singularValues A 0 := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_sqrt_eigenvalues_eq A
  let j : Fin (Fintype.card (Fin n)) := ⟨0, by simp only [Fintype.card_fin]; omega⟩
  apply le_antisymm
  · unfold largestSingularValue
    apply Finset.max'_le
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [he i]
    exact NLAlib.singularValues_antitone A (Nat.zero_le _)
  · unfold largestSingularValue
    apply Finset.le_max'
    refine Finset.mem_image.mpr ⟨e.symm j, Finset.mem_univ _, ?_⟩
    simpa only [Equiv.apply_symm_apply] using he (e.symm j)

end SubGaussian.Previous
