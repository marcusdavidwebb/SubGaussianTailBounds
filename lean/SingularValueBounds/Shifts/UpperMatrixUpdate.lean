import SingularValueBounds.Shifts.UpperRoot

/-! # Rank-one subtraction and upper-barrier potential preservation -/

open scoped Matrix BigOperators

namespace SingularValueBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem weighted_matrix_cauchy (a x y : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2 / a i) * (∑ i, a i * y i ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro i _
    exact div_nonneg (sq_nonneg _) (ha i).le
  · intro i _
    exact mul_nonneg (ha i).le (sq_nonneg _)
  · intro i _
    field_simp [(ha i).ne']
    ring

omit [DecidableEq ι] in
theorem outer_quadratic (x y : ι → ℝ) :
    y ⬝ᵥ (Matrix.vecMulVec x x *ᵥ y) = (∑ i, x i * y i) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem diagonal_sub_outer_posDef (a x : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hq : (∑ i, x i ^ 2 / a i) < 1) :
    (Matrix.diagonal a - Matrix.vecMulVec x x).PosDef := by
  refine ⟨(Matrix.PosDef.diagonal ha).isHermitian.sub (outer_posSemidef x).isHermitian, ?_⟩
  intro y hy
  have hpos := (Matrix.PosDef.diagonal ha).2 y hy
  have hdiag : y ⬝ᵥ (Matrix.diagonal a *ᵥ y) = ∑ i, a i * y i ^ 2 := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [star_trivial, hdiag] at hpos
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hdiag, outer_quadratic]
  have hcs := weighted_matrix_cauchy a x y ha
  nlinarith [mul_pos (sub_pos.mpr hq) hpos]

theorem diagonal_sub_outer_criterion (a x : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hG : (Matrix.diagonal a - Matrix.vecMulVec x x).PosDef) :
    (∑ i, x i ^ 2 / a i) < 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · let y := fun i => x i / a i
    have hy : y ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      intro hz
      have hzi := congrFun hz i
      change x i / a i = 0 at hzi
      exact hi ((div_eq_zero_iff).mp hzi |>.resolve_right (ha i).ne')
    have hp := hG.2 y hy
    have hsum : (∑ i, x i * y i) = ∑ i, x i ^ 2 / a i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [y]
      ring
    have hdiag : y ⬝ᵥ (Matrix.diagonal a *ᵥ y) = ∑ i, x i ^ 2 / a i := by
      simp only [dotProduct, Matrix.mulVec_diagonal]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [y]
      field_simp [(ha i).ne']
      ring
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hdiag, outer_quadratic, hsum] at hp
    nlinarith [sq_nonneg ((∑ i, x i ^ 2 / a i) - 1)]

/-- Sherman--Morrison for rank-one subtraction from a positive diagonal matrix. -/
theorem diagonal_sub_rankOne_inverse (a x : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hq : (∑ i, x i ^ 2 / a i) < 1) :
    (Matrix.diagonal a - Matrix.vecMulVec x x)⁻¹ =
      Matrix.diagonal (fun i => (a i)⁻¹) +
        (1 - ∑ i, x i ^ 2 / a i)⁻¹ •
          Matrix.vecMulVec (fun i => x i / a i) (fun i => x i / a i) := by
  have hz : 1 - ∑ i, x i ^ 2 / a i ≠ 0 := (sub_pos.mpr hq).ne'
  apply Matrix.inv_eq_right_inv
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [Matrix.diagonal_mul_diagonal, diagonal_mul_outer, outer_mul_diagonal, outer_mul_outer]
  have hab : (fun i => a i * (a i)⁻¹) = (fun _ => (1 : ℝ)) := by
    funext i
    exact mul_inv_cancel₀ (ha i).ne'
  have hax : (fun i => a i * (x i / a i)) = x := by
    funext i
    field_simp [(ha i).ne']
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

theorem diagonal_sub_rankOne_trace (a x : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hq : (∑ i, x i ^ 2 / a i) < 1) :
    Matrix.trace (Matrix.diagonal a - Matrix.vecMulVec x x)⁻¹ =
      (∑ i, (a i)⁻¹) + (∑ i, x i ^ 2 / a i ^ 2) / (1 - ∑ i, x i ^ 2 / a i) := by
  rw [diagonal_sub_rankOne_inverse a x ha hq, Matrix.trace_add, Matrix.trace_diagonal,
    Matrix.trace_smul]
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, smul_eq_mul, div_eq_mul_inv]
  congr 1
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spectral_upperShift_preserves [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) {x : ι → ℝ} (hx : x ≠ 0) :
    let δ := spectralUpperShift r hr x
    let G := Matrix.diagonal (fun i => (r i)⁻¹ + δ) - Matrix.vecMulVec x x
    G.PosDef ∧ Matrix.trace G⁻¹ = ∑ i, r i := by
  let δ := spectralUpperShift r hr x
  let s := spectralUpperResolvent r δ
  let d := spectralUpperDrop r δ
  have hδ : 0 < δ := spectralUpperShift_pos hr hx
  have hs : ∀ i, 0 < s i := spectralUpperResolvent_pos hr hδ.le
  have hd : 0 < d := spectralUpperDrop_pos hr hδ
  have heq := spectralUpperShift_equation hr hx
  change (∑ i, x i ^ 2 * (s i + s i ^ 2 / d)) = 1 at heq
  simp only [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, ← Finset.sum_div] at heq
  have hq2 : 0 < ∑ i, x i ^ 2 * s i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (mul_pos (sq_pos_of_ne_zero hi) (sq_pos_of_pos (hs i)))
      (Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ i))
  have hq1 : (∑ i, x i ^ 2 * s i) < 1 := by
    linarith [div_pos hq2 hd]
  have ha : ∀ i, 0 < (r i)⁻¹ + δ := fun i => add_pos (inv_pos.mpr (hr i)) hδ
  have hinv : ∀ i, ((r i)⁻¹ + δ)⁻¹ = s i := by
    intro i
    dsimp [s, spectralUpperResolvent]
    have hdi : 0 < 1 + δ * r i := by nlinarith [mul_pos hδ (hr i)]
    field_simp [(hr i).ne', hdi.ne']
  have hq1' : (∑ i, x i ^ 2 / ((r i)⁻¹ + δ)) < 1 := by
    simpa only [div_eq_mul_inv, hinv] using hq1
  change (Matrix.diagonal (fun i => (r i)⁻¹ + δ) - Matrix.vecMulVec x x).PosDef ∧ _
  refine ⟨diagonal_sub_outer_posDef _ _ ha hq1', ?_⟩
  rw [diagonal_sub_rankOne_trace _ _ ha hq1']
  simp only [div_eq_mul_inv, ← inv_pow, hinv]
  have hratio : (∑ i, x i ^ 2 * s i ^ 2) / (1 - ∑ i, x i ^ 2 * s i) = d := by
    have hmult : (∑ i, x i ^ 2 * s i ^ 2) = d * (1 - ∑ i, x i ^ 2 * s i) := by
      have htemp : (∑ i, x i ^ 2 * s i ^ 2) / d = 1 - ∑ i, x i ^ 2 * s i := by
        linarith
      have := (div_eq_iff hd.ne').mp htemp
      nlinarith only [this]
    apply (div_eq_iff (sub_pos.mpr hq1).ne').2
    exact hmult
  rw [← div_eq_mul_inv, hratio]
  dsimp [d, spectralUpperDrop, s]
  ring

/-- Deterministic matrix conclusion in Lemma 3.2: the exact shift stays above
the updated spectrum and preserves the inverse-trace potential. -/
theorem upperShift_preserves [Nonempty ι] {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (x : ι → ℝ) :
    let G := R⁻¹ + upperShift R hR x • (1 : Matrix ι ι ℝ) - Matrix.vecMulVec x x
    G.PosDef ∧ Matrix.trace G⁻¹ = Matrix.trace R := by
  by_cases hx : x = 0
  · subst x
    have houter : Matrix.vecMulVec (0 : ι → ℝ) (0 : ι → ℝ) = 0 := by
      ext i j; simp [Matrix.vecMulVec]
    simp only [upperShift_zero, zero_smul, add_zero, houter, sub_zero]
    refine ⟨hR.inv, ?_⟩
    rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit)]
  · let U := hR.isHermitian.eigenvectorUnitary
    let r := hR.isHermitian.eigenvalues
    let y := star (U : Matrix ι ι ℝ) *ᵥ x
    let δ := upperShift R hR x
    have hr : ∀ i, 0 < r i := hR.eigenvalues_pos
    have hy : y ≠ 0 := upper_coordinates_ne_zero hR hx
    have hdiag := spectral_upperShift_preserves hr hy
    change (Matrix.diagonal (fun i => (r i)⁻¹ + δ) - Matrix.vecMulVec y y).PosDef ∧ _ at hdiag
    have hxy : (U : Matrix ι ι ℝ) *ᵥ y = x := by
      dsimp [y]
      rw [Matrix.mulVec_mulVec, U.2.2, Matrix.one_mulVec]
    have houter : Matrix.vecMulVec x x = (U : Matrix ι ι ℝ) * Matrix.vecMulVec y y *
        star (U : Matrix ι ι ℝ) := by rw [unitary_conjugate_outer, hxy]
    have hd : Matrix.diagonal (fun i => (r i)⁻¹ + δ) =
        Matrix.diagonal (fun i => (r i)⁻¹) + δ • (1 : Matrix ι ι ℝ) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
    have hG : R⁻¹ + δ • (1 : Matrix ι ι ℝ) - Matrix.vecMulVec x x =
        (U : Matrix ι ι ℝ) *
          (Matrix.diagonal (fun i => (r i)⁻¹ + δ) - Matrix.vecMulVec y y) *
            star (U : Matrix ι ι ℝ) := by
      rw [real_spectral_decomposition hR.isHermitian, unitary_conjugate_inverse,
        positive_diagonal_inverse _ hr, houter, hd, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_add, Matrix.add_mul, unitary_conjugate_scalar]
    change (R⁻¹ + δ • (1 : Matrix ι ι ℝ) - Matrix.vecMulVec x x).PosDef ∧ _
    rw [hG]
    refine ⟨unitary_conjugate_posDef U _ hdiag.1, ?_⟩
    rw [unitary_conjugate_inverse, unitary_conjugate_trace, real_spectral_trace hR.isHermitian]
    exact hdiag.2

theorem spectral_upperShift_unique_preserves [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) (x : ι → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hG : (Matrix.diagonal (fun i => (r i)⁻¹ + h) - Matrix.vecMulVec x x).PosDef)
    (htrace : Matrix.trace (Matrix.diagonal (fun i => (r i)⁻¹ + h) - Matrix.vecMulVec x x)⁻¹ =
      ∑ i, r i) : h = spectralUpperShift r hr x := by
  let s := spectralUpperResolvent r h
  let d := spectralUpperDrop r h
  have ha : ∀ i, 0 < (r i)⁻¹ + h :=
    fun i => add_pos_of_pos_of_nonneg (inv_pos.mpr (hr i)) hh
  have hinv : ∀ i, ((r i)⁻¹ + h)⁻¹ = s i := by
    intro i
    dsimp [s, spectralUpperResolvent]
    have hdi : 0 < 1 + h * r i := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le)
    field_simp [(hr i).ne', hdi.ne']
  have hq := diagonal_sub_outer_criterion _ _ ha hG
  rw [diagonal_sub_rankOne_trace _ _ ha hq] at htrace
  simp only [div_eq_mul_inv, ← inv_pow, hinv] at htrace hq
  have hratio : (∑ i, x i ^ 2 * s i ^ 2) / (1 - ∑ i, x i ^ 2 * s i) = d := by
    dsimp [d, spectralUpperDrop]
    rw [div_eq_mul_inv]
    linarith
  by_cases hx : x = 0
  · subst x
    rw [spectralUpperShift_zero]
    have hd0 : d = 0 := by simpa using hratio.symm
    by_contra hn
    have hp : 0 < h := lt_of_le_of_ne hh (Ne.symm hn)
    have := spectralUpperDrop_pos hr hp
    change 0 < d at this
    linarith
  · have hq2 : 0 < ∑ i, x i ^ 2 * s i ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      exact lt_of_lt_of_le (mul_pos (sq_pos_of_ne_zero hi)
        (sq_pos_of_pos (spectralUpperResolvent_pos hr hh i)))
        (Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ i))
    have hdpos : 0 < d := by rw [← hratio]; exact div_pos hq2 (sub_pos.mpr hq)
    have hp : 0 < h := by
      by_contra hn
      have hz : h = 0 := le_antisymm (le_of_not_gt hn) hh
      simp only [d, spectralUpperDrop, spectralUpperResolvent, hz, zero_mul, add_zero,
        div_one, sub_self, lt_self_iff_false] at hdpos
    apply spectralUpperShift_unique hr hx hp
    apply (spectralUpperEquation_iff_criterion hr x hp).1
    change (∑ i, x i ^ 2 * s i ^ 2) - d * (1 - ∑ i, x i ^ 2 * s i) = 0
    have := (div_eq_iff (sub_pos.mpr hq).ne').mp hratio
    nlinarith only [this]

theorem unitary_conjugate_posDef_iff (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    ((U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ)).PosDef ↔ A.PosDef := by
  refine ⟨?_, unitary_conjugate_posDef U A⟩
  intro h
  have hinj : Function.Injective (Matrix.mulVec (U : Matrix ι ι ℝ)) := by
    intro x y heq
    have := congrArg (Matrix.mulVec (star (U : Matrix ι ι ℝ))) heq
    simpa only [Matrix.mulVec_mulVec, U.2.1, Matrix.one_mulVec] using this
  have hp := h.conjTranspose_mul_mul_same hinj
  have hid : (U : Matrix ι ι ℝ)ᴴ *
      ((U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ)) * (U : Matrix ι ι ℝ) = A := by
    rw [← Matrix.star_eq_conjTranspose]
    calc
      _ = (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) * A *
        (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) := by noncomm_ring
      _ = _ := by rw [U.2.1]; simp
  rwa [hid] at hp

/-- Uniqueness in the literal potential-preserving formulation of Lemma 3.2,
including zero vectors and zero candidate shifts. -/
theorem upperShift_unique_preserves [Nonempty ι] {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (x : ι → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hG : (R⁻¹ + h • (1 : Matrix ι ι ℝ) - Matrix.vecMulVec x x).PosDef)
    (htrace : Matrix.trace (R⁻¹ + h • (1 : Matrix ι ι ℝ) - Matrix.vecMulVec x x)⁻¹ =
      Matrix.trace R) : h = upperShift R hR x := by
  let U := hR.isHermitian.eigenvectorUnitary
  let r := hR.isHermitian.eigenvalues
  let y := star (U : Matrix ι ι ℝ) *ᵥ x
  have hr : ∀ i, 0 < r i := hR.eigenvalues_pos
  have hxy : (U : Matrix ι ι ℝ) *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, U.2.2, Matrix.one_mulVec]
  have houter : Matrix.vecMulVec x x = (U : Matrix ι ι ℝ) * Matrix.vecMulVec y y *
      star (U : Matrix ι ι ℝ) := by rw [unitary_conjugate_outer, hxy]
  have hd : Matrix.diagonal (fun i => (r i)⁻¹ + h) =
      Matrix.diagonal (fun i => (r i)⁻¹) + h • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have hform : R⁻¹ + h • (1 : Matrix ι ι ℝ) - Matrix.vecMulVec x x =
      (U : Matrix ι ι ℝ) *
        (Matrix.diagonal (fun i => (r i)⁻¹ + h) - Matrix.vecMulVec y y) *
          star (U : Matrix ι ι ℝ) := by
    rw [real_spectral_decomposition hR.isHermitian, unitary_conjugate_inverse,
      positive_diagonal_inverse _ hr, houter, hd, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_add, Matrix.add_mul, unitary_conjugate_scalar]
  rw [hform, unitary_conjugate_posDef_iff] at hG
  rw [hform, unitary_conjugate_inverse, unitary_conjugate_trace,
    real_spectral_trace hR.isHermitian] at htrace
  exact spectral_upperShift_unique_preserves hr y hh hG htrace

end SingularValueBounds
