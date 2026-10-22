import SingularValueBounds.Shifts.UpperRoot

/-! # Scalar determinant factor bound for the upper-shift tail -/

open scoped BigOperators Matrix

namespace SingularValueBounds

noncomputable section

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem one_sub_sum_le_prod_one_sub (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hi0 := ha i (Finset.mem_insert_self _ _)
    have hi1 := ha1 i (Finset.mem_insert_self _ _)
    have hs0 : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hs1 : ∀ j ∈ s, a j ≤ 1 := fun j hj => ha1 j (Finset.mem_insert_of_mem hj)
    have hsum := Finset.sum_nonneg hs0
    have hmul := mul_le_mul_of_nonneg_left (ih hs0 hs1) (sub_nonneg.mpr hi1)
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith [mul_nonneg hi0 hsum]

private theorem upper_first_factor_exp {r h t : ℝ} (hr : 0 < r)
    (ht : 0 ≤ t) (hth : t ≤ h) :
    Real.exp (-(t * r)) ≤ 1 - t * (r / (1 + h * r)) := by
  have hh : 0 ≤ h := ht.trans hth
  have hdt : 0 < 1 + t * r := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht hr.le)
  have hdh : 0 < 1 + h * r := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh hr.le)
  have hexp : Real.exp (-(t * r)) ≤ 1 / (1 + t * r) := by
    rw [Real.exp_neg]
    have h := one_div_le_one_div_of_le hdt
      (show 1 + t * r ≤ Real.exp (t * r) by linarith [Real.add_one_le_exp (t * r)])
    simpa only [one_div] using h
  apply hexp.trans
  have heq : 1 - t * (r / (1 + h * r)) = (1 + (h - t) * r) / (1 + h * r) := by
    field_simp [hdh.ne']
    ring
  rw [heq]
  apply (div_le_div_iff₀ hdt hdh).2
  nlinarith [mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hth)) (sq_nonneg r)]

def upperDeterminantCorrection (r : ι → ℝ) (h t : ℝ) (i : ι) : ℝ :=
  r i ^ 2 / ((1 + h * r i) * (1 + (h - t) * r i) * spectralUpperDrop r h)

theorem upperDeterminantCorrection_sum [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) {h t : ℝ} (hh : 0 < h) (hth : t ≤ h) :
    (∀ i, 0 ≤ upperDeterminantCorrection r h t i) ∧
      (∑ i, upperDeterminantCorrection r h t i) ≤ 1 / h := by
  have hd := spectralUpperDrop_pos hr hh
  have hdh : ∀ i, 0 < 1 + h * r i := fun i =>
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh.le (hr i).le)
  have hdt : ∀ i, 1 ≤ 1 + (h - t) * r i := fun i => by
    nlinarith [mul_nonneg (sub_nonneg.mpr hth) (hr i).le]
  have hc0 : ∀ i, 0 ≤ upperDeterminantCorrection r h t i := by
    intro i
    unfold upperDeterminantCorrection
    exact div_nonneg (sq_nonneg _) (mul_nonneg
      (mul_nonneg (hdh i).le (le_trans zero_le_one (hdt i))) hd.le)
  refine ⟨hc0, ?_⟩
  calc
    (∑ i, upperDeterminantCorrection r h t i) ≤
        ∑ i, (r i ^ 2 / (1 + h * r i)) / spectralUpperDrop r h := by
      apply Finset.sum_le_sum
      intro i _
      unfold upperDeterminantCorrection
      rw [div_div]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (hdh i) hd)
      have := mul_le_mul_of_nonneg_left (hdt i) (hdh i).le
      nlinarith [mul_le_mul_of_nonneg_right this hd.le]
    _ = 1 / h := by
      rw [← Finset.sum_div, spectralUpperDrop_eq hr hh.le]
      have hsum : 0 < ∑ i, r i ^ 2 / (1 + h * r i) :=
        Finset.sum_pos (fun i _ => div_pos (sq_pos_of_pos (hr i)) (hdh i)) Finset.univ_nonempty
      field_simp [hh.ne', hsum.ne']
      ring

/-- The finite-dimensional determinant estimate used in Lemma 3.2. The
parameter `t` is `2 K² λ`; the expression inside the product is an eigenvalue
of `I - t B_h`. -/
theorem upper_determinant_factor_bound [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) {h t : ℝ} (ht : 0 < t) (hth : t < h) :
    let b := fun i => spectralUpperResolvent r h i +
      spectralUpperResolvent r h i ^ 2 / spectralUpperDrop r h
    (∀ i, 0 < 1 - t * b i) ∧
      Real.exp (-(t * ∑ i, r i)) * (1 - t / h) ≤ ∏ i, (1 - t * b i) := by
  let f := fun i => 1 - t * spectralUpperResolvent r h i
  let c := upperDeterminantCorrection r h t
  have hh : 0 < h := ht.trans hth
  have hd := spectralUpperDrop_pos hr hh
  obtain ⟨hc0, hcsum⟩ := upperDeterminantCorrection_sum hr hh hth.le
  have hf : ∀ i, Real.exp (-(t * r i)) ≤ f i := fun i =>
    upper_first_factor_exp (hr i) ht.le hth.le
  have hfpos : ∀ i, 0 < f i := fun i => (Real.exp_pos _).trans_le (hf i)
  have htc : ∀ i, t * c i < 1 := by
    intro i
    have hsingle : c i ≤ ∑ j, c j :=
      Finset.single_le_sum (fun j _ => hc0 j) (Finset.mem_univ i)
    have hbound := mul_le_mul_of_nonneg_left (hsingle.trans hcsum) ht.le
    rw [mul_one_div] at hbound
    have hfrac : t / h < 1 := (div_lt_one hh).2 hth
    nlinarith only [hbound, hfrac]
  have hfactor : ∀ i, 1 - t * (spectralUpperResolvent r h i +
      spectralUpperResolvent r h i ^ 2 / spectralUpperDrop r h) = f i * (1 - t * c i) := by
    intro i
    dsimp [f, c, spectralUpperResolvent, upperDeterminantCorrection]
    have hdh : 0 < 1 + h * r i := by nlinarith [mul_pos hh (hr i)]
    have hdt : 0 < 1 + (h - t) * r i := by nlinarith [mul_pos (sub_pos.mpr hth) (hr i)]
    field_simp [hdh.ne', hdt.ne', hd.ne']
    ring
  constructor
  · intro i
    rw [hfactor]
    exact mul_pos (hfpos i) (sub_pos.mpr (htc i))
  · dsimp only
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib]
    have hfirst : Real.exp (-(t * ∑ i, r i)) ≤ ∏ i, f i := by
      have hp := Finset.prod_le_prod (s := Finset.univ)
        (fun i _ => (Real.exp_pos (-(t * r i))).le) (fun i _ => hf i)
      convert hp using 1
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.mul_sum, Finset.sum_neg_distrib]
    have hsecond : 1 - t / h ≤ ∏ i, (1 - t * c i) := by
      have hp := one_sub_sum_le_prod_one_sub Finset.univ (fun i => t * c i)
        (fun i _ => mul_nonneg ht.le (hc0 i)) (fun i _ => (htc i).le)
      rw [← Finset.mul_sum] at hp
      have hm := mul_le_mul_of_nonneg_left hcsum ht.le
      have htm : t * (1 / h) = t / h := by ring
      rw [htm] at hm
      exact (sub_le_sub_left hm 1).trans hp
    exact mul_le_mul hfirst hsecond (sub_nonneg.mpr ((div_lt_one hh).2 hth).le)
      (Finset.prod_nonneg (fun i _ => (hfpos i).le))

variable [DecidableEq ι]

theorem unitary_conjugate_det (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    Matrix.det ((U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ)) = Matrix.det A := by
  have hu : Matrix.det (U : Matrix ι ι ℝ) * Matrix.det (star (U : Matrix ι ι ℝ)) = 1 := by
    rw [← Matrix.det_mul, U.2.2, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    _ = Matrix.det A * (Matrix.det (U : Matrix ι ι ℝ) * Matrix.det (star (U : Matrix ι ι ℝ))) := by ring
    _ = _ := by rw [hu, mul_one]

theorem upperCriterion_posDef [Nonempty ι] {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 < h) : (upperCriterion R h).PosDef := by
  rw [upperCriterion_spectral hR hh.le]
  apply unitary_conjugate_posDef
  apply Matrix.PosDef.diagonal
  intro i
  have hr := hR.eigenvalues_pos i
  have hden : 0 < 1 + h * hR.isHermitian.eigenvalues i := by nlinarith [mul_pos hh hr]
  have hd := spectralUpperDrop_pos hR.eigenvalues_pos hh
  rw [spectralUpperDrop_eq hR.eigenvalues_pos hh.le] at hd
  exact add_pos_of_pos_of_nonneg (div_pos hr hden) (div_nonneg (sq_nonneg _) hd.le)

/-- Matrix form of the determinant estimate, independent of which orthogonal
eigenbasis is chosen for the quadratic-form MGF theorem. -/
theorem upperCriterion_determinant_bound [Nonempty ι] {R : Matrix ι ι ℝ}
    (hR : R.PosDef) {h t : ℝ} (ht : 0 < t) (hth : t < h) :
    ((1 : Matrix ι ι ℝ) - t • upperCriterion R h).PosDef ∧
      Real.exp (-(t * Matrix.trace R)) * (1 - t / h) ≤
        Matrix.det ((1 : Matrix ι ι ℝ) - t • upperCriterion R h) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let r := hR.isHermitian.eigenvalues
  let b := fun i => spectralUpperResolvent r h i +
    spectralUpperResolvent r h i ^ 2 / spectralUpperDrop r h
  have hr : ∀ i, 0 < r i := hR.eigenvalues_pos
  have hh : 0 < h := ht.trans hth
  have hB : upperCriterion R h = (U : Matrix ι ι ℝ) * Matrix.diagonal b * star (U : Matrix ι ι ℝ) := by
    rw [upperCriterion_spectral hR hh.le]
    simp only [b, spectralUpperResolvent, spectralUpperDrop_eq hr hh.le]
    rfl
  have hdiag : Matrix.diagonal (fun i => 1 - t * b i) =
      (1 : Matrix ι ι ℝ) - t • Matrix.diagonal b := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have hmat : (1 : Matrix ι ι ℝ) - t • upperCriterion R h =
      (U : Matrix ι ι ℝ) * Matrix.diagonal (fun i => 1 - t * b i) * star (U : Matrix ι ι ℝ) := by
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, U.2.2, hB]
  have hb := upper_determinant_factor_bound hr ht hth
  change (∀ i, 0 < 1 - t * b i) ∧ _ at hb
  rw [hmat]
  refine ⟨unitary_conjugate_posDef U _ (Matrix.PosDef.diagonal hb.1), ?_⟩
  rw [unitary_conjugate_det, Matrix.det_diagonal, real_spectral_trace hR.isHermitian]
  exact hb.2

end
end SingularValueBounds
