import SingularValueBounds.KL.Upper.ExactTails

/-! # The new fixed upper comparison (supplementary S1.6.2)
This is `R+P(tr(RP)I-2R)`, whose trace is `tr R-tr(RP)`.
It may be zero (in particular, in dimension one). -/
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The trace-one square of the resolvent. -/
def upperSquareWeight (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (Matrix.trace (R ^ 2))⁻¹ • R ^ 2

/-- The new, smaller fixed comparison from `app:upper-logdet`. -/
def upperFixedComparison (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  let P := upperSquareWeight R
  R + P * (Matrix.trace (R * P) • (1 : Matrix ι ι ℝ) - 2 • R)

/-- The eigenvalue of the new comparison. -/
def upperFixedEigenvalue (r : ι → ℝ) (i : ι) : ℝ :=
  r i + upperWeight r i * (upperWeightedMean r - 2 * r i)

theorem upperSquareWeight_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    upperSquareWeight R = (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (upperWeight hR.isHermitian.eigenvalues) *
        star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  unfold upperSquareWeight
  rw [real_spectral_trace_square hR.isHermitian, real_spectral_square hR.isHermitian]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  congr 2
  ext i j
  simp [Matrix.diagonal, upperWeight, div_eq_mul_inv, mul_comm]

theorem upperSquareWeight_mean {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix.trace (R * upperSquareWeight R) = upperWeightedMean hR.isHermitian.eigenvalues := by
  rw [upperSquareWeight_spectral hR]
  conv_lhs => arg 1; lhs; rw [real_spectral_decomposition hR.isHermitian]
  rw [unitary_conjugate_mul, Matrix.diagonal_mul_diagonal,
    unitary_conjugate_trace, Matrix.trace_diagonal]
  simp only [upperWeightedMean]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Spectral representation of the actual polynomial matrix, with coefficient two. -/
theorem upperFixedComparison_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    upperFixedComparison R = (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (upperFixedEigenvalue hR.isHermitian.eigenvalues) *
        star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let r := hR.isHermitian.eigenvalues
  have he : upperFixedComparison R = upperComparison R - upperSquareWeight R * R := by
    simp only [upperFixedComparison, upperComparison, upperSquareWeight, two_smul]
    noncomm_ring
  rw [he, upperComparison_spectral hR, upperSquareWeight_spectral hR]
  conv_lhs => rhs; rhs; rw [real_spectral_decomposition hR.isHermitian]
  rw [unitary_conjugate_mul, Matrix.diagonal_mul_diagonal, ← Matrix.sub_mul, ← Matrix.mul_sub,
    Matrix.diagonal_sub]
  congr 2
  apply congrArg Matrix.diagonal
  funext i
  simp only [Pi.sub_apply, upperAveragedEigenvalue, upperFixedEigenvalue]
  ring

/-- Positivity allows semidefinite, rather than positive-definite, matrices. -/
theorem upperFixedEigenvalue_nonneg {r : ι → ℝ} (hr : ∀ i, 0 < r i) (i : ι) :
    0 ≤ upperFixedEigenvalue r i := by
  obtain ⟨hp, hp1, _, _⟩ := upper_weight_properties hr
  have hm : upperWeight r i * r i ≤ upperWeightedMean r :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hp j).le (hr j).le) (Finset.mem_univ i)
  have he : r i * (1 - upperWeight r i) ^ 2 ≤ upperFixedEigenvalue r i := by
    unfold upperFixedEigenvalue
    nlinarith [mul_le_mul_of_nonneg_left hm (hp i).le]
  exact (mul_nonneg (hr i).le (sq_nonneg _)).trans he

theorem upperFixedComparison_posSemidef {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (upperFixedComparison R).PosSemidef := by
  rw [upperFixedComparison_spectral hR]
  have hd : (Matrix.diagonal (upperFixedEigenvalue hR.isHermitian.eigenvalues)).PosSemidef :=
    Matrix.PosSemidef.diagonal (upperFixedEigenvalue_nonneg hR.eigenvalues_pos)
  exact hd.mul_mul_conjTranspose_same (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)

/-- The trace loses exactly the square-weighted mean. -/
theorem upperFixedComparison_trace {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix.trace (upperFixedComparison R) = Matrix.trace R - Matrix.trace (R * upperSquareWeight R) := by
  rw [upperFixedComparison_spectral hR, unitary_conjugate_trace, Matrix.trace_diagonal,
    real_spectral_trace hR.isHermitian, upperSquareWeight_mean hR]
  obtain ⟨_, _, hp, _⟩ := upper_weight_properties hR.eigenvalues_pos
  simp only [upperFixedEigenvalue, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hp, one_mul, mul_left_comm _ 2]
  unfold upperWeightedMean
  have he : (∑ x, upperWeight hR.isHermitian.eigenvalues x * (2 * hR.isHermitian.eigenvalues x)) =
      2 * ∑ x, upperWeight hR.isHermitian.eigenvalues x * hR.isHermitian.eigenvalues x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

/-- The one-dimensional comparison vanishes, including arbitrary positive scales. -/
theorem upperFixedComparison_eq_zero_of_subsingleton [Subsingleton ι]
    {R : Matrix ι ι ℝ} (hR : R.PosDef) : upperFixedComparison R = 0 := by
  rw [upperFixedComparison_spectral hR]
  letI : Unique ι := ⟨⟨Classical.choice inferInstance⟩, fun _ => Subsingleton.elim _ _⟩
  have hz : upperFixedEigenvalue hR.isHermitian.eigenvalues = 0 := by
    funext i
    have hi : i = default := Subsingleton.elim _ _
    subst i
    simp only [upperFixedEigenvalue, upperWeight, upperWeightedMean, Finset.univ_unique,
      Finset.sum_singleton, Pi.zero_apply]
    field_simp [(hR.eigenvalues_pos default).ne']
    ring
  have hdz : Matrix.diagonal (0 : ι → ℝ) = (0 : Matrix ι ι ℝ) := by
    ext i j
    simp [Matrix.diagonal]
  rw [hz, hdz, mul_zero, zero_mul]

/-- Harmonic-mean supporting inequality on any finite collection. This is
Cauchy--Schwarz, the concavity calculation for `1/S_j` in the printed proof. -/
theorem resolvent_harmonic_tangent (s : Finset ι) {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 < r i) {h : ℝ} (hh : 0 ≤ h) :
    (∑ i ∈ s, r i ^ 2) ^ 2 ≤
      (∑ i ∈ s, r i ^ 2 / (1 + h * r i)) *
        ((∑ i ∈ s, r i ^ 2) + h * ∑ i ∈ s, r i ^ 3) := by
  have hd : ∀ i ∈ s, 0 < 1 + h * r i := fun i hi =>
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i hi).le)
  have hc : (∑ i ∈ s, r i ^ 2) ^ 2 ≤
      (∑ i ∈ s, r i ^ 2 / (1 + h * r i)) *
        (∑ i ∈ s, r i ^ 2 * (1 + h * r i)) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro i hi
      exact div_nonneg (sq_nonneg _) (hd i hi).le
    · intro i hi
      exact mul_nonneg (sq_nonneg _) (hd i hi).le
    · intro i hi
      have hd' : 1 + r i * h ≠ 0 := by simpa only [mul_comm] using (hd i hi).ne'
      field_simp [(hd i hi).ne', hd']
  convert! hc using 2
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Reciprocal supporting line; this is the final convex-reciprocal step in
 the concavity proof of the individual `B_h` eigenvalues. -/
theorem reciprocal_supporting_line {A B h : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) : 1 - 1 / (A + h * B) ≤ 1 - 1 / A + h * B / A ^ 2 := by
  have hd : 0 < A + h * B := by positivity
  have he : (1 - 1 / A + h * B / A ^ 2) - (1 - 1 / (A + h * B)) =
      (h * B) ^ 2 / (A ^ 2 * (A + h * B)) := by
    field_simp
    ring
  have hn : 0 ≤ (h * B) ^ 2 / (A ^ 2 * (A + h * B)) := by positivity
  linarith

/-- Algebraic form of the concavity tangent, with `s,t,S` denoting respectively
`S_j(0)`, the complementary cube sum, and `S_j(h)`. -/
theorem upper_eigenvalue_tangent_of_harmonic {r s t S h : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 ≤ t) (hS : 0 < S) (hh : 0 ≤ h)
    (hcauchy : s ^ 2 ≤ S * (s + h * t)) :
    h * r / (1 + h * r) + (r / (1 + h * r)) ^ 2 /
        (S + r ^ 2 / (1 + h * r)) ≤
      r ^ 2 / (s + r ^ 2) + h *
        (r + (r ^ 2 / (s + r ^ 2)) * ((t + r ^ 3) / (s + r ^ 2) - 2 * r)) := by
  have hd : 0 < 1 + h * r := by positivity
  have hT : 0 < s + r ^ 2 := by positivity
  have hsmall : 0 < 1 + h * r + r ^ 2 / S := by positivity
  have hlarge : 0 < (s + r ^ 2) / s + h * (r + r ^ 2 * t / s ^ 2) := by positivity
  have hinv : 1 / S ≤ (s + h * t) / s ^ 2 := by
    apply (div_le_div_iff₀ hS (sq_pos_of_pos hs)).2
    nlinarith
  have hden : 1 + h * r + r ^ 2 / S ≤
      (s + r ^ 2) / s + h * (r + r ^ 2 * t / s ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hinv (sq_nonneg r)
    have he : (s + r ^ 2) / s + h * (r + r ^ 2 * t / s ^ 2) =
        1 + h * r + r ^ 2 * ((s + h * t) / s ^ 2) := by field_simp; ring
    rw [he]
    rw [mul_one_div] at hm
    linarith
  have hb := reciprocal_supporting_line (div_pos hT hs)
    (show 0 ≤ r + r ^ 2 * t / s ^ 2 by positivity) hh
  have hrec := one_div_le_one_div_of_le hsmall hden
  have hid : h * r / (1 + h * r) + (r / (1 + h * r)) ^ 2 /
      (S + r ^ 2 / (1 + h * r)) = 1 - 1 / (1 + h * r + r ^ 2 / S) := by
    field_simp
    ring
  have htangent : 1 - 1 / ((s + r ^ 2) / s) +
      h * (r + r ^ 2 * t / s ^ 2) / ((s + r ^ 2) / s) ^ 2 =
      r ^ 2 / (s + r ^ 2) + h *
        (r + (r ^ 2 / (s + r ^ 2)) * ((t + r ^ 3) / (s + r ^ 2) - 2 * r)) := by
    field_simp
    ring
  rw [hid]
  rw [← htangent]
  linarith

/-- The concavity tangent for every individual eigenvalue, including dimension one. -/
theorem upper_fixed_eigenvalue_bound {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {h : ℝ} (hh : 0 ≤ h) (i : ι) :
    h * (r i / (1+h*r i)) + (r i / (1+h*r i))^2 /
        (∑ j,r j^2/(1+h*r j)) ≤ upperWeight r i + h*upperFixedEigenvalue r i := by
  rcases subsingleton_or_nontrivial ι with hsub | hnon
  · letI := hsub
    letI : Unique ι := ⟨⟨i⟩, fun _ => Subsingleton.elim _ _⟩
    have hd : 0 < 1+h*r i := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr i).le)
    simp only [Finset.univ_unique, Finset.sum_singleton, upperWeight,
      upperFixedEigenvalue, upperWeightedMean]
    have hi : (default : ι) = i := Subsingleton.elim _ _
    rw [hi]
    apply le_of_eq
    field_simp [(hr i).ne', hd.ne']
    ring
  · letI := hnon
    let e := Finset.univ.erase i
    let s : ℝ := ∑ j ∈ e, r j^2
    let t : ℝ := ∑ j ∈ e, r j^3
    let S : ℝ := ∑ j ∈ e,r j^2/(1+h*r j)
    have he : e.Nonempty := by
      obtain ⟨j,hji⟩ := exists_ne i
      exact ⟨j,Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩⟩
    have hs : 0 < s := Finset.sum_pos (fun j _ => sq_pos_of_pos (hr j)) he
    have ht : 0 ≤ t := Finset.sum_nonneg (fun j _ => pow_nonneg (hr j).le _)
    have hd : ∀ j,0 < 1+h*r j := fun j => add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hr j).le)
    have hS : 0 < S := Finset.sum_pos (fun j _ =>
      div_pos (sq_pos_of_pos (hr j)) (hd j)) he
    have hc := resolvent_harmonic_tangent e (fun j _ => hr j) hh
    have h2 : (∑ j,r j^2) = s+r i^2 := by
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    have h3 : (∑ j,r j^3) = t+r i^3 := by
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    have hD : (∑ j,r j^2/(1+h*r j)) = S+r i^2/(1+h*r i) := by
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    have ha : upperWeightedMean r = (t+r i^3)/(s+r i^2) := by
      unfold upperWeightedMean upperWeight
      simp_rw [div_mul_eq_mul_div, ← pow_succ]
      rw [← Finset.sum_div, h2, h3]
    have hb := upper_eigenvalue_tangent_of_harmonic (hr i) hs ht hS hh hc
    rw [hD]
    simpa only [upperFixedEigenvalue, upperWeight, h2, ha, mul_div_assoc] using hb

/-- Supplementary `eq:app-up-fixed-comparison`, tested on an arbitrary vector. -/
theorem upper_fixed_quadratic_comparison {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : ι → ℝ) {h : ℝ} (hh : 0 < h) :
    x ⬝ᵥ (upperTailMatrix R h *ᵥ x) ≤
      x ⬝ᵥ (upperSquareWeight R *ᵥ x) + h*(x ⬝ᵥ (upperFixedComparison R *ᵥ x)) := by
  let r := hR.isHermitian.eigenvalues
  let y := star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x
  have hr : ∀ i,0 < r i := hR.eigenvalues_pos
  have hd : 0 < ∑ j,r j^2/(1+h*r j) :=
    Finset.sum_pos (fun j _ => div_pos (sq_pos_of_pos (hr j)) (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh.le (hr j).le))) Finset.univ_nonempty
  rw [upperTailMatrix_eq_smul_criterion hR hh, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, upperCriterion_spectral hR hh.le,
    quadratic_conjugate_diagonal, upperSquareWeight_spectral hR,
    quadratic_conjugate_diagonal, upperFixedComparison_spectral hR,
    quadratic_conjugate_diagonal]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rhs; rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hb := mul_le_mul_of_nonneg_left (upper_fixed_eigenvalue_bound hr hh.le i) (sq_nonneg (y i))
  convert! hb using 1
  · dsimp [y,r]
    have hdi : 0 < 1+h*hR.isHermitian.eigenvalues i := by
      have hi := hR.eigenvalues_pos i
      positivity
    field_simp [hh.ne',hd.ne',hdi.ne']
  · dsimp [y,r]
    ring

/-- The exact root comparison used in the upper mean argument. -/
theorem upperShift_fixed_comparison {R : Matrix ι ι ℝ} (hR : R.PosDef) (x : ι → ℝ) :
    upperShift R hR x ≤ x ⬝ᵥ (upperSquareWeight R *ᵥ x) +
      upperShift R hR x * (x ⬝ᵥ (upperFixedComparison R *ᵥ x)) := by
  by_cases hx : x = 0
  · subst x
    simp [upperShift_zero]
  · have hh := upper_fixed_quadratic_comparison hR x (upperShift_pos hR hx)
    rw [upperShift_tail_equation hR x] at hh
    exact hh

/-- The square weight is strictly positive even when the new comparison is zero. -/
theorem upperSquareWeight_posDef {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (upperSquareWeight R).PosDef := by
  rw [upperSquareWeight_spectral hR]
  exact unitary_conjugate_posDef _ _
    (Matrix.PosDef.diagonal (upper_weight_properties hR.eigenvalues_pos).1)

theorem upperTailMatrix_zero {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    upperTailMatrix R 0 = upperSquareWeight R := by
  have hres : upperResolvent R 0 = R := by
    unfold upperResolvent
    simp only [zero_smul,add_zero]
    exact Matrix.nonsing_inv_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit)
  simp only [upperTailMatrix,upperTailDenominator,hres,zero_smul,zero_add,
    upperSquareWeight,pow_two]

/-- The exact event equivalence also holds at the endpoint `h=0`. -/
theorem upperShift_tail_event_nonneg {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : ι → ℝ) {h : ℝ} (hh : 0 ≤ h) :
    h < upperShift R hR x ↔ h < x ⬝ᵥ (upperTailMatrix R h *ᵥ x) := by
  rcases hh.eq_or_lt with rfl | hh
  · rw [upperShift_pos_iff hR x,upperTailMatrix_zero hR]
    constructor
    · intro hx
      simpa only [star_trivial] using (upperSquareWeight_posDef hR).dotProduct_mulVec_pos hx
    · intro hx hz
      subst x
      simpa using hx
  · exact upperShift_tail_event hR x hh

/-- The exact tail matrix is positive at every nonnegative shift. -/
theorem upperTailMatrix_posDef {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 ≤ h) : (upperTailMatrix R h).PosDef := by
  rcases hh.eq_or_lt with rfl | hh
  · rw [upperTailMatrix_zero hR]
    exact upperSquareWeight_posDef hR
  · rw [upperTailMatrix_spectral hR hh]
    apply unitary_conjugate_posDef
    apply Matrix.PosDef.diagonal
    intro i
    have hi := hR.eigenvalues_pos i
    have hp := (upperTailWeight_properties hR.eigenvalues_pos hh.le).1 i
    unfold upperTailEigenvalue
    positivity

/-- The fixed quadratic comparison includes the endpoint shift. -/
theorem upper_fixed_quadratic_comparison_nonneg {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : ι → ℝ) {h : ℝ} (hh : 0 ≤ h) :
    x ⬝ᵥ (upperTailMatrix R h *ᵥ x) ≤
      x ⬝ᵥ (upperSquareWeight R *ᵥ x)+h*(x ⬝ᵥ (upperFixedComparison R *ᵥ x)) := by
  rcases hh.eq_or_lt with rfl | hh
  · simp only [upperTailMatrix_zero hR,zero_mul,add_zero,le_rfl]
  · exact upper_fixed_quadratic_comparison hR x hh

/-- Matrix form of supplementary `B_h ≼ P+h C`, including `h=0`. -/
theorem upper_fixed_matrix_comparison {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 ≤ h) :
    (upperSquareWeight R+h • upperFixedComparison R-upperTailMatrix R h).PosSemidef := by
  have hP := (upperSquareWeight_posDef hR).isHermitian
  have hC := (upperFixedComparison_posSemidef hR).isHermitian
  have hB := (upperTailMatrix_posDef hR hh).isHermitian
  have hCs : (h • upperFixedComparison R).IsHermitian := by
    change (h • upperFixedComparison R).conjTranspose = h • upperFixedComparison R
    rw [Matrix.conjTranspose_smul,hC]
    rfl
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨(hP.add hCs).sub hB,?_⟩
  intro x
  have hq := upper_fixed_quadratic_comparison_nonneg hR x hh
  simpa only [star_trivial,Matrix.sub_mulVec,Matrix.add_mulVec,Matrix.smul_mulVec,
    dotProduct_sub,dotProduct_add,dotProduct_smul,smul_eq_mul,sub_nonneg] using hq

end
end SingularValueBounds.KL
