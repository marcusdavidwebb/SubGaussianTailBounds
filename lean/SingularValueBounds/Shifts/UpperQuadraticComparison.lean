import SingularValueBounds.Core.Matrix
import SingularValueBounds.QuadraticForms.Estimates

/-!
# The deterministic quadratic upper bound (Lemma 3.2)

The fixed comparison matrix is defined by the polynomial formula in the paper.
Its spectral representation averages each eigenvalue towards the mean weighted
by the squares of the eigenvalues.
-/

open scoped Matrix BigOperators

namespace SingularValueBounds

noncomputable section

variable {ι : Type*} [Fintype ι]

def upperWeight (r : ι → ℝ) (i : ι) : ℝ := r i ^ 2 / ∑ j, r j ^ 2

def upperWeightedMean (r : ι → ℝ) : ℝ := ∑ i, upperWeight r i * r i

def upperAveragedEigenvalue (r : ι → ℝ) (i : ι) : ℝ :=
  (1 - upperWeight r i) * r i + upperWeight r i * upperWeightedMean r

theorem upper_weight_properties [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    (∀ i, 0 < upperWeight r i) ∧ (∀ i, upperWeight r i ≤ 1) ∧
      (∑ i, upperWeight r i) = 1 ∧ 0 < upperWeightedMean r := by
  have hS : 0 < ∑ i, r i ^ 2 :=
    Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) Finset.univ_nonempty
  have hw : ∀ i, 0 < upperWeight r i :=
    fun i => div_pos (sq_pos_of_pos (hr i)) hS
  refine ⟨hw, ?_, ?_, ?_⟩
  · intro i
    exact (div_le_one hS).2
      (Finset.single_le_sum (fun j _ => sq_nonneg (r j)) (Finset.mem_univ i))
  · simp only [upperWeight, ← Finset.sum_div]
    exact div_self hS.ne'
  · exact Finset.sum_pos (fun i _ => mul_pos (hw i) (hr i)) Finset.univ_nonempty

theorem upper_averaged_positive [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    ∀ i, 0 < upperAveragedEigenvalue r i := by
  obtain ⟨hw, hw1, _, ha⟩ := upper_weight_properties hr
  intro i
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr (hw1 i)) (hr i).le)
    (mul_pos (hw i) ha)

theorem upper_averaged_sum [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    (∑ i, upperAveragedEigenvalue r i) = ∑ i, r i := by
  have hw := (upper_weight_properties hr).2.2.1
  simp only [upperAveragedEigenvalue, sub_mul, one_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul, upperWeightedMean]
  ring

theorem upper_averaged_square_sum [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    (∑ i, upperAveragedEigenvalue r i ^ 2) ≤ ∑ i, r i ^ 2 := by
  obtain ⟨hw, hw1, hsum, ha⟩ := upper_weight_properties hr
  have hvar : upperWeightedMean r ^ 2 ≤ ∑ i, upperWeight r i * r i ^ 2 := by
    have hnonneg : 0 ≤ ∑ i, upperWeight r i * (r i - upperWeightedMean r) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))
    have hid : (∑ i, upperWeight r i * (r i - upperWeightedMean r) ^ 2) =
        (∑ i, upperWeight r i * r i ^ 2) - upperWeightedMean r ^ 2 := by
      calc
        _ = (∑ i, upperWeight r i * r i ^ 2) -
            2 * upperWeightedMean r * (∑ i, upperWeight r i * r i) +
            upperWeightedMean r ^ 2 * (∑ i, upperWeight r i) := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hsum]; unfold upperWeightedMean; ring
    rw [hid] at hnonneg
    linarith
  calc
    (∑ i, upperAveragedEigenvalue r i ^ 2) ≤
        ∑ i, ((1 - upperWeight r i) * r i ^ 2 + upperWeight r i * upperWeightedMean r ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [upperAveragedEigenvalue]
      nlinarith [mul_nonneg (mul_nonneg (hw i).le (sub_nonneg.mpr (hw1 i)))
        (sq_nonneg (r i - upperWeightedMean r))]
    _ = (∑ i, r i ^ 2) - (∑ i, upperWeight r i * r i ^ 2) + upperWeightedMean r ^ 2 := by
      simp only [sub_mul, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i, r i ^ 2 := by linarith

private theorem inv_one_add_tangent {r a h : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hh : 0 ≤ h) :
    (1 + 2 * h * a - h * r) / (1 + h * a) ^ 2 ≤ 1 / (1 + h * r) := by
  have hdr : 0 < 1 + h * r := by positivity
  have hda : 0 < (1 + h * a) ^ 2 := by positivity
  apply (div_le_div_iff₀ hda hdr).2
  nlinarith [sq_nonneg (h * (r - a))]

theorem upper_resolvent_jensen [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {h : ℝ} (hh : 0 ≤ h) :
    (∑ i, r i ^ 2) / (1 + h * upperWeightedMean r) ≤
      ∑ i, r i ^ 2 / (1 + h * r i) := by
  obtain ⟨hw, hw1, hsum, ha⟩ := upper_weight_properties hr
  have hS : 0 < ∑ i, r i ^ 2 :=
    Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) Finset.univ_nonempty
  have hb : 1 / (1 + h * upperWeightedMean r) ≤
      ∑ i, upperWeight r i / (1 + h * r i) := by
    have hsumineq := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (inv_one_add_tangent (hr i).le ha.le hh) (hw i).le)
    have hid : (∑ i, upperWeight r i *
        ((1 + 2 * h * upperWeightedMean r - h * r i) /
          (1 + h * upperWeightedMean r) ^ 2)) =
        1 / (1 + h * upperWeightedMean r) := by
      calc
        _ = ((1 + 2 * h * upperWeightedMean r) * (∑ i, upperWeight r i) -
            h * (∑ i, upperWeight r i * r i)) / (1 + h * upperWeightedMean r) ^ 2 := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          rw [hsum]
          change ((1 + 2 * h * upperWeightedMean r) * 1 - h * upperWeightedMean r) /
            (1 + h * upperWeightedMean r) ^ 2 = _
          field_simp
          ring
    rw [hid] at hsumineq
    simpa only [mul_one_div] using hsumineq
  have hmul := mul_le_mul_of_nonneg_left hb hS.le
  convert hmul using 1
  · ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [upperWeight]
    have hd : 0 < 1 + h * r i := by nlinarith [mul_nonneg hh (hr i).le]
    field_simp [hS.ne', hd.ne']
    ring

private theorem upper_scalar_comparison {x b w : ℝ}
    (hx : 0 ≤ x) (hb : 0 ≤ b) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    x / (1 + x) + w * (1 + b) / (1 + x) ^ 2 ≤ (1 - w) * x + w * (1 + b) := by
  have hd : 0 < 1 + x := by positivity
  have hfirst : x / (1 + x) ≤ x := by
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg x]
  have hsecond : x / (1 + x) + (1 + b) / (1 + x) ^ 2 ≤ 1 + b := by
    have heq : x / (1 + x) + (1 + b) / (1 + x) ^ 2 =
        (x * (1 + x) + (1 + b)) / (1 + x) ^ 2 := by
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    nlinarith [mul_nonneg hb hx, mul_nonneg hb (sq_nonneg x)]
  have h1 := mul_le_mul_of_nonneg_left hfirst (sub_nonneg.mpr hw1)
  have h2 := mul_le_mul_of_nonneg_left hsecond hw
  have hs := add_le_add h1 h2
  convert hs using 1
  ring

theorem upper_resolvent_eigenvalue_bound [Nonempty ι] {r : ι → ℝ}
    (hr : ∀ i, 0 < r i) {h : ℝ} (hh : 0 ≤ h) (i : ι) :
    h * (r i / (1 + h * r i)) + (r i / (1 + h * r i)) ^ 2 /
        (∑ j, r j ^ 2 / (1 + h * r j)) ≤
      upperWeight r i + h * upperAveragedEigenvalue r i := by
  obtain ⟨hw, hw1, hsum, ha⟩ := upper_weight_properties hr
  have hS : 0 < ∑ i, r i ^ 2 :=
    Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) Finset.univ_nonempty
  have hda : 0 < 1 + h * upperWeightedMean r := by positivity
  calc
    _ ≤ h * (r i / (1 + h * r i)) + (r i / (1 + h * r i)) ^ 2 /
        ((∑ j, r j ^ 2) / (1 + h * upperWeightedMean r)) :=
      add_le_add_left (div_le_div_of_nonneg_left (sq_nonneg _)
        (div_pos hS hda) (upper_resolvent_jensen hr hh)) _
    _ = (h * r i) / (1 + h * r i) +
        upperWeight r i * (1 + h * upperWeightedMean r) / (1 + h * r i) ^ 2 := by
      dsimp [upperWeight]
      field_simp
      ring
    _ ≤ (1 - upperWeight r i) * (h * r i) +
        upperWeight r i * (1 + h * upperWeightedMean r) :=
      upper_scalar_comparison (mul_nonneg hh (hr i).le) (mul_nonneg hh ha.le) (hw i).le (hw1 i)
    _ = _ := by unfold upperAveragedEigenvalue; ring

variable [DecidableEq ι]

/-- The resolvent after moving the upper barrier by `h`. -/
def upperResolvent (R : Matrix ι ι ℝ) (h : ℝ) : Matrix ι ι ℝ :=
  (R⁻¹ + h • (1 : Matrix ι ι ℝ))⁻¹

/-- The matrix whose quadratic form equals one at the exact upper shift. -/
def upperCriterion (R : Matrix ι ι ℝ) (h : ℝ) : Matrix ι ι ℝ :=
  upperResolvent R h + (Matrix.trace (R - upperResolvent R h))⁻¹ • upperResolvent R h ^ 2

/-- The fixed comparison matrix `R + P (tr(RP) I - R)`, where `P = R² / tr(R²)`. -/
def upperComparison (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  let P := (Matrix.trace (R ^ 2))⁻¹ • R ^ 2
  R + P * (Matrix.trace (R * P) • (1 : Matrix ι ι ℝ) - R)

theorem unitary_conjugate_scalar {h : ℝ} (U : Matrix.unitaryGroup ι ℝ) :
    (U : Matrix ι ι ℝ) * (h • (1 : Matrix ι ι ℝ)) * star (U : Matrix ι ι ℝ) =
      h • (1 : Matrix ι ι ℝ) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, U.2.2]

/-- The polynomial comparison matrix averages the eigenvalues using their
squared eigenvalue weights. -/
theorem upperComparison_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    upperComparison R = (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (upperAveragedEigenvalue hR.isHermitian.eigenvalues) *
        star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let r := hR.isHermitian.eigenvalues
  let P := (Matrix.trace (R ^ 2))⁻¹ • R ^ 2
  have hRrep : R = (U : Matrix ι ι ℝ) * Matrix.diagonal r * star (U : Matrix ι ι ℝ) :=
    real_spectral_decomposition hR.isHermitian
  have hPrep : P = (U : Matrix ι ι ℝ) * Matrix.diagonal (upperWeight r) *
      star (U : Matrix ι ι ℝ) := by
    dsimp [P]
    rw [real_spectral_trace_square hR.isHermitian, real_spectral_square hR.isHermitian]
    change (∑ i, r i ^ 2)⁻¹ •
      ((U : Matrix ι ι ℝ) * Matrix.diagonal (fun i => r i ^ 2) * star (U : Matrix ι ι ℝ)) = _
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    simp [Matrix.diagonal, upperWeight, div_eq_mul_inv, mul_comm]
  have hbar : Matrix.trace (R * P) = upperWeightedMean r := by
    rw [hRrep, hPrep, unitary_conjugate_mul, Matrix.diagonal_mul_diagonal,
      unitary_conjugate_trace, Matrix.trace_diagonal]
    simp only [upperWeightedMean]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change R + P * (Matrix.trace (R * P) • (1 : Matrix ι ι ℝ) - R) =
    (U : Matrix ι ι ℝ) * Matrix.diagonal (upperAveragedEigenvalue r) * star (U : Matrix ι ι ℝ)
  rw [hbar, hRrep, hPrep, ← unitary_conjugate_scalar (h := upperWeightedMean r) U]
  have hsub : (U : Matrix ι ι ℝ) * (upperWeightedMean r • (1 : Matrix ι ι ℝ)) *
        star (U : Matrix ι ι ℝ) -
      (U : Matrix ι ι ℝ) * Matrix.diagonal r * star (U : Matrix ι ι ℝ) =
      (U : Matrix ι ι ℝ) * (upperWeightedMean r • (1 : Matrix ι ι ℝ) - Matrix.diagonal r) *
        star (U : Matrix ι ι ℝ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hsub, unitary_conjugate_mul, ← Matrix.add_mul, ← Matrix.mul_add]
  change (U : Matrix ι ι ℝ) * _ * star (U : Matrix ι ι ℝ) =
    (U : Matrix ι ι ℝ) * Matrix.diagonal (upperAveragedEigenvalue r) * star (U : Matrix ι ι ℝ)
  congr 2
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal, upperAveragedEigenvalue]
    ring
  · simp [Matrix.diagonal, hij]

theorem upperComparison_posDef [Nonempty ι] {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (upperComparison R).PosDef := by
  rw [upperComparison_spectral hR]
  exact unitary_conjugate_posDef _ _ (Matrix.PosDef.diagonal
    (upper_averaged_positive hR.eigenvalues_pos))

theorem upperComparison_trace [Nonempty ι] {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix.trace (upperComparison R) = Matrix.trace R := by
  rw [upperComparison_spectral hR]
  rw [unitary_conjugate_trace, Matrix.trace_diagonal, upper_averaged_sum hR.eigenvalues_pos,
    real_spectral_trace hR.isHermitian]

theorem upperComparison_trace_square [Nonempty ι] {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix.trace (upperComparison R ^ 2) ≤ Matrix.trace (R ^ 2) := by
  rw [upperComparison_spectral hR]
  rw [pow_two, unitary_conjugate_mul, Matrix.diagonal_mul_diagonal,
    unitary_conjugate_trace, Matrix.trace_diagonal,
    real_spectral_trace_square hR.isHermitian]
  simpa only [pow_two] using upper_averaged_square_sum hR.eigenvalues_pos

theorem upperResolvent_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 ≤ h) :
    upperResolvent R h = (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => hR.isHermitian.eigenvalues i /
        (1 + h * hR.isHermitian.eigenvalues i)) *
      star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let r := hR.isHermitian.eigenvalues
  have hr : ∀ i, 0 < r i := hR.eigenvalues_pos
  have hdiag : Matrix.diagonal (fun i => (r i)⁻¹ + h) =
      Matrix.diagonal (fun i => (r i)⁻¹) + h • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have hform : R⁻¹ + h • (1 : Matrix ι ι ℝ) = (U : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => (r i)⁻¹ + h) * star (U : Matrix ι ι ℝ) := by
    rw [real_spectral_decomposition hR.isHermitian, unitary_conjugate_inverse,
      positive_diagonal_inverse _ hr, hdiag, Matrix.mul_add, Matrix.add_mul,
      unitary_conjugate_scalar]
  unfold upperResolvent
  rw [hform, unitary_conjugate_inverse,
    positive_diagonal_inverse _ (fun i => add_pos_of_pos_of_nonneg (inv_pos.mpr (hr i)) hh)]
  congr 2
  apply congrArg Matrix.diagonal
  funext i
  have hd : 0 < 1 + h * r i := by nlinarith [mul_nonneg hh (hr i).le]
  field_simp [ne_of_gt (hr i), hd.ne']
  rfl

theorem upperResolvent_trace_drop {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 ≤ h) :
    Matrix.trace (R - upperResolvent R h) =
      h * ∑ i, hR.isHermitian.eigenvalues i ^ 2 /
        (1 + h * hR.isHermitian.eigenvalues i) := by
  rw [Matrix.trace_sub, upperResolvent_spectral hR hh,
    real_spectral_trace hR.isHermitian, unitary_conjugate_trace, Matrix.trace_diagonal,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hd : 0 < 1 + h * hR.isHermitian.eigenvalues i :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh (hR.eigenvalues_pos i).le)
  field_simp [hd.ne']
  ring

theorem upperCriterion_spectral {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {h : ℝ} (hh : 0 ≤ h) :
    upperCriterion R h = (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i =>
        hR.isHermitian.eigenvalues i / (1 + h * hR.isHermitian.eigenvalues i) +
        (hR.isHermitian.eigenvalues i / (1 + h * hR.isHermitian.eigenvalues i)) ^ 2 /
          (h * ∑ j, hR.isHermitian.eigenvalues j ^ 2 /
            (1 + h * hR.isHermitian.eigenvalues j))) *
      star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let r := hR.isHermitian.eigenvalues
  let d := h * ∑ j, r j ^ 2 / (1 + h * r j)
  let s := fun i => r i / (1 + h * r i)
  have hd : Matrix.diagonal (fun i => s i + s i ^ 2 / d) =
      Matrix.diagonal s + d⁻¹ • (Matrix.diagonal s ^ 2) := by
    rw [pow_two, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij, div_eq_mul_inv, pow_two, mul_comm]
  unfold upperCriterion
  rw [upperResolvent_trace_drop hR hh, upperResolvent_spectral hR hh]
  change (U : Matrix ι ι ℝ) * Matrix.diagonal s * star (U : Matrix ι ι ℝ) +
    d⁻¹ • ((U : Matrix ι ι ℝ) * Matrix.diagonal s * star (U : Matrix ι ι ℝ)) ^ 2 =
    (U : Matrix ι ι ℝ) * Matrix.diagonal (fun i => s i + s i ^ 2 / d) * star (U : Matrix ι ι ℝ)
  rw [hd, Matrix.mul_add, Matrix.add_mul, pow_two, unitary_conjugate_mul]
  simp only [pow_two, Matrix.mul_smul, Matrix.smul_mul]

/-- The matrix inequality in the proof of Lemma 3.2, tested against any vector.
It holds for every positive shift, independently of the sampled row. -/
theorem upper_quadratic_comparison [Nonempty ι] {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (x : ι → ℝ) {h : ℝ} (hh : 0 < h) :
    h * (x ⬝ᵥ (upperCriterion R h *ᵥ x)) ≤
      (x ⬝ᵥ ((R ^ 2) *ᵥ x)) / Matrix.trace (R ^ 2) +
        h * (x ⬝ᵥ (upperComparison R *ᵥ x)) := by
  let r := hR.isHermitian.eigenvalues
  let y := star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x
  have hr : ∀ i, 0 < r i := hR.eigenvalues_pos
  have hS : 0 < ∑ i, r i ^ 2 :=
    Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) Finset.univ_nonempty
  have hd : 0 < ∑ i, r i ^ 2 / (1 + h * r i) :=
    Finset.sum_pos (fun i _ => div_pos (sq_pos_of_pos (hr i))
      (by nlinarith [mul_pos hh (hr i)])) Finset.univ_nonempty
  rw [upperCriterion_spectral hR hh.le, quadratic_conjugate_diagonal,
    real_spectral_square hR.isHermitian, quadratic_conjugate_diagonal,
    unitary_conjugate_trace, Matrix.trace_diagonal]
  rw [upperComparison_spectral hR]
  rw [quadratic_conjugate_diagonal]
  simp only [Finset.mul_sum, Finset.sum_div]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hb := mul_le_mul_of_nonneg_left (upper_resolvent_eigenvalue_bound hr hh.le i)
    (sq_nonneg (y i))
  convert hb using 1
  · dsimp [y, r] at *
    rw [← Finset.mul_sum]
    have hdi : 0 < 1 + h * hR.isHermitian.eigenvalues i :=
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hh.le (hR.eigenvalues_pos i).le)
    field_simp [hh.ne', hd.ne', hdi.ne']
    ring
  · dsimp [y, r, upperWeight]
    ring

/-- Apply the deterministic comparison at a positive solution of the exact
upper-barrier equation. Existence of that solution is established separately. -/
theorem upper_shift_quadratic_of_equation [Nonempty ι] {R : Matrix ι ι ℝ}
    (hR : R.PosDef) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (heq : x ⬝ᵥ (upperCriterion R δ *ᵥ x) = 1) :
    δ ≤ (x ⬝ᵥ ((R ^ 2) *ᵥ x)) / Matrix.trace (R ^ 2) +
      δ * (x ⬝ᵥ (upperComparison R *ᵥ x)) := by
  simpa only [heq, mul_one] using upper_quadratic_comparison hR x hδ

end
end SingularValueBounds
