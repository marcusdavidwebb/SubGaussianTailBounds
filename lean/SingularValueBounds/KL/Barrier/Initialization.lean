import SingularValueBounds.KL.Barrier.Process
import SingularValueBounds.Main.SpectralBounds

/-! # Scalar initialization and final strict spectral gaps -/
open Set MeasureTheory
open scoped BigOperators Matrix
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def scalarResolvent (u : ℝ) (hu : 0 < u) : PositiveResolvent ι :=
  ⟨Matrix.diagonal (fun _ => u⁻¹), Matrix.PosDef.diagonal (fun _ => inv_pos.mpr hu)⟩

lemma scalarResolvent_inv (u : ℝ) (hu : 0 < u) :
    (scalarResolvent (ι := ι) u hu).1⁻¹ = u • (1 : Matrix ι ι ℝ) := by
  rw [scalarResolvent, positive_diagonal_inverse _ (fun _ => inv_pos.mpr hu)]
  simp only [inv_inv]
  ext i j
  by_cases hij : i=j <;> simp [Matrix.diagonal, hij]

lemma scalarResolvent_trace (u : ℝ) (hu : 0 < u) :
    Matrix.trace (scalarResolvent (ι := ι) u hu).1 = Fintype.card ι / u := by
  simp [scalarResolvent, Matrix.trace_diagonal, div_eq_mul_inv]

lemma scalarResolvent_frobenius (u : ℝ) (hu : 0 < u) :
    frobenius (scalarResolvent (ι := ι) u hu).1 = Real.sqrt (Fintype.card ι) / u := by
  rw [frobenius_eq_sqrt_trace_square (scalarResolvent u hu).2.isHermitian]
  change Real.sqrt (Matrix.trace ((Matrix.diagonal (fun _ : ι => u⁻¹))^2)) = _
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [Pi.pow_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hu)]
  rfl

/-- Initial scalar distance for the constant cap. -/
def initialDistance (n : ℕ) (K w b : ℝ) : ℝ := (K^2*n+w*Real.sqrt n)/b

lemma initialDistance_pos {n : ℕ} (hn : 0 < n) (K : ℝ) {w b : ℝ}
    (hw : 0 < w) (hb : 0 < b) : 0 < initialDistance n K w b := by
  unfold initialDistance
  exact div_pos (add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (mul_pos hw (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)))) hb

lemma scalar_initial_cap (K : ℝ) {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    regularityCost K w
      (scalarResolvent (ι := ι) (initialDistance (Fintype.card ι) K w b)
        (initialDistance_pos Fintype.card_pos K hw hb)).1 = b := by
  rw [regularityCost, scalarResolvent_trace, scalarResolvent_frobenius]
  have hp := initialDistance_pos (n := Fintype.card ι) Fintype.card_pos K hw hb
  unfold initialDistance at hp ⊢
  field_simp
  <;> nlinarith [mul_pos hb hp]

lemma scalar_initial_trace_lt (K : ℝ) {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    K^2 * Matrix.trace
      (scalarResolvent (ι := ι) (initialDistance (Fintype.card ι) K w b)
        (initialDistance_pos Fintype.card_pos K hw hb)).1 < b := by
  have he := scalar_initial_cap (ι := ι) K hw hb
  have hf := frobenius_pos
    (scalarResolvent (ι := ι) (initialDistance (Fintype.card ι) K w b)
      (initialDistance_pos Fintype.card_pos K hw hb)).2
  dsimp [regularityCost] at he
  nlinarith [mul_pos hw hf]

lemma scalar_initial_potential (K : ℝ) {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    traceBudgetPrimitive (K^2) w b
      (Matrix.trace (scalarResolvent (ι := ι) (initialDistance (Fintype.card ι) K w b)
        (initialDistance_pos Fintype.card_pos K hw hb)).1) =
      w*Real.sqrt (Fintype.card ι)/b := by
  rw [scalarResolvent_trace]
  have hs : Real.sqrt (Fintype.card ι) ^ 2 = Fintype.card ι := Real.sq_sqrt (Nat.cast_nonneg _)
  have hspos : 0 < Real.sqrt (Fintype.card ι) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  have hnum : K^2*(Fintype.card ι)+w*Real.sqrt (Fintype.card ι) ≠ 0 := by positivity
  unfold traceBudgetPrimitive initialDistance
  field_simp [hb.ne', hnum]
  nlinarith only [congrArg (fun z : ℝ => w*z) hs]

/-- Complete pathwise constant-profile correction budget. -/
theorem constant_process_budget (K : ℝ) {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (upper : Bool) (x : ℕ → ι → ℝ) (m : ℕ) :
    CorrectionBudget (Fintype.card ι) w b
      ((constantCorrectionRule K hw.le hb).process upper
        (scalarResolvent (initialDistance (Fintype.card ι) K w b)
          (initialDistance_pos Fintype.card_pos K hw hb)) x m).outward := by
  constructor
  · exact CorrectionRule.process_outward_nonneg _ _ _ _ _
  · have h := constant_process_outward_le K hw hb upper
      (scalarResolvent (initialDistance (Fintype.card ι) K w b)
        (initialDistance_pos Fintype.card_pos K hw hb)) x m (scalar_initial_trace_lt K hw hb)
    rwa [scalar_initial_potential K hw hb] at h

/-- A generic deterministic cost budget yields the final strict upper gap. -/
theorem process_upper_gap (c : CorrectionRule ι) (u : ℝ) (hu : 0 < u)
    (x : ℕ → ι → ℝ) (m : ℕ) :
    (((c.process true (scalarResolvent u hu) x m).shifts+u+
      (c.process true (scalarResolvent u hu) x m).outward) • (1 : Matrix ι ι ℝ) -
      (c.process true (scalarResolvent u hu) x m).gram).PosDef := by
  have hp := (c.process true (scalarResolvent (ι := ι) u hu) x m).positive.inv
  rw [c.process_inverse] at hp
  simp only [Bool.true_eq, if_true, scalarResolvent_inv] at hp
  convert! hp using 1 <;> simp only [add_smul] <;> abel

/-- A generic deterministic cost budget yields the final strict lower gap. -/
theorem process_lower_gap (c : CorrectionRule ι) (u : ℝ) (hu : 0 < u)
    (x : ℕ → ι → ℝ) (m : ℕ) :
    ((c.process false (scalarResolvent u hu) x m).gram-
      ((c.process false (scalarResolvent u hu) x m).shifts-u-
        (c.process false (scalarResolvent u hu) x m).outward) • (1 : Matrix ι ι ℝ)).PosDef := by
  have hp := (c.process false (scalarResolvent (ι := ι) u hu) x m).positive.inv
  rw [c.process_inverse] at hp
  simp only [Bool.false_eq_true, if_false, scalarResolvent_inv] at hp
  convert! hp using 1 <;> simp only [add_smul, sub_smul] <;> abel

end
end SingularValueBounds.KL
