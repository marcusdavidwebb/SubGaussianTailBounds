import SingularValueBounds.KL.Barrier.Corrections

/-! # Pathwise trace budgets
A primitive of the reciprocal-square kernel accounts for each correction.
The finite telescope is the disjoint-trace-interval argument in a form that
also applies to future nonconstant profiles. -/
open Set Filter MeasureTheory
open scoped BigOperators Matrix Topology
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def traceBudgetPrimitive (a w b τ : ℝ) : ℝ := w^2 * τ / (b * (b-a*τ))

lemma hasDerivAt_traceBudgetPrimitive {a w b τ : ℝ} (hb : b ≠ 0) (hg : b-a*τ ≠ 0) :
    HasDerivAt (traceBudgetPrimitive a w b) (w^2/(b-a*τ)^2) τ := by
  have hd := ((hasDerivAt_id τ).const_mul (w^2)).div
    ((hasDerivAt_const τ b).mul ((hasDerivAt_const τ b).sub
      ((hasDerivAt_id τ).const_mul a))) (mul_ne_zero hb hg)
  convert! hd using 1 <;> (try ext x) <;>
    simp only [traceBudgetPrimitive, Pi.div_apply, Pi.mul_apply, Pi.sub_apply, id_eq] <;>
    field_simp <;> ring

lemma traceBudgetPrimitive_nonneg {a w b τ : ℝ} (hb : 0 < b)
    (hτ : 0 ≤ τ) (hg : 0 < b-a*τ) : 0 ≤ traceBudgetPrimitive a w b τ :=
  div_nonneg (mul_nonneg (sq_nonneg w) hτ) (mul_pos hb hg).le

/-- One correction is paid for by the drop of a scalar trace potential. -/
theorem constantCorrection_budget {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (K : ℝ) {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (htrace : K^2 * Matrix.trace R < b) :
    constantCorrection K w b R ≤
      traceBudgetPrimitive (K^2) w b (Matrix.trace R) -
      traceBudgetPrimitive (K^2) w b
        (Matrix.trace (outwardResolvent R (constantCorrection K w b R))) := by
  let c := constantCorrection K w b R
  let τ := fun x => Matrix.trace (outwardResolvent R x)
  let F := fun x => frobenius (outwardResolvent R x)
  have hc : 0 ≤ c := (constantCorrection_spec hR K hw.le hb).1
  have hτle {x : ℝ} (hx : 0 ≤ x) : τ x ≤ Matrix.trace R := by
    simpa only [τ, outwardResolvent_zero hR] using
      (outward_trace_strictAnti hR).antitoneOn (show 0 ∈ Ici (0 : ℝ) by simp) hx hx
  have hgap {x : ℝ} (hx : 0 ≤ x) : 0 < b-K^2*τ x := by
    have h := mul_le_mul_of_nonneg_left (hτle hx) (sq_nonneg K)
    linarith
  have hd {x : ℝ} (hx : 0 ≤ x) :
      HasDerivAt (fun y => y + traceBudgetPrimitive (K^2) w b (τ y))
        (1 - w^2/(b-K^2*τ x)^2 * (F x)^2) x := by
    have h := (hasDerivAt_id x).add
      ((hasDerivAt_traceBudgetPrimitive (w := w) hb.ne' (hgap hx).ne').comp x
        (hasDerivAt_outwardTrace hR hx))
    simpa only [τ, F, mul_neg, sub_eq_add_neg] using! h
  have hanti : AntitoneOn (fun y => y + traceBudgetPrimitive (K^2) w b (τ y)) (Icc 0 c) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 c)
    · intro x hx
      exact (hd hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd hx.1.le).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hbefore : b < K^2*τ x+w*F x :=
        leastCorrection_before (f := fun y => regularityCost K w (outwardResolvent R y))
          (b := b) (constantCost_continuous hR K w)
          (constantCost_antitone hR K hw.le) (constantCost_nonempty hR K w hb)
          hx.1.le hx.2
      have hF := frobenius_nonneg (outwardResolvent R x)
      have hg := hgap hx.1.le
      have hsq : (b-K^2*τ x)^2 ≤ w^2*(F x)^2 := by
        nlinarith [mul_nonneg (show 0 ≤ w*F x-(b-K^2*τ x) by linarith)
          (show 0 ≤ w*F x+(b-K^2*τ x) by positivity)]
      have hdiv : 1 ≤ w^2/(b-K^2*τ x)^2 * (F x)^2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hg)]
        simpa only [one_mul] using hsq
      linarith
  have hh := hanti (show 0 ∈ Icc (0 : ℝ) c from ⟨le_rfl, hc⟩)
    (show c ∈ Icc (0 : ℝ) c from ⟨hc, le_rfl⟩) hc
  dsimp [τ] at hh
  rw [outwardResolvent_zero hR, zero_add] at hh
  dsimp [c] at hh ⊢
  linarith

/-- Explicit integration of the trace kernel, with the correct orientation. -/
theorem traceBudget_integral {a w b x y : ℝ} (hb : 0 < b) (ha : 0 ≤ a)
    (hxy : x ≤ y) (hgap : a*y < b) :
    (∫ τ in x..y, w^2/(b-a*τ)^2) =
      traceBudgetPrimitive a w b y - traceBudgetPrimitive a w b x := by
  have hden {τ : ℝ} (hτ : τ ∈ Icc x y) : b-a*τ ≠ 0 := by
    have := mul_le_mul_of_nonneg_left hτ.2 ha
    linarith
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro τ hτ
    rw [uIcc_of_le hxy] at hτ
    exact hasDerivAt_traceBudgetPrimitive hb.ne' (hden hτ)
  · apply ContinuousOn.intervalIntegrable
    intro τ hτ
    rw [uIcc_of_le hxy] at hτ
    have hcont : ContinuousAt (fun y : ℝ => w^2/(b-a*y)^2) τ :=
      continuousAt_const.div ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow 2)
        (pow_ne_zero 2 (hden hτ))
    exact hcont.continuousWithinAt

/-- Finite trace histories: the next row preserves the corrected trace. -/
structure CorrectionTraceChain (m : ℕ) where
  R : ℕ → Matrix ι ι ℝ
  positive : ∀ i ≤ m, (R i).PosDef
  amount : ℕ → ℝ
  nonneg : ∀ i < m, 0 ≤ amount i
  trace_next : ∀ i < m,
    Matrix.trace (R (i+1)) = Matrix.trace (outwardResolvent (R i) (amount i))

namespace CorrectionTraceChain
variable {m : ℕ} (q : CorrectionTraceChain (ι := ι) m)

lemma trace_antitone : AntitoneOn (fun i => Matrix.trace (q.R i)) (Set.Iic m) := by
  have hstep (i : ℕ) (hi : i < m) : Matrix.trace (q.R (i+1)) ≤ Matrix.trace (q.R i) := by
    rw [q.trace_next i hi]
    simpa only [outwardResolvent_zero (q.positive i hi.le)] using
      (outward_trace_strictAnti (q.positive i hi.le)).antitoneOn
        (show 0 ∈ Ici (0 : ℝ) by simp) (q.nonneg i hi) (q.nonneg i hi)
  intro i hi j hj hij
  change i ≤ m at hi
  change j ≤ m at hj
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
      intro hj
      exact (hstep j (by omega)).trans (ih (by omega))

/-- The open trace intervals of separate corrections are disjoint. -/
lemma trace_intervals_disjoint {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i < j) :
    Disjoint (Ioo (Matrix.trace (q.R (i+1))) (Matrix.trace (q.R i)))
      (Ioo (Matrix.trace (q.R (j+1))) (Matrix.trace (q.R j))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h := q.trace_antitone (show i+1 ∈ Iic m from hi)
    (show j ∈ Iic m from hj.le) hij
  linarith [hx.1, hy.2]

/-- Any per-correction trace potential bound telescopes pathwise. -/
theorem total_le_potential (B : ℝ → ℝ)
    (hstep : ∀ i < m, q.amount i ≤ B (Matrix.trace (q.R i)) - B (Matrix.trace (q.R (i+1)))) :
    ∑ i ∈ Finset.range m, q.amount i ≤ B (Matrix.trace (q.R 0)) - B (Matrix.trace (q.R m)) := by
  calc
    _ ≤ ∑ i ∈ Finset.range m,
        (B (Matrix.trace (q.R i))-B (Matrix.trace (q.R (i+1)))) :=
      Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))
    _ = _ := by rw [Finset.sum_range_sub']

end CorrectionTraceChain
end
end SingularValueBounds.KL
