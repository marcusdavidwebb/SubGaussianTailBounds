import SingularValueBounds.KL.Barrier.Budget

/-! # The deterministic adaptive barrier process
The process records its actual inverse gap, the Gram matrix, and both costs.
It is defined for every deterministic row sequence. -/
open Set Filter MeasureTheory
open scoped BigOperators Matrix Topology
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev PositiveResolvent (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  {R : Matrix ι ι ℝ // R.PosDef}

/-- Inverse gap, accumulated exact shifts, accumulated outward corrections,
and the actual uncentred Gram matrix. -/
abbrev BarrierState (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  PositiveResolvent ι × (ℝ × ℝ × Matrix ι ι ℝ)

namespace BarrierState

def R (q : BarrierState ι) : Matrix ι ι ℝ := q.1.1
lemma positive (q : BarrierState ι) : q.R.PosDef := q.1.2
def shifts (q : BarrierState ι) : ℝ := q.2.1
def outward (q : BarrierState ι) : ℝ := q.2.2.1
def gram (q : BarrierState ι) : Matrix ι ι ℝ := q.2.2.2

end BarrierState

/-- `true` is the upper barrier and `false` the lower barrier. -/
def exactShift (upper : Bool) (R : PositiveResolvent ι) (x : ι → ℝ) : ℝ :=
  if upper then upperShift R.1 R.2 x else lowerShift R.1 R.2 x

def rowGap (upper : Bool) (R : PositiveResolvent ι) (x : ι → ℝ) : Matrix ι ι ℝ :=
  if upper then R.1⁻¹ + exactShift upper R x • (1 : Matrix ι ι ℝ) - Matrix.vecMulVec x x
  else R.1⁻¹ + Matrix.vecMulVec x x - exactShift upper R x • (1 : Matrix ι ι ℝ)

lemma rowGap_preserves (upper : Bool) (R : PositiveResolvent ι) (x : ι → ℝ) :
    (rowGap upper R x).PosDef ∧ Matrix.trace (rowGap upper R x)⁻¹ = Matrix.trace R.1 := by
  cases upper
  · exact lowerShift_preserves R.2 x
  · exact upperShift_preserves R.2 x

lemma exactShift_nonneg (upper : Bool) (R : PositiveResolvent ι) (x : ι → ℝ) :
    0 ≤ exactShift upper R x := by
  cases upper
  · exact lowerShift_nonneg R.2 x
  · exact upperShift_nonneg R.2 x

lemma measurable_exactShift (upper : Bool) :
    Measurable (fun z : PositiveResolvent ι × (ι → ℝ) => exactShift upper z.1 z.2) := by
  cases upper
  · exact measurable_lowerShift
  · exact measurable_upperShift

/-- Generic measurable outward rule; concrete profiles supply its cap and budget.
These are analytic process data, never external numerical premises. -/
structure CorrectionRule (ι : Type*) [Fintype ι] [DecidableEq ι] where
  amount : PositiveResolvent ι → ℝ
  measurable : Measurable amount
  nonneg : ∀ R, 0 ≤ amount R

namespace CorrectionRule

def prepared (c : CorrectionRule ι) (R : PositiveResolvent ι) : PositiveResolvent ι :=
  ⟨outwardResolvent R.1 (c.amount R), outwardResolvent_posDef R.2 (c.nonneg R)⟩

lemma measurable_prepared (c : CorrectionRule ι) : Measurable c.prepared := by
  apply Measurable.subtype_mk
  change Measurable (fun R : PositiveResolvent ι => (R.1⁻¹+c.amount R • (1 : Matrix ι ι ℝ))⁻¹)
  apply measurable_matrix_inverse.comp
  exact (measurable_matrix_inverse.comp measurable_subtype_coe).add (c.measurable.smul measurable_const)

lemma prepared_inv (c : CorrectionRule ι) (R : PositiveResolvent ι) :
    (c.prepared R).1⁻¹ = R.1⁻¹ + c.amount R • (1 : Matrix ι ι ℝ) := by
  exact Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (outwardGap_posDef R.2 (c.nonneg R)).isUnit)

def step (c : CorrectionRule ι) (upper : Bool) (q : BarrierState ι) (x : ι → ℝ) : BarrierState ι :=
  let P := c.prepared q.1
  (⟨(rowGap upper P x)⁻¹, (rowGap_preserves upper P x).1.inv⟩,
    q.shifts+exactShift upper P x, q.outward+c.amount q.1, q.gram+Matrix.vecMulVec x x)

lemma step_trace (c : CorrectionRule ι) (upper : Bool) (q : BarrierState ι) (x : ι → ℝ) :
    Matrix.trace (c.step upper q x).R = Matrix.trace (c.prepared q.1).1 :=
  (rowGap_preserves upper (c.prepared q.1) x).2

lemma step_inv (c : CorrectionRule ι) (upper : Bool) (q : BarrierState ι) (x : ι → ℝ) :
    (c.step upper q x).R⁻¹ = rowGap upper (c.prepared q.1) x :=
  Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (rowGap_preserves upper (c.prepared q.1) x).1.isUnit)

attribute [local irreducible] prepared exactShift rowGap
set_option maxHeartbeats 1000000 in
lemma measurable_step (c : CorrectionRule ι) (upper : Bool) :
    Measurable (fun z : BarrierState ι × (ι → ℝ) => c.step upper z.1 z.2) := by
  let T := BarrierState ι × (ι → ℝ)
  have hr : Measurable (fun z : T => z.1.1) := measurable_fst.comp measurable_fst
  have hx : Measurable (fun z : T => z.2) := measurable_snd
  have hP : Measurable (fun z : T => c.prepared z.1.1) := c.measurable_prepared.comp hr
  have hδ : Measurable (fun z : T => exactShift upper (c.prepared z.1.1) z.2) :=
    (measurable_exactShift upper).comp (hP.prodMk hx)
  have hR : Measurable (fun z : T => (c.prepared z.1.1).1⁻¹) :=
    measurable_matrix_inverse.comp (measurable_subtype_coe.comp hP)
  have ho : Measurable (fun z : T => Matrix.vecMulVec z.2 z.2) :=
    (show Continuous (fun x : ι → ℝ => Matrix.vecMulVec x x) by fun_prop).measurable.comp hx
  have hg : Measurable (fun z : T => rowGap upper (c.prepared z.1.1) z.2) := by
    cases upper
    · simpa only [rowGap, Bool.false_eq_true, if_false] using! (hR.add ho).sub (hδ.smul measurable_const)
    · simpa only [rowGap, Bool.true_eq, if_true] using! (hR.add (hδ.smul measurable_const)).sub ho
  have hs : Measurable (fun z : T => z.1.shifts) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hc : Measurable (fun z : T => z.1.outward) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hgram : Measurable (fun z : T => z.1.gram) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hnew : Measurable (fun z : T =>
      (⟨(rowGap upper (c.prepared z.1.1) z.2)⁻¹,
        (rowGap_preserves upper (c.prepared z.1.1) z.2).1.inv⟩ : PositiveResolvent ι)) :=
    (measurable_matrix_inverse.comp hg).subtype_mk
  simpa only [step, BarrierState.shifts, BarrierState.outward, BarrierState.gram,
    Pi.add_apply, Function.comp_def] using!
    hnew.prodMk ((hs.add hδ).prodMk ((hc.add (c.measurable.comp hr)).prodMk (hgram.add ho)))

attribute [local semireducible] prepared exactShift rowGap

/-- Iteration from an arbitrary positive starting resolvent. -/
def process (c : CorrectionRule ι) (upper : Bool) (R₀ : PositiveResolvent ι)
    (x : ℕ → ι → ℝ) : ℕ → BarrierState ι
  | 0 => (R₀, 0, 0, 0)
  | i+1 => c.step upper (c.process upper R₀ x i) (x i)

lemma process_gram (c : CorrectionRule ι) (upper : Bool) (R₀ : PositiveResolvent ι)
    (x : ℕ → ι → ℝ) (m : ℕ) :
    (c.process upper R₀ x m).gram = ∑ i ∈ Finset.range m, Matrix.vecMulVec (x i) (x i) := by
  induction m with
  | zero => simp [process, BarrierState.gram]
  | succ m ih =>
    simpa only [process, step, BarrierState.gram, Finset.sum_range_succ] using
      congrArg (fun A => A + Matrix.vecMulVec (x m) (x m)) ih

lemma process_shifts (c : CorrectionRule ι) (upper : Bool) (R₀ : PositiveResolvent ι)
    (x : ℕ → ι → ℝ) (m : ℕ) :
    (c.process upper R₀ x m).shifts = ∑ i ∈ Finset.range m,
      exactShift upper (c.prepared (c.process upper R₀ x i).1) (x i) := by
  induction m with
  | zero => simp [process, BarrierState.shifts]
  | succ m ih =>
    simpa only [process, step, BarrierState.shifts, Finset.sum_range_succ] using
      congrArg (fun a => a + exactShift upper (c.prepared (c.process upper R₀ x m).1) (x m)) ih

lemma process_outward (c : CorrectionRule ι) (upper : Bool) (R₀ : PositiveResolvent ι)
    (x : ℕ → ι → ℝ) (m : ℕ) :
    (c.process upper R₀ x m).outward = ∑ i ∈ Finset.range m, c.amount (c.process upper R₀ x i).1 := by
  induction m with
  | zero => simp [process, BarrierState.outward]
  | succ m ih =>
    simpa only [process, step, BarrierState.outward, Finset.sum_range_succ] using
      congrArg (fun a => a+c.amount (c.process upper R₀ x m).1) ih

lemma process_shifts_nonneg (c : CorrectionRule ι) (upper : Bool) (R₀ : PositiveResolvent ι)
    (x : ℕ → ι → ℝ) (m : ℕ) : 0 ≤ (c.process upper R₀ x m).shifts := by
  rw [c.process_shifts]
  exact Finset.sum_nonneg (fun i _ => exactShift_nonneg _ _ _)

lemma process_outward_nonneg (c : CorrectionRule ι) (upper : Bool) (R₀ : PositiveResolvent ι)
    (x : ℕ → ι → ℝ) (m : ℕ) : 0 ≤ (c.process upper R₀ x m).outward := by
  rw [c.process_outward]
  exact Finset.sum_nonneg (fun i _ => c.nonneg _)

/-- Trace history attached to the actual process; row updates preserve each endpoint. -/
def traceChain (c : CorrectionRule ι) (upper : Bool) (R₀ : PositiveResolvent ι)
    (x : ℕ → ι → ℝ) (m : ℕ) : CorrectionTraceChain (ι := ι) m where
  R i := (c.process upper R₀ x i).R
  positive i _ := (c.process upper R₀ x i).positive
  amount i := c.amount (c.process upper R₀ x i).1
  nonneg i _ := c.nonneg _
  trace_next i _ := c.step_trace upper (c.process upper R₀ x i) (x i)

/-- The inverse gap has exactly the accumulated scalar cost and Gram matrix. -/
lemma process_inverse (c : CorrectionRule ι) (upper : Bool) (R₀ : PositiveResolvent ι)
    (x : ℕ → ι → ℝ) (m : ℕ) :
    (c.process upper R₀ x m).R⁻¹ =
      if upper then R₀.1⁻¹ + ((c.process upper R₀ x m).shifts +
        (c.process upper R₀ x m).outward) • (1 : Matrix ι ι ℝ) - (c.process upper R₀ x m).gram
      else R₀.1⁻¹ + (c.process upper R₀ x m).gram +
        ((c.process upper R₀ x m).outward-(c.process upper R₀ x m).shifts) • (1 : Matrix ι ι ℝ) := by
  cases upper <;> induction m with
  | zero => simp [process, BarrierState.R, BarrierState.shifts, BarrierState.outward, BarrierState.gram]
  | succ m ih =>
    rw [process, c.step_inv]
    simp only [rowGap, Bool.false_eq_true, Bool.true_eq, if_false, if_true]
    rw [c.prepared_inv]
    simp only [Bool.false_eq_true, Bool.true_eq, if_false, if_true, BarrierState.R] at ih
    rw [ih]
    simp only [process, step, BarrierState.shifts, BarrierState.outward, BarrierState.gram,
      add_smul, sub_smul]
    abel

end CorrectionRule

/-- Concrete constant-profile correction rule, proved measurable and total. -/
def constantCorrectionRule (K : ℝ) {w b : ℝ} (hw : 0 ≤ w) (hb : 0 < b) : CorrectionRule ι where
  amount R := constantCorrection K w b R.1
  measurable := measurable_constantCorrection K hw hb
  nonneg R := (constantCorrection_spec R.2 K hw hb).1

lemma constantCorrectionRule_cap (K : ℝ) {w b : ℝ} (hw : 0 ≤ w) (hb : 0 < b)
    (R : PositiveResolvent ι) :
    regularityCost K w ((constantCorrectionRule K hw hb).prepared R).1 ≤ b :=
  (constantCorrection_spec R.2 K hw hb).2

/-- Total correction cost for every deterministic row sequence, before evaluating
its explicit scalar initial trace. -/
theorem constant_process_outward_le (K : ℝ) {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (upper : Bool) (R₀ : PositiveResolvent ι) (x : ℕ → ι → ℝ) (m : ℕ)
    (htrace : K^2 * Matrix.trace R₀.1 < b) :
    ((constantCorrectionRule K hw.le hb).process upper R₀ x m).outward ≤
      traceBudgetPrimitive (K^2) w b (Matrix.trace R₀.1) := by
  let c := constantCorrectionRule (ι := ι) K hw.le hb
  let q := c.traceChain upper R₀ x m
  have hτ (i : ℕ) (hi : i ≤ m) : Matrix.trace (q.R i) ≤ Matrix.trace R₀.1 := by
    simpa only [q, CorrectionRule.traceChain, CorrectionRule.process, BarrierState.R] using
      q.trace_antitone (show 0 ∈ Iic m by simp) (show i ∈ Iic m from hi) (Nat.zero_le i)
  have hgap (i : ℕ) (hi : i ≤ m) : K^2*Matrix.trace (q.R i) < b :=
    (mul_le_mul_of_nonneg_left (hτ i hi) (sq_nonneg K)).trans_lt htrace
  have ht := q.total_le_potential (traceBudgetPrimitive (K^2) w b) (fun i hi => by
    rw [q.trace_next i hi]
    exact constantCorrection_budget (q.positive i hi.le) K hw hb (hgap i hi.le))
  have hn : 0 ≤ traceBudgetPrimitive (K^2) w b (Matrix.trace (q.R m)) :=
    traceBudgetPrimitive_nonneg hb (trace_pos (q.positive m le_rfl)).le (sub_pos.mpr (hgap m le_rfl))
  have heq : ((constantCorrectionRule K hw.le hb).process upper R₀ x m).outward =
      ∑ i ∈ Finset.range m, q.amount i := c.process_outward upper R₀ x m
  rw [heq]
  have hzero : Matrix.trace (q.R 0) = Matrix.trace R₀.1 := rfl
  rw [hzero] at ht
  linarith

end
end SingularValueBounds.KL
