import SingularValueBounds.KL.Barrier.Initialization
import SingularValueBounds.KL.Barrier.Adaptive
import SingularValueBounds.SpectralConcentration.Chernoff
import SingularValueBounds.Main.VariationalOptimization

/-! # Independent-row iteration and transfer
The deterministic barrier process is independent of the next row because
its entire state is a measurable function of the preceding rows. -/
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {m n : ℕ} [NeZero n]

/-- The actual adaptive state after the first `i` random rows. -/
def rowProcess (c : CorrectionRule (Fin n)) (upper : Bool) (R₀ : PositiveResolvent (Fin n))
    (X : Fin m → Ω → Fin n → ℝ) (i : ℕ) (ω : Ω) : BarrierState (Fin n) :=
  c.process upper R₀ (fun j => spectralRow X j ω) i

omit [MeasurableSpace Ω] in
lemma rowProcess_eq_adaptive (c : CorrectionRule (Fin n)) (upper : Bool)
    (R₀ : PositiveResolvent (Fin n)) (X : Fin m → Ω → Fin n → ℝ) (i : ℕ) :
    rowProcess c upper R₀ X i =
      adaptiveState (fun _ z => c.step upper z.1 z.2) (R₀,0,0,0) 0 X i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    funext ω
    change c.step upper (rowProcess c upper R₀ X i ω) (spectralRow X i ω) = _
    rw [ih]
    rfl

/-- The complete adaptive barrier history is independent of the next row. -/
theorem rowProcess_independent (c : CorrectionRule (Fin n)) (upper : Bool)
    (R₀ : PositiveResolvent (Fin n)) (X : Fin m → Ω → Fin n → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (i : Fin m) :
    Measurable (rowProcess c upper R₀ X i.val) ∧
      IndepFun (rowProcess c upper R₀ X i.val) (X i) μ := by
  apply past_state_independent X hX hind i
  rw [rowProcess_eq_adaptive]
  exact measurable_adaptiveState_past _ (fun _ => c.measurable_step upper) _ _ _ _

omit [MeasurableSpace Ω] in
/-- Actual Gram matrix at the final state. -/
lemma rowProcess_gram (c : CorrectionRule (Fin n)) (upper : Bool)
    (R₀ : PositiveResolvent (Fin n)) (X : Fin m → Ω → Fin n → ℝ) (ω : Ω) :
    (rowProcess c upper R₀ X m ω).gram = (rowMatrix X ω)ᴴ * rowMatrix X ω := by
  rw [rowProcess, c.process_gram, ← Fin.sum_univ_eq_sum_range, gram_eq_sum_outer]
  apply Finset.sum_congr rfl
  intro i _
  simp only [spectralRow, dif_pos i.isLt]
  rfl

attribute [local irreducible] CorrectionRule.prepared exactShift rowGap
set_option maxHeartbeats 800000 in
/-- MGF iteration for the actual exact shifts, for an arbitrary correction rule.
The one-row hypothesis is stated analytically and explicitly. -/
theorem rowProcess_mgf [IsProbabilityMeasure μ]
    (c : CorrectionRule (Fin n)) (upper : Bool) (R₀ : PositiveResolvent (Fin n))
    (X : Fin m → Ω → Fin n → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (A θ ν : ℝ)
    (hrow : ∀ i : Fin m, ∀ R : PositiveResolvent (Fin n),
      Integrable (fun ω => Real.exp (θ*A*exactShift upper (c.prepared R) (X i ω))) μ ∧
      (∫ ω, Real.exp (θ*A*exactShift upper (c.prepared R) (X i ω)) ∂μ) ≤
        Real.exp (θ/(1-ν*θ))) :
    Integrable (fun ω => Real.exp (θ*A*(rowProcess c upper R₀ X m ω).shifts)) μ ∧
      (∫ ω, Real.exp (θ*A*(rowProcess c upper R₀ X m ω).shifts) ∂μ) ≤
        Real.exp ((m:ℝ)*θ/(1-ν*θ)) := by
  let step := fun (_ : ℕ) (z : BarrierState (Fin n) × (Fin n → ℝ)) => c.step upper z.1 z.2
  let w := fun q : BarrierState (Fin n) => Real.exp (θ*A*q.shifts)
  let g := fun (_ : ℕ) (z : BarrierState (Fin n) × (Fin n → ℝ)) =>
    Real.exp (θ*A*exactShift upper (c.prepared z.1.1) z.2)
  have hw : Measurable w := Real.continuous_exp.measurable.comp
    (measurable_const.mul (show Measurable (fun q : BarrierState (Fin n) => q.shifts) from
      measurable_fst.comp measurable_snd))
  have hshift : Measurable (fun z : BarrierState (Fin n) × (Fin n → ℝ) =>
      exactShift upper (c.prepared z.1.1) z.2) :=
    (measurable_exactShift upper).comp
      ((c.measurable_prepared.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hg : ∀ i, Measurable (g i) := fun _ =>
    Real.continuous_exp.measurable.comp (measurable_const.mul hshift)
  have hfactor : ∀ i q x, w (step i (q,x)) = w q*g i (q,x) := by
    intro i q x
    change Real.exp (θ*A*(q.shifts+exactShift upper (c.prepared q.1) x)) = _
    rw [mul_add, Real.exp_add]
  have hmap (i : Fin m) (R : BarrierState (Fin n)) :
      Integrable (fun x => g i.val (R,x)) (μ.map (X i)) ∧
      (∫ x, g i.val (R,x) ∂μ.map (X i)) ≤ Real.exp (θ/(1-ν*θ)) := by
    have hf : Measurable (fun x : Fin n → ℝ => g i.val (R,x)) :=
      (hg i.val).comp (measurable_const.prodMk measurable_id)
    constructor
    · exact (integrable_map_measure hf.aestronglyMeasurable (hX i).aemeasurable).2 (hrow i R.1).1
    · rw [integral_map (hX i).aemeasurable hf.aestronglyMeasurable]
      exact (hrow i R.1).2
  have hi := adaptive_weighted_iteration X hX hind step (fun _ => c.measurable_step upper)
    (R₀,0,0,0) 0 w hw (fun _ => Real.exp_nonneg _) (by simp [w, BarrierState.shifts])
    g hg (fun _ _ => Real.exp_nonneg _) (Real.exp (θ/(1-ν*θ))) (Real.exp_nonneg _)
    hfactor (fun i R => (hmap i R).1) (fun i R => (hmap i R).2)
  have heq : (fun ω => Real.exp (θ*A*(rowProcess c upper R₀ X m ω).shifts)) =
      (fun ω => w (adaptiveState step (R₀,0,0,0) 0 X m ω)) := by
    rw [rowProcess_eq_adaptive]
  rw [heq]
  convert hi using 1
  rw [← Real.exp_nat_mul]
  ring

attribute [local semireducible] CorrectionRule.prepared exactShift rowGap

/-- Constant-cap lower exact-shift iteration from the stated row estimates. -/
theorem lower_process_mgf [IsProbabilityMeasure μ]
    (X : Fin m → Ω → Fin n → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (K : ℝ) {w ν b θ : ℝ} (hw : 0 < w) (hb : 0 < b) (hθ : θ < 0)
    (hrow : ∀ i, LowerRowEstimate μ (X i) K w ν) (R₀ : PositiveResolvent (Fin n)) :
    Integrable (fun ω => Real.exp (θ*(1+b)*
      (rowProcess (constantCorrectionRule K hw.le hb) false R₀ X m ω).shifts)) μ ∧
      (∫ ω, Real.exp (θ*(1+b)*
        (rowProcess (constantCorrectionRule K hw.le hb) false R₀ X m ω).shifts) ∂μ) ≤
        Real.exp ((m:ℝ)*θ/(1-ν*θ)) := by
  apply rowProcess_mgf _ false R₀ X hX hind (1+b) θ ν
  intro i R
  have h := hrow i ((constantCorrectionRule K hw.le hb).prepared R).1
    ((constantCorrectionRule K hw.le hb).prepared R).2 b
    (constantCorrectionRule_cap K hw.le hb R) hb (-θ) (neg_pos.mpr hθ)
  simpa only [exactShift, Bool.false_eq_true, if_false, neg_neg, mul_neg, sub_eq_add_neg,
    neg_div, neg_mul] using h

/-- Constant-cap upper exact-shift iteration from the stated row estimates. -/
theorem upper_process_mgf [IsProbabilityMeasure μ]
    (X : Fin m → Ω → Fin n → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (K : ℝ) {w ν b θ : ℝ} (hw : 0 < w) (hb : 0 < b) (hb1 : b < 1)
    (hθ : 0 < θ) (hθν : θ < 1/ν)
    (hrow : ∀ i, UpperRowEstimate μ (X i) K w ν) (R₀ : PositiveResolvent (Fin n)) :
    Integrable (fun ω => Real.exp (θ*(1-b)*
      (rowProcess (constantCorrectionRule K hw.le hb) true R₀ X m ω).shifts)) μ ∧
      (∫ ω, Real.exp (θ*(1-b)*
        (rowProcess (constantCorrectionRule K hw.le hb) true R₀ X m ω).shifts) ∂μ) ≤
        Real.exp ((m:ℝ)*θ/(1-ν*θ)) := by
  apply rowProcess_mgf _ true R₀ X hX hind (1-b) θ ν
  intro i R
  exact hrow i ((constantCorrectionRule K hw.le hb).prepared R).1
    ((constantCorrectionRule K hw.le hb).prepared R).2 b
    (constantCorrectionRule_cap K hw.le hb R) hb1 θ hθ hθν

omit [MeasurableSpace Ω] in
/-- The actual lower barrier gives a strict bound for the squared minimum. -/
lemma rowProcess_lower_sq (c : CorrectionRule (Fin n)) (u : ℝ) (hu : 0 < u)
    (X : Fin m → Ω → Fin n → ℝ) (ω : Ω) :
    (rowProcess c false (scalarResolvent u hu) X m ω).shifts-u-
      (rowProcess c false (scalarResolvent u hu) X m ω).outward <
        smallestSingularValue (rowMatrix X ω)^2 := by
  let q := rowProcess c false (scalarResolvent u hu) X m ω
  have hg := process_lower_gap c u hu (fun j => spectralRow X j ω) m
  change (q.gram-(q.shifts-u-q.outward) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef at hg
  have hgram : q.gram = (rowMatrix X ω)ᴴ*rowMatrix X ω := rowProcess_gram c false _ X ω
  rw [hgram] at hg
  have hh := smallestSingularValue_sq_gt (rowMatrix X ω) (a := u+q.outward-q.shifts) (by
    convert hg using 1 <;> simp only [sub_smul, add_smul, neg_smul, one_smul] <;> abel)
  dsimp [q] at hh ⊢
  linarith

omit [MeasurableSpace Ω] in
lemma rowProcess_upper_sq (c : CorrectionRule (Fin n)) (u : ℝ) (hu : 0 < u)
    (X : Fin m → Ω → Fin n → ℝ) (ω : Ω) :
    largestSingularValue (rowMatrix X ω)^2 <
      (rowProcess c true (scalarResolvent u hu) X m ω).shifts+u+
        (rowProcess c true (scalarResolvent u hu) X m ω).outward := by
  have hg := process_upper_gap c u hu (fun j => spectralRow X j ω) m
  change (((rowProcess c true (scalarResolvent u hu) X m ω).shifts+u+
    (rowProcess c true (scalarResolvent u hu) X m ω).outward) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      (rowProcess c true (scalarResolvent u hu) X m ω).gram).PosDef at hg
  rw [rowProcess_gram] at hg
  exact largestSingularValue_sq_lt _ (by simpa only [one_smul] using hg)

/-- Analytic lower-transfer input. The total pathwise cost is `N/b`.
This interface also accepts future mixed-profile budgets. -/
structure LowerTransferInput (μ : Measure Ω) (X : Fin m → Ω → Fin n → ℝ)
    (N ν b : ℝ) where
  S : Ω → ℝ
  integrable : ∀ θ : ℝ, θ < 0 → Integrable (fun ω => Real.exp (θ*((1+b)*S ω))) μ
  mgf : ∀ θ : ℝ, θ < 0 →
    (∫ ω, Real.exp (θ*((1+b)*S ω)) ∂μ) ≤ Real.exp ((m:ℝ)*θ/(1-ν*θ))
  gap : ∀ ω, S ω-N/b < smallestSingularValue (rowMatrix X ω)^2

structure UpperTransferInput (μ : Measure Ω) (X : Fin m → Ω → Fin n → ℝ)
    (N ν b : ℝ) where
  S : Ω → ℝ
  integrable : ∀ θ : ℝ, 0 < θ → θ < 1/ν →
    Integrable (fun ω => Real.exp (θ*((1-b)*S ω))) μ
  mgf : ∀ θ : ℝ, 0 < θ → θ < 1/ν →
    (∫ ω, Real.exp (θ*((1-b)*S ω)) ∂μ) ≤ Real.exp ((m:ℝ)*θ/(1-ν*θ))
  gap : ∀ ω, largestSingularValue (rowMatrix X ω)^2 < S ω+N/b

/-- The proved constant-cap process discharges every deterministic budget. -/
def constantLowerTransferInput [IsProbabilityMeasure μ]
    (X : Fin m → Ω → Fin n → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (K : ℝ) {w ν b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (hrow : ∀ i, LowerRowEstimate μ (X i) K w ν) :
    LowerTransferInput μ X (K^2*n+2*w*Real.sqrt n) ν b := by
  let u := initialDistance n K w b
  have hu : 0 < u := initialDistance_pos (NeZero.pos n) K hw hb
  let R₀ := scalarResolvent (ι := Fin n) u hu
  let c := constantCorrectionRule (ι := Fin n) K hw.le hb
  refine ⟨(fun ω => (rowProcess c false R₀ X m ω).shifts), ?_, ?_, ?_⟩
  · intro θ hθ
    simpa only [mul_assoc] using (lower_process_mgf X hX hind K hw hb hθ hrow R₀).1
  · intro θ hθ
    simpa only [mul_assoc] using (lower_process_mgf X hX hind K hw hb hθ hrow R₀).2
  · intro ω
    have hg := rowProcess_lower_sq c u hu X ω
    have hbq := constant_process_budget (ι := Fin n) K hw hb false (fun j => spectralRow X j ω) m
    have hcost := correction_total_cost (K := K) hbq
    simp only [Fintype.card_fin] at hcost
    change u+(rowProcess c false R₀ X m ω).outward ≤ (K^2*n+2*w*Real.sqrt n)/b at hcost
    dsimp [R₀] at hg ⊢
    linarith

def constantUpperTransferInput [IsProbabilityMeasure μ]
    (X : Fin m → Ω → Fin n → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (K : ℝ) {w ν b : ℝ} (hw : 0 < w) (hb : 0 < b) (hb1 : b < 1)
    (hrow : ∀ i, UpperRowEstimate μ (X i) K w ν) :
    UpperTransferInput μ X (K^2*n+2*w*Real.sqrt n) ν b := by
  let u := initialDistance n K w b
  have hu : 0 < u := initialDistance_pos (NeZero.pos n) K hw hb
  let R₀ := scalarResolvent (ι := Fin n) u hu
  let c := constantCorrectionRule (ι := Fin n) K hw.le hb
  refine ⟨(fun ω => (rowProcess c true R₀ X m ω).shifts), ?_, ?_, ?_⟩
  · intro θ hθ hθν
    simpa only [mul_assoc] using (upper_process_mgf X hX hind K hw hb hb1 hθ hθν hrow R₀).1
  · intro θ hθ hθν
    simpa only [mul_assoc] using (upper_process_mgf X hX hind K hw hb hb1 hθ hθν hrow R₀).2
  · intro ω
    have hg := rowProcess_upper_sq c u hu X ω
    have hbq := constant_process_budget (ι := Fin n) K hw hb true (fun j => spectralRow X j ω) m
    have hcost := correction_total_cost (K := K) hbq
    simp only [Fintype.card_fin] at hcost
    change u+(rowProcess c true R₀ X m ω).outward ≤ (K^2*n+2*w*Real.sqrt n)/b at hcost
    dsimp [R₀] at hg ⊢
    linarith

/-- Separate dimension and fluctuation costs, lower tail. The strict allowance
`d < D` also covers an exactly zero final singular-value threshold. -/
theorem lower_transfer [IsProbabilityMeasure μ]
    (X : Fin m → Ω → Fin n → ℝ) {N d D q : ℝ}
    (hm : 0 < m) (hd : 0 < d) (hd2 : d^2=N) (hD : d < D) (hq : 0 < q)
    (hprocess : ∀ b : ℝ, 0 < b → Nonempty (LowerTransferInput μ X N (2*q^2) b))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | smallestSingularValue (rowMatrix X ω) ≤ Real.sqrt m-D-q*t} ≤
      Real.exp (-t^2/2) := by
  by_cases ht0 : t=0
  · subst t
    simpa using (measureReal_le_one (μ := μ)
      (s := {ω | smallestSingularValue (rowMatrix X ω) ≤ Real.sqrt m-D-q*0}))
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hneg : Real.sqrt m-D-q*t < 0
  · have he : {ω | smallestSingularValue (rowMatrix X ω) ≤ Real.sqrt m-D-q*t} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt (hneg.trans_le (smallestSingularValue_nonneg _))
    rw [he]
    simpa using Real.exp_nonneg (-t^2/2)
  have htarget : 0 ≤ Real.sqrt m-D-q*t := le_of_not_gt hneg
  let s := Real.sqrt m-q*t
  have hs : d < s := by dsimp [s]; linarith
  let b := d/(s-d)
  have hb : 0 < b := div_pos hd (sub_pos.mpr hs)
  obtain ⟨input⟩ := hprocess b hb
  have htail := spectral_lower_sqrt_tail (fun ω => (1+b)*input.S ω)
    (by exact_mod_cast hm) hq input.integrable input.mgf htp (hd.trans hs)
  have hcost : s^2/(1+b)-N/b = (s-d)^2 := by
    simpa only [one_mul] using spectral_lower_optimal_cost (A := 1) (by norm_num) hd hs
      (by simpa using hd2)
  apply le_trans (measureReal_mono ?_) htail
  intro ω hω
  change smallestSingularValue (rowMatrix X ω) ≤ Real.sqrt m-D-q*t at hω
  change (1+b)*input.S ω ≤ s^2
  have hσ : smallestSingularValue (rowMatrix X ω) ≤ s-D := by dsimp [s]; linarith
  have hsq : smallestSingularValue (rowMatrix X ω)^2 ≤ (s-d)^2 := by
    nlinarith [smallestSingularValue_nonneg (rowMatrix X ω)]
  have hgap := input.gap ω
  rw [← hcost] at hsq
  have hdiv : input.S ω < s^2/(1+b) := by linarith
  have hbc : 0 < 1+b := by positivity
  simpa only [mul_comm] using ((lt_div_iff₀ hbc).mp hdiv).le

/-- Separate dimension and fluctuation costs, upper tail. -/
theorem upper_transfer [IsProbabilityMeasure μ]
    (X : Fin m → Ω → Fin n → ℝ) {N d D q : ℝ}
    (hm : 0 < m) (hd : 0 < d) (hd2 : d^2=N) (hD : d ≤ D) (hq : 0 < q)
    (hprocess : ∀ b : ℝ, 0 < b → b < 1 → Nonempty (UpperTransferInput μ X N (2*q^2) b))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | Real.sqrt m+D+q*t ≤ largestSingularValue (rowMatrix X ω)} ≤
      Real.exp (-t^2/2) := by
  by_cases ht0 : t=0
  · subst t
    simpa using (measureReal_le_one (μ := μ)
      (s := {ω | Real.sqrt m+D+q*0 ≤ largestSingularValue (rowMatrix X ω)}))
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let s := Real.sqrt m+q*t
  have hs : 0 < s := by
    exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by exact_mod_cast hm)) (mul_nonneg hq.le ht)
  let b := d/(s+d)
  have hb : 0 < b := div_pos hd (add_pos hs hd)
  have hb1 : b < 1 := (div_lt_one (add_pos hs hd)).mpr (by linarith)
  have hbc : 0 < 1-b := sub_pos.mpr hb1
  obtain ⟨input⟩ := hprocess b hb hb1
  have htail := spectral_upper_sqrt_tail (fun ω => (1-b)*input.S ω)
    (by exact_mod_cast hm) hq input.integrable input.mgf htp
  have hcost : N/b+s^2/(1-b) = (s+d)^2 := by
    simpa only [one_mul] using spectral_upper_optimal_cost (A := 1) (by norm_num) hd hs
      (by simpa using hd2)
  apply le_trans (measureReal_mono ?_) htail
  intro ω hω
  change Real.sqrt m+D+q*t ≤ largestSingularValue (rowMatrix X ω) at hω
  change s^2 ≤ (1-b)*input.S ω
  have hσ : s+d ≤ largestSingularValue (rowMatrix X ω) := by dsimp [s]; linarith
  have hsq : (s+d)^2 ≤ largestSingularValue (rowMatrix X ω)^2 := by
    have hp : 0 ≤ largestSingularValue (rowMatrix X ω)+(s+d) := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) hp]
  have hgap := input.gap ω
  rw [← hcost] at hsq
  have hdiv : s^2/(1-b) < input.S ω := by linarith
  simpa only [mul_comm] using ((div_lt_iff₀ hbc).mp hdiv).le

/-- Strict scalar allowance for the constant-profile dimension cost. -/
theorem constant_dimension_cost_lt {K w : ℝ} (hK : 0 < K) (hw : 0 < w) :
    Real.sqrt (K^2*n+2*w*Real.sqrt n) < K*Real.sqrt n+w/K := by
  have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hN : 0 ≤ K^2*n+2*w*Real.sqrt n := by positivity
  have hd := Real.sq_sqrt hN
  have hallow : 0 < K*Real.sqrt n+w/K := by positivity
  have hform : (K*Real.sqrt n+w/K)^2 = K^2*n+2*w*Real.sqrt n+(w/K)^2 := by
    rw [add_sq, mul_pow, hs]
    field_simp
  nlinarith [sq_pos_of_pos (div_pos hw hK), Real.sqrt_nonneg (K^2*n+2*w*Real.sqrt n)]

/-- The same strict allowance for the mixed-profile budget
`d² = K² n + 2 K² L H √n`. The budget proof itself is supplied by the
profile integration package through `LowerTransferInput`. -/
theorem mixed_dimension_cost_lt {K L H : ℝ} (hK : 0 < K) (hL : 0 < L) (hH : 0 < H) :
    Real.sqrt (K^2*n+2*K^2*L*H*Real.sqrt n) < K*Real.sqrt n+K*L*H := by
  have h := constant_dimension_cost_lt (n := n) hK (show 0 < K^2*L*H by positivity)
  have he : K^2*L*H/K=K*L*H := by field_simp
  rw [he] at h
  convert h using 1 <;> congr 1 <;> ring

/-- Lemma S1.2, lower half, from its exact one-row estimates. -/
theorem lower_tail_from_row_estimates [IsProbabilityMeasure μ]
    (X : Fin m → Ω → Fin n → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hm : 0 < m) {K w ν : ℝ} (hK : 0 < K) (hw : 0 < w) (hν : 0 < ν)
    (hrow : ∀ i, LowerRowEstimate μ (X i) K w ν) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | smallestSingularValue (rowMatrix X ω) ≤
      Real.sqrt m-K*Real.sqrt n-w/K-Real.sqrt (ν/2)*t} ≤ Real.exp (-t^2/2) := by
  let N := K^2*n+2*w*Real.sqrt n
  have hN : 0 < N := by
    have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
    dsimp [N]
    positivity
  have hq : 0 < Real.sqrt (ν/2) := Real.sqrt_pos.mpr (by positivity)
  have hνq : 2*Real.sqrt (ν/2)^2=ν := by rw [Real.sq_sqrt (by positivity : 0 ≤ ν/2)]; ring
  have htail := lower_transfer X hm (Real.sqrt_pos.mpr hN) (Real.sq_sqrt hN.le)
    (constant_dimension_cost_lt (n := n) hK hw) hq (fun b hb => by
      rw [hνq]
      exact ⟨constantLowerTransferInput X hX hind K hw hb hrow⟩) ht
  simpa only [sub_add_eq_sub_sub] using htail

/-- Lemma S1.2, upper half, from its exact one-row estimates. -/
theorem upper_tail_from_row_estimates [IsProbabilityMeasure μ]
    (X : Fin m → Ω → Fin n → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hm : 0 < m) {K w ν : ℝ} (hK : 0 < K) (hw : 0 < w) (hν : 0 < ν)
    (hrow : ∀ i, UpperRowEstimate μ (X i) K w ν) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | Real.sqrt m+K*Real.sqrt n+w/K+Real.sqrt (ν/2)*t ≤
      largestSingularValue (rowMatrix X ω)} ≤ Real.exp (-t^2/2) := by
  let N := K^2*n+2*w*Real.sqrt n
  have hN : 0 < N := by
    have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
    dsimp [N]
    positivity
  have hq : 0 < Real.sqrt (ν/2) := Real.sqrt_pos.mpr (by positivity)
  have hνq : 2*Real.sqrt (ν/2)^2=ν := by rw [Real.sq_sqrt (by positivity : 0 ≤ ν/2)]; ring
  have htail := upper_transfer X hm (Real.sqrt_pos.mpr hN) (Real.sq_sqrt hN.le)
    (constant_dimension_cost_lt (n := n) hK hw).le hq (fun b hb hb1 => by
      rw [hνq]
      exact ⟨constantUpperTransferInput X hX hind K hw hb hb1 hrow⟩) ht
  simpa only [add_assoc] using htail

end
end SingularValueBounds.KL
