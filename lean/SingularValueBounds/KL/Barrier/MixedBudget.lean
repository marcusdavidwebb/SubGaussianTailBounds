import SingularValueBounds.KL.Barrier.MixedCorrections

/-! # Mixed-cap trace accounting

The scalar potential is differentiated only while a correction is active.
Consequently no differentiability at the scalar cap's stopping point is
required. The final theorem below applies this to the actual process.
-/
open Set Filter MeasureTheory
open scoped BigOperators Matrix Topology
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem mixedCorrection_le_potential (R : PositiveResolvent ι)
    {a : ℝ} (ha : 0 ≤ a) {h : ℝ → ℝ} (hc : Continuous h)
    (hm : MonotoneOn h (Icc (0 : ℝ) 1)) (h0 : ∀ k ∈ Icc (0 : ℝ) 1, 0 ≤ h k)
    {b : ℝ} (hb : 0 < b) (B k : ℝ → ℝ) (hB : ContinuousOn B (Ioi 0))
    (hd : ∀ Q : PositiveResolvent ι, Matrix.trace Q.1 ≤ Matrix.trace R.1 →
      b < mixedCost a h Q → HasDerivAt B (k (Matrix.trace Q.1)) (Matrix.trace Q.1))
    (hk : ∀ Q : PositiveResolvent ι, Matrix.trace Q.1 ≤ Matrix.trace R.1 →
      b < mixedCost a h Q → 1 ≤ k (Matrix.trace Q.1) * (frobenius Q.1)^2) :
    mixedCorrection a h b R ≤ B (Matrix.trace R.1) -
      B (Matrix.trace (outwardState R (mixedCorrection a h b R)).1) := by
  let c := mixedCorrection a h b R
  let τ := fun x => Matrix.trace (outwardState R x).1
  have hcn : 0 ≤ c := (mixedCorrection_spec R ha hc hm hb).1
  have hτ (x : ℝ) (hx : 0 ≤ x) : τ x ≤ Matrix.trace R.1 := by
    dsimp [τ]
    rw [outwardState_of_nonneg R hx]
    simpa only [outwardResolvent_zero R.2] using
      (outward_trace_strictAnti R.2).antitoneOn (show 0 ∈ Ici (0 : ℝ) by simp) hx hx
  have ht : Continuous τ := by
    exact (show Continuous (fun Q : PositiveResolvent ι => Matrix.trace Q.1) by
      fun_prop).comp (continuous_outwardState R)
  have hcont : Continuous (fun x => x+B (τ x)) := by
    exact continuous_id.add (hB.comp_continuous ht (fun x => trace_pos (outwardState R x).2))
  have hanti : AntitoneOn (fun x => x+B (τ x)) (Icc 0 c) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 c)
    · exact hcont.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hbefore : b < mixedCost a h (outwardState R x) :=
        leastCorrection_before (f := fun ω => mixedCost a h (outwardState R ω)) (b := b)
          (mixedCost_outward_continuous R a hc).continuousOn
          (mixedCost_outward_antitone R ha hm h0) (mixedCost_outward_nonempty R ha hm hb)
          hx.1.le hx.2
      have hdτ : HasDerivAt τ (-(frobenius (outwardState R x).1)^2) x := by
        have he : τ =ᶠ[𝓝 x] (fun y => Matrix.trace (outwardResolvent R.1 y)) := by
          filter_upwards [eventually_gt_nhds hx.1] with y hy
          exact congrArg Matrix.trace (outwardState_of_nonneg R hy.le)
        have hder := hasDerivAt_outwardTrace R.2 hx.1.le
        rw [← outwardState_of_nonneg R hx.1.le] at hder
        exact hder.congr_of_eventuallyEq he
      exact ((hasDerivAt_id x).add ((hd _ (hτ x hx.1.le) hbefore).comp x hdτ)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hbefore : b < mixedCost a h (outwardState R x) :=
        leastCorrection_before (f := fun ω => mixedCost a h (outwardState R ω)) (b := b)
          (mixedCost_outward_continuous R a hc).continuousOn
          (mixedCost_outward_antitone R ha hm h0) (mixedCost_outward_nonempty R ha hm hb)
          hx.1.le hx.2
      have := hk (outwardState R x) (hτ x hx.1.le) hbefore
      nlinarith
  have hh := hanti (show 0 ∈ Icc (0 : ℝ) c from ⟨le_rfl,hcn⟩)
    (show c ∈ Icc (0 : ℝ) c from ⟨hcn,le_rfl⟩) hcn
  have he : τ 0 = Matrix.trace R.1 := by simp [τ,outwardState,outwardResolvent_zero R.2]
  change c+B (τ c) ≤ 0+B (τ 0) at hh
  rw [he,zero_add] at hh
  dsimp [c,τ] at hh ⊢
  linarith

theorem mixed_process_outward_le_potential {a : ℝ} (ha : 0 ≤ a) {h : ℝ → ℝ}
    (hc : Continuous h) (hm : MonotoneOn h (Icc (0 : ℝ) 1))
    (h0 : ∀ k ∈ Icc (0 : ℝ) 1, 0 ≤ h k) {b : ℝ} (hb : 0 < b)
    (upper : Bool) (R₀ : PositiveResolvent ι) (x : ℕ → ι → ℝ) (m : ℕ)
    (B k : ℝ → ℝ) (hB : ContinuousOn B (Ioi 0))
    (hB0 : ∀ t, 0 < t → 0 ≤ B t)
    (hd : ∀ Q : PositiveResolvent ι, Matrix.trace Q.1 ≤ Matrix.trace R₀.1 →
      b < mixedCost a h Q → HasDerivAt B (k (Matrix.trace Q.1)) (Matrix.trace Q.1))
    (hk : ∀ Q : PositiveResolvent ι, Matrix.trace Q.1 ≤ Matrix.trace R₀.1 →
      b < mixedCost a h Q → 1 ≤ k (Matrix.trace Q.1) * (frobenius Q.1)^2) :
    ((mixedCorrectionRule ha hc hm h0 hb).process upper R₀ x m).outward ≤
      B (Matrix.trace R₀.1) := by
  let c := mixedCorrectionRule (ι := ι) ha hc hm h0 hb
  let q := c.traceChain upper R₀ x m
  have hτ (i : ℕ) (hi : i ≤ m) : Matrix.trace (q.R i) ≤ Matrix.trace R₀.1 := by
    simpa only [q,CorrectionRule.traceChain,CorrectionRule.process,BarrierState.R] using
      q.trace_antitone (show 0 ∈ Iic m by simp) (show i ∈ Iic m from hi) (Nat.zero_le i)
  have hstep (i : ℕ) (hi : i < m) : q.amount i ≤
      B (Matrix.trace (q.R i))-B (Matrix.trace (q.R (i+1))) := by
    rw [q.trace_next i hi]
    let R : PositiveResolvent ι := ⟨q.R i,q.positive i hi.le⟩
    have hs := mixedCorrection_le_potential R ha hc hm h0 hb B k hB
      (fun Q hQ => hd Q (hQ.trans (hτ i hi.le)))
      (fun Q hQ => hk Q (hQ.trans (hτ i hi.le)))
    change mixedCorrection a h b R ≤ B (Matrix.trace R.1) -
      B (Matrix.trace (outwardResolvent R.1 (mixedCorrection a h b R)))
    rw [← outwardState_of_nonneg R (mixedCorrection_spec R ha hc hm hb).1]
    exact hs
  have ht := q.total_le_potential B hstep
  have hn := hB0 _ (trace_pos (q.positive m le_rfl))
  rw [c.process_outward]
  change ∑ i ∈ Finset.range m,q.amount i ≤ _
  have he : Matrix.trace (q.R 0) = Matrix.trace R₀.1 := rfl
  rw [he] at ht
  linarith

end
end SingularValueBounds.KL
