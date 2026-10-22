import SingularValueBounds.KL.Barrier.MixedGeometry

/-! # The measurable mixed-profile correction rule -/
open Set Filter MeasureTheory
open scoped BigOperators Matrix Topology
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

instance positiveResolventBorelSpace : BorelSpace (PositiveResolvent ι) :=
  inferInstanceAs (BorelSpace ({R : Matrix ι ι ℝ | R.PosDef} : Set (Matrix ι ι ℝ)))

lemma continuous_outwardState (R : PositiveResolvent ι) : Continuous (outwardState R) := by
  apply Continuous.subtype_mk
  exact (continuousOn_outwardResolvent R.2).comp_continuous
    (continuous_id.max continuous_const) (fun ω => (show max ω 0 ∈ Ici (0 : ℝ) from le_max_right ω 0))

lemma measurable_outwardState :
    Measurable (fun z : PositiveResolvent ι × ℝ => outwardState z.1 z.2) := by
  apply Measurable.subtype_mk
  exact Measurable.comp
    (f := fun z : PositiveResolvent ι × ℝ => (z.1.1,max z.2 0))
    (g := fun z : Matrix ι ι ℝ × ℝ => outwardResolvent z.1 z.2)
    (measurable_outwardResolvent (ι := ι))
    ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_snd.max measurable_const))

lemma mixedCost_outward_continuous (R : PositiveResolvent ι) (a : ℝ)
    {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (fun ω => mixedCost a h (outwardState R ω)) :=
  (continuous_mixedCost a hh).comp (continuous_outwardState R)

lemma outward_frobenius_antitone (R : PositiveResolvent ι) :
    AntitoneOn (fun ω => frobenius (outwardState R ω).1) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  dsimp only
  rw [outwardState_of_nonneg R hx, outwardState_of_nonneg R hy,
    outward_frobenius R.2 hx, outward_frobenius R.2 hy]
  exact Real.sqrt_le_sqrt ((reciprocalTrace_strictAnti (outwardBase R.1 R.2).2.eigenvalues
    (by decide : 2 ≠ 0)).antitoneOn (outwardBase_above R.2 hx) (outwardBase_above R.2 hy) hxy)

theorem mixedCost_outward_antitone (R : PositiveResolvent ι) {a : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hh0 : ∀ k ∈ Icc (0 : ℝ) 1, 0 ≤ h k) :
    AntitoneOn (fun ω => mixedCost a h (outwardState R ω)) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hsx := spectralRatio_pos_le_one (outwardState R x).2
  have hsy := spectralRatio_pos_le_one (outwardState R y).2
  have hshape := hh ⟨hsy.1.le,hsy.2⟩ ⟨hsx.1.le,hsx.2⟩
    (outward_spectralRatio_antitone R hx hy hxy)
  have hf := outward_frobenius_antitone R hx hy hxy
  have ht : Matrix.trace (outwardState R y).1 ≤ Matrix.trace (outwardState R x).1 := by
    rw [outwardState_of_nonneg R hx, outwardState_of_nonneg R hy]
    exact (outward_trace_strictAnti R.2).antitoneOn hx hy hxy
  exact add_le_add (mul_le_mul_of_nonneg_left ht ha)
    (mul_le_mul hf hshape (hh0 _ ⟨hsy.1.le,hsy.2⟩) (frobenius_nonneg _))

lemma mixedCost_le_constant (R : PositiveResolvent ι) {a : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hh : MonotoneOn h (Icc (0 : ℝ) 1)) :
    mixedCost a h R ≤ regularityCost (Real.sqrt a) (h 1) R.1 := by
  have hs := spectralRatio_pos_le_one R.2
  have he := hh ⟨hs.1.le,hs.2⟩ ⟨by norm_num,le_rfl⟩ hs.2
  simpa only [mixedCost,regularityCost,Real.sq_sqrt ha,mul_comm (h 1)] using
    add_le_add_left (mul_le_mul_of_nonneg_left he (frobenius_nonneg R.1)) (a*Matrix.trace R.1)

lemma mixedCost_outward_nonempty (R : PositiveResolvent ι) {a : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hh : MonotoneOn h (Icc (0 : ℝ) 1)) {b : ℝ} (hb : 0 < b) :
    ∃ ω, 0 ≤ ω ∧ mixedCost a h (outwardState R ω) ≤ b := by
  obtain ⟨ω,hω,hcap⟩ := constantCost_nonempty R.2 (Real.sqrt a) (h 1) hb
  refine ⟨ω,hω,(mixedCost_le_constant (outwardState R ω) ha hh).trans ?_⟩
  rwa [outwardState_of_nonneg R hω]

def mixedCorrection (a : ℝ) (h : ℝ → ℝ) (b : ℝ) (R : PositiveResolvent ι) : ℝ :=
  leastCorrection (fun ω => mixedCost a h (outwardState R ω)) b

theorem mixedCorrection_spec (R : PositiveResolvent ι) {a : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hc : Continuous h) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    {b : ℝ} (hb : 0 < b) :
    0 ≤ mixedCorrection a h b R ∧
      mixedCost a h (outwardState R (mixedCorrection a h b R)) ≤ b :=
  leastCorrection_mem (mixedCost_outward_continuous R a hc).continuousOn
    (mixedCost_outward_nonempty R ha hh hb)

theorem mixedCorrection_le_iff (R : PositiveResolvent ι) {a : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hc : Continuous h) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hh0 : ∀ k ∈ Icc (0 : ℝ) 1, 0 ≤ h k) {b x : ℝ} (hb : 0 < b) :
    mixedCorrection a h b R ≤ x ↔ 0 ≤ x ∧ mixedCost a h (outwardState R x) ≤ b :=
  leastCorrection_le_iff (mixedCost_outward_continuous R a hc).continuousOn
    (mixedCost_outward_antitone R ha hh hh0) (mixedCost_outward_nonempty R ha hh hb)

theorem measurable_mixedCorrection {a : ℝ} (ha : 0 ≤ a) {h : ℝ → ℝ}
    (hc : Continuous h) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hh0 : ∀ k ∈ Icc (0 : ℝ) 1, 0 ≤ h k) {b : ℝ} (hb : 0 < b) :
    Measurable (mixedCorrection (ι := ι) a h b) := by
  apply measurable_of_Iic
  intro x
  have hm : Measurable (fun R : PositiveResolvent ι => mixedCost a h (outwardState R x)) :=
    Measurable.comp (f := fun R : PositiveResolvent ι => outwardState R x)
      (g := mixedCost (ι := ι) a h) (continuous_mixedCost (ι := ι) a hc).measurable
      (Measurable.comp (f := fun R : PositiveResolvent ι => (R,x))
        (g := fun z : PositiveResolvent ι × ℝ => outwardState z.1 z.2)
        (measurable_outwardState (ι := ι)) (measurable_id.prodMk measurable_const))
  have he : mixedCorrection (ι := ι) a h b ⁻¹' Iic x =
      {R | 0 ≤ x ∧ mixedCost a h (outwardState R x) ≤ b} := by
    ext R
    exact mixedCorrection_le_iff R ha hc hh hh0 hb
  rw [he]
  by_cases hx : 0 ≤ x
  · simpa only [hx,true_and] using measurableSet_le hm measurable_const
  · simp only [hx,false_and,Set.setOf_false,MeasurableSet.empty]

def mixedCorrectionRule {a : ℝ} (ha : 0 ≤ a) {h : ℝ → ℝ}
    (hc : Continuous h) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hh0 : ∀ k ∈ Icc (0 : ℝ) 1, 0 ≤ h k) {b : ℝ} (hb : 0 < b) : CorrectionRule ι where
  amount R := mixedCorrection a h b R
  measurable := measurable_mixedCorrection ha hc hh hh0 hb
  nonneg R := (mixedCorrection_spec R ha hc hh hb).1

lemma mixedCorrectionRule_cap {a : ℝ} (ha : 0 ≤ a) {h : ℝ → ℝ}
    (hc : Continuous h) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hh0 : ∀ k ∈ Icc (0 : ℝ) 1, 0 ≤ h k) {b : ℝ} (hb : 0 < b)
    (R : PositiveResolvent ι) :
    mixedCost a h ((mixedCorrectionRule ha hc hh hh0 hb).prepared R) ≤ b := by
  have hs := mixedCorrection_spec R ha hc hh hb
  have he : (mixedCorrectionRule ha hc hh hh0 hb).prepared R =
      outwardState R (mixedCorrection a h b R) := by
    apply Subtype.ext
    exact (outwardState_of_nonneg R hs.1).symm
  rw [he]
  exact hs.2

end
end SingularValueBounds.KL
