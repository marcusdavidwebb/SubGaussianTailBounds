import SingularValueBounds.KL.Barrier.Norms

/-! # Continuous outward corrections
The least correction is selected from a closed upper level set. All
measurability statements concern the actual inverse matrix; no measurable
choice of eigenvectors is made. -/
open Set Filter MeasureTheory
open scoped BigOperators Matrix Topology
namespace SingularValueBounds.KL
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def outwardResolvent (R : Matrix ι ι ℝ) (ω : ℝ) : Matrix ι ι ℝ :=
  (R⁻¹ + ω • (1 : Matrix ι ι ℝ))⁻¹

def outwardBase (R : Matrix ι ι ℝ) (hR : R.PosDef) : SymmetricMatrix ι :=
  ⟨-R⁻¹, hR.inv.isHermitian.neg⟩

lemma outwardBase_gap (R : Matrix ι ι ℝ) (hR : R.PosDef) (ω : ℝ) :
    (outwardBase R hR).gap ω = R⁻¹ + ω • (1 : Matrix ι ι ℝ) := by
  simp [outwardBase, SymmetricMatrix.gap, add_comm]

lemma outwardBase_above {R : Matrix ι ι ℝ} (hR : R.PosDef) {ω : ℝ} (hω : 0 ≤ ω) :
    ω ∈ aboveSpectrum (outwardBase R hR).2.eigenvalues := by
  have h0 : ((outwardBase R hR).gap 0).PosDef := by
    simpa only [outwardBase_gap, zero_smul, add_zero] using hR.inv
  exact fun i => ((outwardBase R hR).gap_posDef_iff 0).mp h0 i |>.trans_le hω

lemma outwardGap_posDef {R : Matrix ι ι ℝ} (hR : R.PosDef) {ω : ℝ} (hω : 0 ≤ ω) :
    (R⁻¹ + ω • (1 : Matrix ι ι ℝ)).PosDef := by
  rw [← outwardBase_gap R hR]
  exact ((outwardBase R hR).gap_posDef_iff ω).mpr (outwardBase_above hR hω)

lemma outwardResolvent_posDef {R : Matrix ι ι ℝ} (hR : R.PosDef) {ω : ℝ} (hω : 0 ≤ ω) :
    (outwardResolvent R ω).PosDef := (outwardGap_posDef hR hω).inv

@[simp] lemma outwardResolvent_zero {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    outwardResolvent R 0 = R := by
  simp only [outwardResolvent, zero_smul, add_zero]
  exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit)

lemma outward_powerTrace {R : Matrix ι ι ℝ} (hR : R.PosDef) {ω : ℝ}
    (hω : 0 ≤ ω) (p : ℕ) :
    Matrix.trace (outwardResolvent R ω ^ p) =
      reciprocalTrace (outwardBase R hR).2.eigenvalues p ω := by
  have hg := ((outwardBase R hR).gap_posDef_iff ω).mpr (outwardBase_above hR hω)
  simpa only [SymmetricMatrix.resolvent, outwardBase_gap, outwardResolvent] using
    (outwardBase R hR).resolvent_powerTrace hg p

lemma outward_trace {R : Matrix ι ι ℝ} (hR : R.PosDef) {ω : ℝ} (hω : 0 ≤ ω) :
    Matrix.trace (outwardResolvent R ω) =
      reciprocalTrace (outwardBase R hR).2.eigenvalues 1 ω := by
  simpa only [pow_one] using outward_powerTrace hR hω 1

lemma outward_frobenius {R : Matrix ι ι ℝ} (hR : R.PosDef) {ω : ℝ} (hω : 0 ≤ ω) :
    frobenius (outwardResolvent R ω) =
      Real.sqrt (reciprocalTrace (outwardBase R hR).2.eigenvalues 2 ω) := by
  rw [frobenius_eq_sqrt_trace_square (outwardResolvent_posDef hR hω).isHermitian,
    outward_powerTrace hR hω]

theorem outward_trace_strictAnti {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    StrictAntiOn (fun ω => Matrix.trace (outwardResolvent R ω)) (Ici 0) := by
  intro a ha b hb hab
  change Matrix.trace (outwardResolvent R b) < Matrix.trace (outwardResolvent R a)
  rw [outward_trace hR ha, outward_trace hR hb]
  exact reciprocalTrace_strictAnti _ (by decide : 1 ≠ 0)
    (outwardBase_above hR ha) (outwardBase_above hR hb) hab

lemma continuousOn_outwardResolvent {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    ContinuousOn (outwardResolvent R) (Ici 0) := by
  intro ω hω
  have hinv : ContinuousAt Inv.inv (R⁻¹ + ω • (1 : Matrix ι ι ℝ)) := by
    apply continuousAt_matrix_inv
    have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [heq]
    exact continuousAt_inv₀ (outwardGap_posDef hR hω).det_pos.ne'
  exact (hinv.comp (f := fun x : ℝ => R⁻¹ + x • (1 : Matrix ι ι ℝ))
    (show ContinuousAt (fun x : ℝ => R⁻¹ + x • (1 : Matrix ι ι ℝ)) ω by
      fun_prop)).continuousWithinAt

lemma continuous_frobenius : Continuous (frobenius (ι := ι)) := by
  unfold frobenius
  fun_prop

lemma measurable_outwardResolvent :
    Measurable (fun q : Matrix ι ι ℝ × ℝ => outwardResolvent q.1 q.2) :=
  measurable_matrix_inverse.comp ((measurable_matrix_inverse.comp measurable_fst).add
    (measurable_snd.smul measurable_const))

theorem hasDerivAt_outwardTrace {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {ω : ℝ} (hω : 0 ≤ ω) :
    HasDerivAt (fun x => Matrix.trace (outwardResolvent R x))
      (-(frobenius (outwardResolvent R ω))^2) ω := by
  let H := outwardBase R hR
  have ha := outwardBase_above hR hω
  have he : ∀ᶠ x : ℝ in 𝓝 ω, ∀ i, H.2.eigenvalues i < x := by
    have hopen : IsOpen (aboveSpectrum H.2.eigenvalues) := by
      have heq : aboveSpectrum H.2.eigenvalues = ⋂ i, Ioi (H.2.eigenvalues i) := by
        ext x; simp [aboveSpectrum]
      rw [heq]
      exact isOpen_iInter_of_finite (fun i => isOpen_Ioi)
    exact hopen.mem_nhds ha
  have heq : (fun x => Matrix.trace (outwardResolvent R x)) =ᶠ[𝓝 ω]
      reciprocalTrace H.2.eigenvalues 1 := by
    filter_upwards [he] with x hx
    have hg := (H.gap_posDef_iff x).mpr hx
    simpa only [H, SymmetricMatrix.resolvent, outwardBase_gap, outwardResolvent, pow_one] using
      H.resolvent_powerTrace hg 1
  have hd : HasDerivAt (reciprocalTrace H.2.eigenvalues 1)
      (-reciprocalTrace H.2.eigenvalues 2 ω) ω := by
    have ht (i : ι) : HasDerivAt (fun x : ℝ => (x - H.2.eigenvalues i)⁻¹)
        (-((ω - H.2.eigenvalues i)⁻¹)^2) ω := by
      convert! ((hasDerivAt_id ω).sub_const (H.2.eigenvalues i)).inv
        (sub_pos.mpr (ha i)).ne' using 1 <;> (try simp) <;> ring
    unfold reciprocalTrace
    simpa only [pow_one, Finset.sum_neg_distrib, Finset.sum_fn] using!
      HasDerivAt.sum (u := Finset.univ) (fun i _ => ht i)
  have hf : (frobenius (outwardResolvent R ω))^2 = reciprocalTrace H.2.eigenvalues 2 ω := by
    rw [outward_frobenius hR hω]
    exact Real.sq_sqrt (reciprocalTrace_pos _ 2 ha).le
  rw [hf]
  exact hd.congr_of_eventuallyEq heq

def leastCorrection (f : ℝ → ℝ) (b : ℝ) : ℝ := sInf {x : ℝ | 0 ≤ x ∧ f x ≤ b}

lemma leastCorrection_mem {f : ℝ → ℝ} {b : ℝ}
    (hc : ContinuousOn f (Ici 0)) (hne : ∃ x, 0 ≤ x ∧ f x ≤ b) :
    0 ≤ leastCorrection f b ∧ f (leastCorrection f b) ≤ b := by
  have hclosed : IsClosed {x : ℝ | 0 ≤ x ∧ f x ≤ b} := by
    have := hc.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_Iic : IsClosed (Iic b))
    simpa only [Set.preimage, Set.mem_Iic, Set.setOf_and] using! this
  exact hclosed.csInf_mem hne ⟨0, fun x hx => hx.1⟩

lemma leastCorrection_le_iff {f : ℝ → ℝ} {b x : ℝ}
    (hc : ContinuousOn f (Ici 0)) (ha : AntitoneOn f (Ici 0))
    (hne : ∃ y, 0 ≤ y ∧ f y ≤ b) :
    leastCorrection f b ≤ x ↔ 0 ≤ x ∧ f x ≤ b := by
  have hm := leastCorrection_mem hc hne
  constructor
  · intro hx
    exact ⟨hm.1.trans hx, (ha hm.1 (hm.1.trans hx) hx).trans hm.2⟩
  · intro hx
    exact csInf_le ⟨0, fun y hy => hy.1⟩ hx

lemma leastCorrection_before {f : ℝ → ℝ} {b x : ℝ}
    (hc : ContinuousOn f (Ici 0)) (ha : AntitoneOn f (Ici 0))
    (hne : ∃ y, 0 ≤ y ∧ f y ≤ b) (hx : 0 ≤ x) (hxc : x < leastCorrection f b) :
    b < f x := by
  exact lt_of_not_ge (fun h => (not_le_of_gt hxc)
    ((leastCorrection_le_iff hc ha hne).mpr ⟨hx, h⟩))

lemma constantCost_continuous {R : Matrix ι ι ℝ} (hR : R.PosDef) (K w : ℝ) :
    ContinuousOn (fun x => regularityCost K w (outwardResolvent R x)) (Ici 0) := by
  unfold regularityCost
  exact ((continuousOn_const.mul ((show Continuous (fun M : Matrix ι ι ℝ => Matrix.trace M) by fun_prop).comp_continuousOn
      (continuousOn_outwardResolvent hR))).add
    (continuousOn_const.mul (continuous_frobenius.comp_continuousOn
      (continuousOn_outwardResolvent hR))))

lemma constantCost_antitone {R : Matrix ι ι ℝ} (hR : R.PosDef) (K : ℝ)
    {w : ℝ} (hw : 0 ≤ w) :
    AntitoneOn (fun x => regularityCost K w (outwardResolvent R x)) (Ici 0) := by
  intro x hx y hy hxy
  have ht := (outward_trace_strictAnti hR).antitoneOn hx hy hxy
  have hs := (reciprocalTrace_strictAnti (outwardBase R hR).2.eigenvalues
    (by decide : 2 ≠ 0)).antitoneOn (outwardBase_above hR hx) (outwardBase_above hR hy) hxy
  have hf : frobenius (outwardResolvent R y) ≤ frobenius (outwardResolvent R x) := by
    rw [outward_frobenius hR hx, outward_frobenius hR hy]
    exact Real.sqrt_le_sqrt hs
  exact add_le_add (mul_le_mul_of_nonneg_left ht (sq_nonneg K))
    (mul_le_mul_of_nonneg_left hf hw)

lemma constantCost_tendsto {R : Matrix ι ι ℝ} (hR : R.PosDef) (K w : ℝ) :
    Tendsto (fun x => regularityCost K w (outwardResolvent R x)) atTop (𝓝 0) := by
  have he : (fun x => regularityCost K w (outwardResolvent R x)) =ᶠ[atTop]
      (fun x => K^2 * reciprocalTrace (outwardBase R hR).2.eigenvalues 1 x +
        w * Real.sqrt (reciprocalTrace (outwardBase R hR).2.eigenvalues 2 x)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [regularityCost, outward_trace hR hx, outward_frobenius hR hx]
  apply Filter.Tendsto.congr' he.symm
  simpa only [mul_zero, Real.sqrt_zero, add_zero] using!
    ((tendsto_const_nhds.mul (reciprocalTrace_tendsto (outwardBase R hR).2.eigenvalues
      (by decide : 1 ≠ 0))).add (tendsto_const_nhds.mul
        (Real.continuous_sqrt.continuousAt.tendsto.comp
          (reciprocalTrace_tendsto (outwardBase R hR).2.eigenvalues (by decide : 2 ≠ 0)))))

lemma constantCost_nonempty {R : Matrix ι ι ℝ} (hR : R.PosDef) (K w : ℝ)
    {b : ℝ} (hb : 0 < b) :
    ∃ x, 0 ≤ x ∧ regularityCost K w (outwardResolvent R x) ≤ b := by
  obtain ⟨x, hx, hcost⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((constantCost_tendsto hR K w).eventually_lt_const hb)).exists
  exact ⟨x, hx, hcost.le⟩

def constantCorrection (K w b : ℝ) (R : Matrix ι ι ℝ) : ℝ :=
  leastCorrection (fun x => regularityCost K w (outwardResolvent R x)) b

theorem constantCorrection_spec {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (K : ℝ) {w b : ℝ} (_hw : 0 ≤ w) (hb : 0 < b) :
    0 ≤ constantCorrection K w b R ∧
      regularityCost K w (outwardResolvent R (constantCorrection K w b R)) ≤ b :=
  leastCorrection_mem (constantCost_continuous hR K w) (constantCost_nonempty hR K w hb)

theorem constantCorrection_le_iff {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (K : ℝ) {w b x : ℝ} (hw : 0 ≤ w) (hb : 0 < b) :
    constantCorrection K w b R ≤ x ↔
      0 ≤ x ∧ regularityCost K w (outwardResolvent R x) ≤ b :=
  leastCorrection_le_iff (constantCost_continuous hR K w) (constantCost_antitone hR K hw)
    (constantCost_nonempty hR K w hb)

set_option maxHeartbeats 800000 in
theorem measurable_constantCorrection (K : ℝ) {w b : ℝ} (hw : 0 ≤ w) (hb : 0 < b) :
    Measurable (fun R : {R : Matrix ι ι ℝ // R.PosDef} => constantCorrection K w b R.1) := by
  apply measurable_of_Iic
  intro x
  have hc : Measurable (fun R : {R : Matrix ι ι ℝ // R.PosDef} =>
      regularityCost K w (outwardResolvent R.1 x)) := by
    have ho : Measurable (fun R : {R : Matrix ι ι ℝ // R.PosDef} => outwardResolvent R.1 x) := by
      change Measurable (fun R : {R : Matrix ι ι ℝ // R.PosDef} => (R.1⁻¹ + x • (1 : Matrix ι ι ℝ))⁻¹)
      apply measurable_matrix_inverse.comp
      exact (measurable_matrix_inverse.comp measurable_subtype_coe).add measurable_const
    exact (measurable_const.mul ((show Continuous (fun M : Matrix ι ι ℝ => Matrix.trace M) by
      fun_prop).measurable.comp ho)).add (measurable_const.mul (continuous_frobenius.measurable.comp ho))
  have heq : (fun R : {R : Matrix ι ι ℝ // R.PosDef} => constantCorrection K w b R.1) ⁻¹' Iic x =
      {R | 0 ≤ x ∧ regularityCost K w (outwardResolvent R.1 x) ≤ b} := by
    ext R
    exact constantCorrection_le_iff R.2 K hw hb
  rw [heq]
  by_cases hx : 0 ≤ x
  · simpa only [hx, true_and] using measurableSet_le hc measurable_const
  · simp only [hx, false_and, Set.setOf_false, MeasurableSet.empty]

end
end SingularValueBounds.KL
