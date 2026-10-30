import SingularValueBounds.KL.Barrier.MixedPotential
import SingularValueBounds.KL.Barrier.MixedScalarCap
import SingularValueBounds.KL.Barrier.MixedInitialization
import SingularValueBounds.KL.Barrier.MixedAngular
import SingularValueBounds.KL.Barrier.MixedInverseIntegral
import SingularValueBounds.KL.Barrier.MixedCostIntegral

/-! # The pathwise mixed-profile budget -/
open Set Filter MeasureTheory
open scoped BigOperators Matrix Topology
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem mixed_process_outward_le_inverse_potential {a : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hc : Continuous h) (hm : MonotoneOn h (Icc (0 : ℝ) 1))
    (h0 : ∀ k ∈ Icc (0 : ℝ) 1, 0 ≤ h k)
    (hp : ∀ k ∈ Ioc (0 : ℝ) 1, 0 < h k) {b : ℝ} (hb : 0 < b)
    (upper : Bool) (R₀ : PositiveResolvent ι) (x : ℕ → ι → ℝ) (m : ℕ)
    (htrace : Matrix.trace R₀.1 = b /
      mixedScalarCap (Fintype.card ι) a h (1/Real.sqrt (Fintype.card ι))) :
    let l := 1/Real.sqrt (Fintype.card ι)
    let g := mixedScalarCap (Fintype.card ι) a h
    let hl := (mixedInitialShape_mem (Fintype.card_pos (α := ι))).2
    let j := mixedInverse g l hl (mixedScalarCap_continuous Fintype.card_pos a hc)
      (mixedScalarCap_strictMono Fintype.card_pos a hm hp)
    ((mixedCorrectionRule ha hc hm h0 hb).process upper R₀ x m).outward ≤
      mixedTracePotential b (g 1) j (Matrix.trace R₀.1) := by
  intro l g hl j
  have hl0 : 0 < l := (mixedInitialShape_mem (Fintype.card_pos (α := ι))).1
  have hgc : ContinuousOn g (Icc l 1) := mixedScalarCap_continuous Fintype.card_pos a hc
  have hgm : StrictMonoOn g (Icc l 1) := mixedScalarCap_strictMono Fintype.card_pos a hm hp
  have hjc : Continuous j := continuous_mixedInverse g l hl hgc hgm
  have hjmem (c : ℝ) : j c ∈ Icc l 1 := mixedInverse_mem g l hl hgc hgm c
  have hjpos (c : ℝ) : 0 < j c := hl0.trans_le (hjmem c).1
  have hgl : 0 < g l := by
    dsimp [g,l]
    rw [mixedScalarCap_base Fintype.card_pos]
    exact add_pos_of_nonneg_of_pos ha
      (mul_pos hl0 (hp _ (mixedInitialShape_mem Fintype.card_pos)))
  let B := mixedTracePotential b (g 1) j
  let k := mixedTraceKernel b j
  have hactive (Q : PositiveResolvent ι) (hQ : Matrix.trace Q.1 ≤ Matrix.trace R₀.1)
      (hcap : b < mixedCost a h Q) :
      b/Matrix.trace Q.1 ∈ Icc (g l) (g 1) ∧
      b/Matrix.trace Q.1 < g 1 ∧
      j (b/Matrix.trace Q.1) ≤ frobenius Q.1/Matrix.trace Q.1 := by
    have hτ := trace_pos Q.2
    have hxr := frobenius_trace_ratio_bounds Q.2
    have hcQ := hcap.trans_le (mixedCost_le_scalarCap a hm Q)
    have hcx : b/Matrix.trace Q.1 < g (frobenius Q.1/Matrix.trace Q.1) :=
      (div_lt_iff₀ hτ).mpr (by simpa only [mul_comm] using hcQ)
    have hcle : b/Matrix.trace Q.1 < g 1 := hcx.trans_le
      (hgm.monotoneOn hxr ⟨hl,le_rfl⟩ hxr.2)
    have hclow : g l ≤ b/Matrix.trace Q.1 := by
      rw [htrace] at hQ
      apply (le_div_iff₀ hτ).mpr
      have ht := (le_div_iff₀ hgl).mp hQ
      simpa only [mul_comm] using ht
    exact ⟨⟨hclow,hcle.le⟩,hcle,
      (mixedInverse_le_iff hl hgc hgm ⟨hclow,hcle.le⟩ hxr).mpr hcx.le⟩
  apply mixed_process_outward_le_potential ha hc hm h0 hb upper R₀ x m B k
    (continuousOn_mixedTracePotential hjc (fun c => (hjpos c).ne'))
    (fun t _ => mixedTracePotential_nonneg hb j t)
  · intro Q hQ hcap
    exact hasDerivAt_mixedTracePotential hb hjc (fun c => (hjpos c).ne')
      (trace_pos Q.2) (hactive Q hQ hcap).2.1
  · intro Q hQ hcap
    have hτ := trace_pos Q.2
    have hjp := hjpos (b/Matrix.trace Q.1)
    have hF := (le_div_iff₀ hτ).mp (hactive Q hQ hcap).2.2
    have he : k (Matrix.trace Q.1)*(frobenius Q.1)^2 =
        (frobenius Q.1)^2/(Matrix.trace Q.1*j (b/Matrix.trace Q.1))^2 := by
      dsimp [k,mixedTraceKernel]
      simp only [div_eq_mul_inv,mul_pow,mul_inv_rev,inv_pow]
      ring
    rw [he,le_div_iff₀ (sq_pos_of_pos (mul_pos hτ hjp)),one_mul]
    nlinarith [frobenius_nonneg Q.1,mul_pos hτ hjp]

/-- The complete mixed-profile budget, including the scalar initial distance.
Every row sequence is allowed; row updates enter only through trace preservation.
-/
theorem mixed_process_total_cost {a : ℝ} (ha : 0 ≤ a)
    {h : ℝ → ℝ} (hc : Continuous h) (hm : MonotoneOn h (Icc (0 : ℝ) 1))
    (h0 : ∀ k ∈ Icc (0 : ℝ) 1, 0 ≤ h k)
    (hp : ∀ k ∈ Ioc (0 : ℝ) 1, 0 < h k)
    (hside : h 1 ≤ 2*(∫ k in (0 : ℝ)..1,h k)) {b : ℝ} (hb : 0 < b)
    (upper : Bool) (x : ℕ → ι → ℝ) (m : ℕ) :
    mixedInitialDistance (Fintype.card ι) a h b +
      ((mixedCorrectionRule ha hc hm h0 hb).process upper
        (scalarResolvent (mixedInitialDistance (Fintype.card ι) a h b)
          (mixedInitialDistance_pos Fintype.card_pos ha hp hb)) x m).outward ≤
      (a*(Fintype.card ι)+2*profileAngularCost h*Real.sqrt (Fintype.card ι))/b := by
  let n := Fintype.card ι
  let l := 1/Real.sqrt n
  let g := mixedScalarCap n a h
  have hn : 0 < n := Fintype.card_pos
  have hl0 : 0 < l := (mixedInitialShape_mem hn).1
  have hl : l ≤ 1 := (mixedInitialShape_mem hn).2
  have hgc : ContinuousOn g (Icc l 1) := mixedScalarCap_continuous hn a hc
  have hgm : StrictMonoOn g (Icc l 1) := mixedScalarCap_strictMono hn a hm hp
  let j := mixedInverse g l hl hgc hgm
  have hjc : Continuous j := continuous_mixedInverse g l hl hgc hgm
  have hjmem (c : ℝ) : j c ∈ Icc l 1 := mixedInverse_mem g l hl hgc hgm c
  have hgle : g l ≤ g 1 := hgm.monotoneOn ⟨le_rfl,hl⟩ ⟨hl,le_rfl⟩ hl
  have hgl : 0 < g l := by
    rw [show g l = a+l*h l from mixedScalarCap_base hn a h]
    exact add_pos_of_nonneg_of_pos ha (mul_pos hl0 (hp _ (mixedInitialShape_mem hn)))
  let u := mixedInitialDistance n a h b
  have hu : 0 < u := mixedInitialDistance_pos hn ha hp hb
  let R₀ := scalarResolvent (ι := ι) u hu
  have htrace : Matrix.trace R₀.1 = b/g l := by
    rw [show g l = a+l*h l from mixedScalarCap_base hn a h]
    exact mixed_scalar_initial_trace ha hp hb
  have hout := mixed_process_outward_le_inverse_potential ha hc hm h0 hp hb upper R₀ x m htrace
  change ((mixedCorrectionRule ha hc hm h0 hb).process upper R₀ x m).outward ≤
    mixedTracePotential b (g 1) j (Matrix.trace R₀.1) at hout
  rw [htrace,mixedTracePotential_at_initial hb.ne' hgl.ne' hgle] at hout
  have hyoung := mixed_inverse_integral_of_continuousOn hgc hjc.continuousOn hl0 hl
    (fun y hy => ⟨hgm.monotoneOn ⟨le_rfl,hl⟩ hy hy.1,
      hgm.monotoneOn hy ⟨hl,le_rfl⟩ hy.2⟩)
    (fun c _ => hjmem c)
    (fun c hc' y hy => mixedInverse_le_iff hl hgc hgm hc' hy)
  have heint : (∫ c in g l..g 1,(j c)⁻¹^2) =
      g 1-g l/l^2+(∫ y in l..1,2*g y/y^3) := by
    simpa only [one_div,inv_pow] using hyoung
  rw [heint] at hout
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hl2 : l^2 = (n : ℝ)⁻¹ := by
    dsimp [l]
    rw [div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    exact one_div (n : ℝ)
  have hinit : u*b = g l/l^2 := by
    have ht : (n : ℝ)/u = b/g l := by rw [← htrace]; exact (scalarResolvent_trace u hu).symm
    have he := (div_eq_div_iff hu.ne' hgl.ne').mp ht
    rw [hl2,div_inv_eq_mul]
    linarith
  have hcancel : u+(g 1-g l/l^2+(∫ y in l..1,2*g y/y^3))/b =
      (g 1+(∫ y in l..1,2*g y/y^3))/b := by
    apply (eq_div_iff hb.ne').mpr
    rw [add_mul,div_mul_cancel₀ _ hb.ne',hinit]
    ring
  have hdimension := mixedScalarCap_integral_le hn a hc hm hside
  have hfinal : (g 1+(∫ y in l..1,2*g y/y^3))/b ≤
      (a*n+2*profileAngularCost h*Real.sqrt n)/b := by
    apply div_le_div_of_nonneg_right _ hb.le
    simpa only [mul_comm (Real.sqrt (n : ℝ)) (profileAngularCost h),mul_assoc] using hdimension
  change u+((mixedCorrectionRule ha hc hm h0 hb).process upper R₀ x m).outward ≤ _
  calc
    _ ≤ u+(g 1-g l/l^2+(∫ y in l..1,2*g y/y^3))/b := add_le_add_right hout u
    _ = _ := hcancel
    _ ≤ _ := hfinal

end
end SingularValueBounds.KL
