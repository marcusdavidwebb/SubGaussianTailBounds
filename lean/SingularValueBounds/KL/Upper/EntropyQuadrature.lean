import SingularValueBounds.KL.Weighted.EntropyIntegration
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Entropy tail integrability, interval splitting and convex interpolation.
The analytic exponential primitives provide the interval bounds directly. -/

open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

/-- The increasing factor in the entropy tail integral. -/
def entropyKernel (c u : ℝ) : ℝ := 1 + Real.log (u/c)

theorem entropyKernel_nonneg {c u : ℝ} (hc : 0 < c) (hu : c ≤ u) :
    0 ≤ entropyKernel c u := by
  have h := Real.log_nonneg ((one_le_div hc).2 hu)
  dsimp [entropyKernel]
  linarith

/-- Exponential domination makes the entropy integrand integrable, including
all finite subintervals and the infinite tail. -/
theorem entropy_tail_integrable {c C r : ℝ} {T : ℝ → ℝ}
    (hc : 0 < c) (hr : 0 < r)
    (hTm : Measurable T) (hT0 : ∀ u, 0 ≤ T u)
    (htail : ∀ u, c < u → T u ≤ C*Real.exp (-(r*u))) :
    IntegrableOn (fun u => entropyKernel c u*T u) (Ioi c) := by
  have hi (n : ℕ) : IntegrableOn (fun u : ℝ => u^n*Real.exp (-(r*u))) (Ioi c) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (n : ℝ)) (p := 1) (b := r)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hr
    have h0 : IntegrableOn (fun u : ℝ => u^n*Real.exp (-(r*u))) (Ioi 0) := by
      simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using h
    exact h0.mono_set (Ioi_subset_Ioi hc.le)
  have hdom := ((hi 0).const_mul C).add ((hi 1).const_mul (C/c))
  apply hdom.mono'
  · apply Measurable.aestronglyMeasurable
    exact ((Real.measurable_log.comp (measurable_id.div_const c)).const_add 1).mul hTm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : c < u := hu
    have huPos : 0 < u := hc.trans hu0
    have hku := entropyKernel_nonneg hc hu0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hku (hT0 u))]
    have hlog := Real.log_le_sub_one_of_pos (div_pos (hc.trans hu0) hc)
    have hk : entropyKernel c u ≤ 1+u/c := by dsimp [entropyKernel]; linarith
    have hh := mul_le_mul hk (htail u hu0) (hT0 u)
      (show 0 ≤ 1+u/c by positivity)
    simp only [Pi.add_apply,pow_zero,pow_one,one_mul]
    convert! hh using 1 <;> ring

/-- Split the infinite entropy integral into the finite interval and its tail. -/
theorem entropy_integral_split {c H : ℝ} {f : ℝ → ℝ} (hcH : c ≤ H)
    (hi : IntegrableOn f (Ioi c)) :
    (∫ u in Ioi c, f u) = (∫ u in c..H, f u) + ∫ u in Ioi H, f u := by
  rw [intervalIntegral.integral_of_le hcH]
  have hUnion : Ioc c H ∪ Ioi H = Ioi c := by
    ext u
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h|h); exact h.1; exact hcH.trans_lt h
    · intro h
      by_cases hu : u ≤ H
      · exact Or.inl ⟨h,hu⟩
      · exact Or.inr (lt_of_not_ge hu)
  have hdis : Disjoint (Ioc c H) (Ioi H) := by
    rw [Set.disjoint_left]
    intro u hu hv
    exact (not_lt_of_ge hu.2) hv
  rw [← hUnion, setIntegral_union hdis measurableSet_Ioi
    (hi.mono_set (fun u hu => hu.1)) (hi.mono_set (Ioi_subset_Ioi hcH))]

/-- A separately convex function is below its four-corner interpolation.
This rule applies to the entropy majorant once its prefactors have been
proved separately convex. -/
theorem separately_convex_corner_bound {F : ℝ → ℝ → ℝ} {al ah kl kh a k : ℝ}
    (ha : a ∈ Icc al ah) (hk : k ∈ Icc kl kh)
    (hA : ∀ y ∈ Icc kl kh, ConvexOn ℝ (Icc al ah) (fun x => F x y))
    (hK : ∀ x ∈ Icc al ah, ConvexOn ℝ (Icc kl kh) (fun y => F x y))
    (ha' : al < ah) (hk' : kl < kh) :
    F a k ≤
      ((ah-a)/(ah-al))*((kh-k)/(kh-kl))*F al kl +
      ((a-al)/(ah-al))*((kh-k)/(kh-kl))*F ah kl +
      ((ah-a)/(ah-al))*((k-kl)/(kh-kl))*F al kh +
      ((a-al)/(ah-al))*((k-kl)/(kh-kl))*F ah kh := by
  let s := (ah-a)/(ah-al)
  let t := (a-al)/(ah-al)
  let u := (kh-k)/(kh-kl)
  let v := (k-kl)/(kh-kl)
  have hs : 0 ≤ s := div_nonneg (by linarith [ha.2]) (by linarith)
  have ht : 0 ≤ t := div_nonneg (by linarith [ha.1]) (by linarith)
  have hu : 0 ≤ u := div_nonneg (by linarith [hk.2]) (by linarith)
  have hv : 0 ≤ v := div_nonneg (by linarith [hk.1]) (by linarith)
  have had : ah-al ≠ 0 := ne_of_gt (sub_pos.mpr ha')
  have hkd : kh-kl ≠ 0 := ne_of_gt (sub_pos.mpr hk')
  have hst : s+t=1 := by dsimp [s,t]; field_simp [had] <;> ring
  have huv : u+v=1 := by dsimp [u,v]; field_simp [hkd] <;> ring
  have hea : s*al+t*ah=a := by dsimp [s,t]; field_simp [had] <;> ring
  have hek : u*kl+v*kh=k := by dsimp [u,v]; field_simp [hkd] <;> ring
  have h1 := (hA k hk).2 (show al ∈ Icc al ah by exact ⟨le_rfl,ha'.le⟩)
    (show ah ∈ Icc al ah by exact ⟨ha'.le,le_rfl⟩) hs ht hst
  have h2 := (hK al ⟨le_rfl,ha'.le⟩).2 (show kl ∈ Icc kl kh by exact ⟨le_rfl,hk'.le⟩)
    (show kh ∈ Icc kl kh by exact ⟨hk'.le,le_rfl⟩) hu hv huv
  have h3 := (hK ah ⟨ha'.le,le_rfl⟩).2 (show kl ∈ Icc kl kh by exact ⟨le_rfl,hk'.le⟩)
    (show kh ∈ Icc kl kh by exact ⟨hk'.le,le_rfl⟩) hu hv huv
  simp only [smul_eq_mul,hea,hek] at h1 h2 h3
  have hh := h1.trans (add_le_add (mul_le_mul_of_nonneg_left h2 hs)
    (mul_le_mul_of_nonneg_left h3 ht))
  dsimp [s,t,u,v] at hh
  convert! hh using 1 <;> ring

end
end SingularValueBounds.KL
