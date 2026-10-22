import SingularValueBounds.KL.Weighted.EntropyIntegration
import SingularValueBounds.KL.Upper.TailMoments
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Entropy quadrature (supplementary S1.6.3)

Analytic interpretation of the upper integration sums in
`eq:app-up-entropy-integration` and `eq:k1-entropy-remainder`.
The endpoints and bounds may be rational certificate data; no numerical
integration assertion is assumed.
-/

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

theorem entropyKernel_mono {c u v : ℝ} (hc : 0 < c) (hu : 0 < u) (huv : u ≤ v) :
    entropyKernel c u ≤ entropyKernel c v := by
  exact add_le_add_left (Real.log_le_log (div_pos hu hc)
    (div_le_div_of_nonneg_right huv hc.le)) 1

/-- A single upper Riemann rectangle uses the left survival value and right
entropy factor. It also permits the minimum of several certified tails. -/
theorem entropy_quadrature_cell {c l r B : ℝ} {T : ℝ → ℝ}
    (hc : 0 < c) (hcl : c ≤ l) (hlr : l ≤ r)
    (hT : Antitone T) (hT0 : ∀ u, 0 ≤ T u) (hB : T l ≤ B)
    (hi : IntervalIntegrable (fun u => entropyKernel c u * T u) volume l r) :
    (∫ u in l..r, entropyKernel c u * T u) ≤
      (r-l)*entropyKernel c r*B := by
  have hbound : ∀ u ∈ Icc l r,
      entropyKernel c u*T u ≤ entropyKernel c r*B := by
    intro u hu
    have hcu : c ≤ u := hcl.trans hu.1
    have hk := entropyKernel_mono hc (lt_of_lt_of_le hc hcu) hu.2
    exact mul_le_mul hk ((hT hu.1).trans hB) (hT0 u)
      (entropyKernel_nonneg hc (hcl.trans hlr))
  have h := intervalIntegral.integral_mono_on hlr hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => entropyKernel c r*B) volume l r)
    hbound
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_assoc, mul_comm,
    mul_left_comm] using h

/-- Full finite-mesh Riemann bound, with arbitrary increasing mesh. -/
theorem entropy_quadrature_sum {c : ℝ} {x B : ℕ → ℝ} {T : ℝ → ℝ} {m n : ℕ}
    (hc : 0 < c) (hmn : m ≤ n)
    (hx : Monotone x) (hcl : c ≤ x m)
    (hT : Antitone T) (hT0 : ∀ u, 0 ≤ T u)
    (hB : ∀ j ∈ Finset.Ico m n, T (x j) ≤ B j)
    (hi : ∀ j ∈ Finset.Ico m n,
      IntervalIntegrable (fun u => entropyKernel c u*T u) volume (x j) (x (j+1))) :
    (∫ u in x m..x n, entropyKernel c u*T u) ≤
      ∑ j ∈ Finset.Ico m n, (x (j+1)-x j)*entropyKernel c (x (j+1))*B j := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := fun u => entropyKernel c u*T u) (a := x) (μ := volume) hmn
    (fun j hj => hi j (Finset.mem_Ico.mpr hj))
  rw [← hsum]
  apply Finset.sum_le_sum
  intro j hj
  exact entropy_quadrature_cell hc (hcl.trans (hx (Finset.mem_Ico.mp hj).1))
    (hx (Nat.le_succ j)) hT hT0 (hB j hj) (hi j hj)

/-- The exact exponential tail remainder after replacing `log(u/c)` by `u/c`.
This is the printed remainder at `H=40`, `r=9/20`. -/
theorem entropy_remainder_integral {c r H C : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hH : 0 ≤ H) :
    (∫ u in Ioi H, C*(1+u/c)*Real.exp (-(r*u))) =
      C*Real.exp (-(r*H))*(1/r+H/(c*r)+1/(c*r^2)) := by
  have hi (n : ℕ) : IntegrableOn (fun u : ℝ => u^n*Real.exp (-(r*u))) (Ioi H) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (n : ℝ)) (p := 1) (b := r)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hr
    have h0 : IntegrableOn (fun u : ℝ => u^n*Real.exp (-(r*u))) (Ioi 0) := by
      simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using h
    exact h0.mono_set (Ioi_subset_Ioi hH)
  have he : (fun u : ℝ => C*(1+u/c)*Real.exp (-(r*u))) =
      (fun u => C*(u^0*Real.exp (-(r*u))) + (C/c)*(u^1*Real.exp (-(r*u)))) := by
    ext u
    simp only [pow_zero, pow_one]
    ring
  rw [he, integral_add ((hi 0).const_mul C) ((hi 1).const_mul (C/c)),
    integral_const_mul, integral_const_mul,
    integral_monomial_exp_cutoff 0 hr hH, integral_monomial_exp_cutoff 1 hr hH]
  norm_num [tailMomentSeries, Finset.sum_range_succ]
  field_simp
  <;> ring

/-- Exponential domination makes the entropy integrand integrable, including
all finite quadrature cells and the infinite remainder. -/
theorem entropy_tail_integrable {c C r : ℝ} {T : ℝ → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hr : 0 < r)
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
    convert hh using 1 <;> ring

/-- The rigorously bounded infinite remainder, with no analytic statement
hidden in the finite numerical premises. -/
theorem entropy_remainder_bound {c C r H : ℝ} {T : ℝ → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hr : 0 < r) (hcH : c ≤ H)
    (hTm : Measurable T) (hT0 : ∀ u, 0 ≤ T u)
    (htail : ∀ u, c < u → T u ≤ C*Real.exp (-(r*u))) :
    (∫ u in Ioi H, entropyKernel c u*T u) ≤
      C*Real.exp (-(r*H))*(1/r+H/(c*r)+1/(c*r^2)) := by
  have hi := entropy_tail_integrable hc hC hr hTm hT0 htail
  have hiH := hi.mono_set (Ioi_subset_Ioi hcH)
  have he (n : ℕ) : IntegrableOn (fun u : ℝ => u^n*Real.exp (-(r*u))) (Ioi H) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (n : ℝ)) (p := 1) (b := r)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hr
    have h0 : IntegrableOn (fun u : ℝ => u^n*Real.exp (-(r*u))) (Ioi 0) := by
      simpa only [Real.rpow_natCast,Real.rpow_one,neg_mul] using h
    exact h0.mono_set (Ioi_subset_Ioi (hc.le.trans hcH))
  have hdom : IntegrableOn (fun u : ℝ => C*(1+u/c)*Real.exp (-(r*u))) (Ioi H) := by
    have hd : IntegrableOn
        (fun u : ℝ => C*(u^0*Real.exp (-(r*u)))+(C/c)*(u^1*Real.exp (-(r*u))))
        (Ioi H) := ((he 0).const_mul C).add ((he 1).const_mul (C/c))
    exact hd.congr (Filter.Eventually.of_forall fun u => by
      simp only [pow_zero,pow_one,one_mul]
      ring)
  rw [← entropy_remainder_integral hc hr (hc.le.trans hcH)]
  apply setIntegral_mono_on hiH hdom measurableSet_Ioi
  intro u hu
  have hcu : c < u := hcH.trans_lt hu
  have huPos : 0 < u := hc.trans hcu
  have hlog := Real.log_le_sub_one_of_pos (div_pos huPos hc)
  have hk : entropyKernel c u ≤ 1+u/c := by dsimp [entropyKernel]; linarith
  convert mul_le_mul hk (htail u hcu) (hT0 u)
    (show 0 ≤ 1+u/c by positivity) using 1 <;> ring

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
This generic rule applies to the finite entropy sum once its prefactors
have been proved separately convex. -/
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
  convert hh using 1 <;> ring

end
end SingularValueBounds.KL
