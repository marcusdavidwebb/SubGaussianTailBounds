import SingularValueBounds.KL.Upper.EntropyQuadrature

/-! # General upper-mean interpolation on the complete real L domain
Supplementary S1.6.3, Lemma app:general-upper-drift. -/
open Set
namespace SingularValueBounds.KL
noncomputable section

def generalMeanCritical (r lo hi : ℝ) : ℝ := min hi (max lo (1/r))

theorem generalMeanCritical_mem {r lo hi : ℝ} (hlohi : lo ≤ hi) :
    generalMeanCritical r lo hi ∈ Icc lo hi :=
  ⟨le_min hlohi (le_max_left _ _), min_le_left _ _⟩

lemma log_tangent_upper {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    Real.log (c*y) ≤ Real.log (c*x)+(y-x)/x := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hl
  rw [Real.log_mul hc.ne' hy.ne', Real.log_mul hc.ne' hx.ne']
  have he : y/x-1 = (y-x)/x := by field_simp [hx.ne']
  rw [he] at hl
  linarith

/-- The clipped critical point minimizes the linear-minus-logarithm margin,
including either boundary case. -/
theorem generalMeanCritical_minimum {r c lo hi x : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hx : x ∈ Icc lo hi) :
    r*generalMeanCritical r lo hi-Real.log (c*generalMeanCritical r lo hi) ≤
      r*x-Real.log (c*x) := by
  let z := generalMeanCritical r lo hi
  have hzmem : z ∈ Icc lo hi := generalMeanCritical_mem hlohi
  have hz0 : 0 < z := hlo.trans_le hzmem.1
  have hx0 : 0 < x := hlo.trans_le hx.1
  have ht := log_tangent_upper hc hz0 hx0
  have hs : 0 ≤ (r-1/z)*(x-z) := by
    by_cases hleft : 1/r ≤ lo
    · have hz : z = lo := by
        dsimp only [z,generalMeanCritical]
        rw [max_eq_left hleft,min_eq_right hlohi]
      rw [hz]
      have hrr : 1/lo ≤ r := (one_div_le hr hlo).mp hleft
      exact mul_nonneg (sub_nonneg.mpr hrr) (sub_nonneg.mpr hx.1)
    · by_cases hright : hi ≤ 1/r
      · have hz : z = hi := by
          dsimp only [z,generalMeanCritical]
          rw [max_eq_right (le_of_not_ge hleft),min_eq_left hright]
        rw [hz]
        have hhi : 0 < hi := hlo.trans_le hlohi
        have hrr : r ≤ 1/hi := (le_one_div hr hhi).mpr hright
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hrr) (sub_nonpos.mpr hx.2)
      · have hz : z = 1/r := by
          dsimp only [z,generalMeanCritical]
          rw [max_eq_right (le_of_not_ge hleft), min_eq_right (le_of_not_ge hright)]
        rw [hz]
        simp
  have he : (r-1/z)*(x-z) = r*(x-z)-(x-z)/z := by ring
  rw [he] at hs
  linarith

/-- Certified node bounds imply a chord bound at every intermediate real L. -/
theorem generalMean_chord {E : ℝ → ℝ} {lo hi el eh L : ℝ}
    (hconv : ConvexOn ℝ (Icc lo hi) E) (hlohi : lo < hi)
    (hel : E lo ≤ el) (heh : E hi ≤ eh) (hL : L ∈ Icc lo hi) :
    E L ≤ el+(eh-el)/(hi-lo)*(L-lo) := by
  let a := (hi-L)/(hi-lo)
  let b := (L-lo)/(hi-lo)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hL.2) (sub_pos.mpr hlohi).le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hL.1) (sub_pos.mpr hlohi).le
  have hsum : a+b=1 := by dsimp [a,b];field_simp [ne_of_gt (sub_pos.mpr hlohi)] <;> ring
  have hnode : a*lo+b*hi=L := by dsimp [a,b];field_simp [ne_of_gt (sub_pos.mpr hlohi)] <;> ring
  have hc := hconv.2 (show lo ∈ Icc lo hi from ⟨le_rfl,hlohi.le⟩)
    (show hi ∈ Icc lo hi from ⟨hlohi.le,le_rfl⟩) ha hb hsum
  simp only [smul_eq_mul,hnode] at hc
  have hh := hc.trans (add_le_add (mul_le_mul_of_nonneg_left hel ha) (mul_le_mul_of_nonneg_left heh hb))
  convert! hh using 1 <;> (try dsimp [a,b]) <;> field_simp [ne_of_gt (sub_pos.mpr hlohi)] <;> ring

/-- The finite minimum comparison certifies an entire real grid interval. -/
theorem generalMean_chord_cost {E : ℝ → ℝ} {w c J lo hi el eh L : ℝ}
    (hc : 0 < c) (hlo : 0 < lo) (hlohi : lo < hi)
    (hconv : ConvexOn ℝ (Icc lo hi) E) (hel : E lo ≤ el) (heh : E hi ≤ eh)
    (hr : 0 < w-2-(eh-el)/(hi-lo))
    (hmargin : 0 ≤ 2+(w-2-(eh-el)/(hi-lo))*
        generalMeanCritical (w-2-(eh-el)/(hi-lo)) lo hi -
      Real.log (c*generalMeanCritical (w-2-(eh-el)/(hi-lo)) lo hi)-J/2-el+
        ((eh-el)/(hi-lo))*lo)
    (hL : L ∈ Icc lo hi) :
    2*L-2+Real.log (c*L)+E L+J/2 ≤ w*L := by
  have hE := generalMean_chord hconv hlohi hel heh hL
  have hm := generalMeanCritical_minimum hr hc hlo hlohi.le hL
  nlinarith only [hE,hm,hmargin]

/-- The last node and monotonicity cover all L beyond the finite grid. -/
theorem generalMean_unbounded_cost {E : ℝ → ℝ} {w c J H eH L : ℝ}
    (hc : 0 < c) (hH : 0 < H) (hL : H ≤ L)
    (hE : E L ≤ eH) (hw : 1/H ≤ w-2)
    (hmargin : 0 ≤ 2+(w-2)*H-Real.log (c*H)-J/2-eH) :
    2*L-2+Real.log (c*L)+E L+J/2 ≤ w*L := by
  have ht := log_tangent_upper hc hH (hH.trans_le hL)
  have hs := mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr hL)
  have he : (1/H)*(L-H) = (L-H)/H := by ring
  rw [he] at hs
  nlinarith only [ht,hs,hE,hmargin]

end
end SingularValueBounds.KL

