import SingularValueBounds.KL.Barrier.MixedAngular
import Mathlib.MeasureTheory.Integral.Prod

/-! Fubini's form of the inverse-profile integral. No derivative of the
increasing profile or its inverse is assumed. -/
open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1500000

theorem mixed_inverse_triangle_integral {g j f : ℝ → ℝ} {l : ℝ}
    (hg : Continuous g) (hf : Continuous f) (hl : l ≤ 1)
    (hgrange : ∀ x ∈ Icc l 1, g x ∈ Icc (g l) (g 1))
    (hjrange : ∀ c ∈ Icc (g l) (g 1), j c ∈ Icc l 1)
    (horder : ∀ c ∈ Icc (g l) (g 1), ∀ x ∈ Icc l 1, j c ≤ x ↔ c ≤ g x) :
    (∫ c in (g l)..(g 1), ∫ x in (j c)..1, f x) =
      ∫ x in l..1, (g x-g l)*f x := by
  have hab : g l ≤ g 1 := (hgrange l ⟨le_rfl,hl⟩).2
  let F : ℝ × ℝ → ℝ := {p | p.1 ≤ g p.2}.indicator (fun p => f p.2)
  have hregion : MeasurableSet {p : ℝ × ℝ | p.1 ≤ g p.2} :=
    isClosed_le continuous_fst (hg.comp continuous_snd) |>.measurableSet
  have hF : IntegrableOn F (Icc (g l) (g 1) ×ˢ Icc l 1) (volume.prod volume) := by
    exact ((hf.comp continuous_snd).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).indicator hregion
  have hswap : (∫ c in Icc (g l) (g 1), ∫ x in Icc l 1, F (c,x)) =
      ∫ x in Icc l 1, ∫ c in Icc (g l) (g 1), F (c,x) := by
    apply integral_integral_swap
    simpa only [IntegrableOn, ← Measure.prod_restrict] using! hF
  have hleft (c : ℝ) (hc : c ∈ Icc (g l) (g 1)) :
      (∫ x in Icc l 1, F (c,x)) = ∫ x in (j c)..1, f x := by
    calc
      _ = ∫ x in Icc l 1, (Ici (j c)).indicator f x := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        simp only [F, Set.indicator, Set.mem_setOf_eq, Set.mem_Ici]
        simp only [horder c hc x hx]
      _ = ∫ x in Icc (j c) 1, f x := by
        rw [setIntegral_indicator measurableSet_Ici]
        have he : Icc l 1 ∩ Ici (j c) = Icc (j c) 1 := by
          ext x
          simp only [mem_inter_iff, mem_Icc, mem_Ici]
          constructor
          · intro h; exact ⟨h.2,h.1.2⟩
          · intro h; exact ⟨⟨(hjrange c hc).1.trans h.1,h.2⟩,h.1⟩
        rw [he]
      _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (hjrange c hc).2]
  have hright (x : ℝ) (hx : x ∈ Icc l 1) :
      (∫ c in Icc (g l) (g 1), F (c,x)) = (g x-g l)*f x := by
    calc
      _ = ∫ c in Icc (g l) (g 1), (Iic (g x)).indicator (fun _ => f x) c := by rfl
      _ = ∫ c in Icc (g l) (g x), f x := by
        rw [setIntegral_indicator measurableSet_Iic]
        have he : Icc (g l) (g 1) ∩ Iic (g x) = Icc (g l) (g x) := by
          ext c
          simp only [mem_inter_iff,mem_Icc,mem_Iic]
          constructor
          · intro h; exact ⟨h.1.1,h.2⟩
          · intro h; exact ⟨⟨h.1,h.2.trans (hgrange x hx).2⟩,h.2⟩
        rw [he]
      _ = _ := by simp [Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal,
        sub_nonneg.mpr (hgrange x hx).1]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hl, ← integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ c in Icc (g l) (g 1), ∫ x in Icc l 1, F (c,x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro c hc
      exact (hleft c hc).symm
    _ = _ := hswap
    _ = _ := setIntegral_congr_fun measurableSet_Icc hright

def mixedInverseWeight (l x : ℝ) : ℝ := 2/(max l x)^3

theorem mixedInverseWeight_continuous {l : ℝ} (hl : 0 < l) :
    Continuous (mixedInverseWeight l) := by
  exact continuous_const.div ((continuous_const.max continuous_id).pow 3)
    (fun x => pow_ne_zero 3 (ne_of_gt (hl.trans_le (le_max_left l x))))

theorem mixedInverseWeight_eq {l x : ℝ} (hx : l ≤ x) :
    mixedInverseWeight l x = 2/x^3 := by simp only [mixedInverseWeight,max_eq_right hx]

theorem mixedInverseWeight_integral {l a : ℝ} (hl : 0 < l) (ha : a ∈ Icc l 1) :
    (∫ x in a..1, mixedInverseWeight l x) = 1/a^2-1 := by
  have ha0 : 0 < a := hl.trans_le ha.1
  have hh : (∫ x in a..1, mixedInverseWeight l x) =
      (∫ x in a..1, 2*x^(-3:ℤ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ha.2] at hx
    rw [mixedInverseWeight_eq (ha.1.trans hx.1)]
    simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv]
  rw [hh,intervalIntegral.integral_const_mul]
  have hz : (0:ℝ) ∉ uIcc a 1 := by rw [uIcc_of_le ha.2]; simp only [mem_Icc,not_and]; intro h; linarith
  rw [integral_zpow (n := (-3:ℤ)) (Or.inr ⟨by norm_num,hz⟩)]
  norm_num [inv_pow]
  ring_nf

/-- Young's inverse-integral identity, proved by integration over the
bounded region below the increasing graph. -/
theorem mixed_inverse_integral {g j : ℝ → ℝ} {l : ℝ}
    (hg : Continuous g) (hj : ContinuousOn j (Icc (g l) (g 1))) (hl : 0 < l) (hl1 : l ≤ 1)
    (hgrange : ∀ x ∈ Icc l 1, g x ∈ Icc (g l) (g 1))
    (hjrange : ∀ c ∈ Icc (g l) (g 1), j c ∈ Icc l 1)
    (horder : ∀ c ∈ Icc (g l) (g 1), ∀ x ∈ Icc l 1, j c ≤ x ↔ c ≤ g x) :
    (∫ c in (g l)..(g 1), 1/(j c)^2) =
      g 1-g l/l^2+(∫ x in l..1, 2*g x/x^3) := by
  have hab : g l ≤ g 1 := (hgrange l ⟨le_rfl,hl1⟩).2
  have htriangle := mixed_inverse_triangle_integral hg (mixedInverseWeight_continuous hl)
    hl1 hgrange hjrange horder
  have hleft : (∫ c in (g l)..(g 1), ∫ x in (j c)..1, mixedInverseWeight l x) =
      (∫ c in (g l)..(g 1), 1/(j c)^2-1) := by
    apply intervalIntegral.integral_congr
    intro c hc
    rw [uIcc_of_le hab] at hc
    exact mixedInverseWeight_integral hl (hjrange c hc)
  rw [hleft] at htriangle
  have hf : Continuous (mixedInverseWeight l) := mixedInverseWeight_continuous hl
  have hi := intervalIntegral.integral_congr (μ := volume) (a := l) (b := 1)
    (f := fun x => (g x-g l)*mixedInverseWeight l x)
    (g := fun x => g x*mixedInverseWeight l x-g l*mixedInverseWeight l x)
    (fun x _ => by ring)
  have hig : IntervalIntegrable (fun x => g x * mixedInverseWeight l x) volume l 1 :=
    (hg.mul hf).intervalIntegrable _ _
  have hic : IntervalIntegrable (fun x => g l * mixedInverseWeight l x) volume l 1 :=
    (continuous_const.mul hf).intervalIntegrable _ _
  rw [hi,intervalIntegral.integral_sub hig hic,intervalIntegral.integral_const_mul,
    mixedInverseWeight_integral hl ⟨le_rfl,hl1⟩] at htriangle
  have hright : (∫ x in l..1, g x*mixedInverseWeight l x) =
      ∫ x in l..1, 2*g x/x^3 := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le hl1] at hx
    rw [mixedInverseWeight_eq hx.1]
    ring
  rw [hright] at htriangle
  have hji : IntervalIntegrable (fun c => 1/(j c)^2) volume (g l) (g 1) := by
    exact (continuousOn_const.div (hj.pow 2) (fun c hc =>
      pow_ne_zero 2 (ne_of_gt (hl.trans_le (hjrange c hc).1)))).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_sub hji (intervalIntegrable_const),intervalIntegral.integral_const] at htriangle
  simp only [smul_eq_mul,mul_one] at htriangle
  simp only [div_eq_mul_inv,one_mul] at htriangle ⊢
  nlinarith only [htriangle]

theorem mixed_inverse_integral_of_continuousOn {g j : ℝ → ℝ} {l : ℝ}
    (hg : ContinuousOn g (Icc l 1)) (hj : ContinuousOn j (Icc (g l) (g 1)))
    (hl : 0 < l) (hl1 : l ≤ 1)
    (hgrange : ∀ x ∈ Icc l 1, g x ∈ Icc (g l) (g 1))
    (hjrange : ∀ c ∈ Icc (g l) (g 1), j c ∈ Icc l 1)
    (horder : ∀ c ∈ Icc (g l) (g 1), ∀ x ∈ Icc l 1, j c ≤ x ↔ c ≤ g x) :
    (∫ c in (g l)..(g 1), 1/(j c)^2) =
      g 1-g l/l^2+(∫ x in l..1, 2*g x/x^3) := by
  let G : ℝ → ℝ := fun x => g (max l (min 1 x))
  have hG : Continuous G := hg.comp_continuous
    (continuous_const.max (continuous_const.min continuous_id))
    (fun x => ⟨le_max_left _ _, max_le hl1 (min_le_left _ _)⟩)
  have hG_eq (x : ℝ) (hx : x ∈ Icc l 1) : G x = g x := by
    simp only [G,min_eq_right hx.2,max_eq_right hx.1]
  have hGl : G l = g l := hG_eq l ⟨le_rfl,hl1⟩
  have hG1 : G 1 = g 1 := hG_eq 1 ⟨hl1,le_rfl⟩
  have hG_range : ∀ x ∈ Icc l 1, G x ∈ Icc (G l) (G 1) := by
    intro x hx
    simpa only [hG_eq x hx,hGl,hG1] using hgrange x hx
  have hj' : ContinuousOn j (Icc (G l) (G 1)) := by simpa only [hGl,hG1] using hj
  have hj_range : ∀ c ∈ Icc (G l) (G 1), j c ∈ Icc l 1 := by
    simpa only [hGl,hG1] using hjrange
  have horder' : ∀ c ∈ Icc (G l) (G 1), ∀ x ∈ Icc l 1, j c ≤ x ↔ c ≤ G x := by
    intro c hc x hx
    rw [hG_eq x hx]
    exact horder c (by simpa only [hGl,hG1] using hc) x hx
  have hh := mixed_inverse_integral hG hj' hl hl1 hG_range hj_range horder'
  have hi : (∫ x in l..1, 2*G x/x^3) = ∫ x in l..1, 2*g x/x^3 := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le hl1] at hx
    rw [hG_eq x hx]
  simpa only [hGl,hG1,hi] using hh

end
end SingularValueBounds.KL
