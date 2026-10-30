import SingularValueBounds.KL.Weighted.RationalIntegral
import SingularValueBounds.KL.Upper.GeneralMeanInterpolation

/-! # Positive Laplace kernels for the general upper entropy error
Supplementary S1.6.3: decreasing convexity of the two entropy remainder terms. -/
open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

def weightedLaplace (weight rate : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ v in Ioi 0, weight v*Real.exp (-(rate v*L))

theorem weightedLaplace_antitone {weight rate : ℝ → ℝ}
    (hw : ∀ v > 0, 0 ≤ weight v) (hr : ∀ v > 0, 0 ≤ rate v)
    (hi : ∀ L ≥ 1, IntegrableOn (fun v => weight v*Real.exp (-(rate v*L))) (Ioi 0)) :
    AntitoneOn (weightedLaplace weight rate) (Ici 1) := by
  intro x hx y hy hxy
  apply setIntegral_mono_on (hi y hy) (hi x hx) measurableSet_Ioi
  intro v hv
  apply mul_le_mul_of_nonneg_left _ (hw v hv)
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hxy (hr v hv)]

theorem weightedLaplace_convex {weight rate : ℝ → ℝ}
    (hw : ∀ v > 0, 0 ≤ weight v)
    (hi : ∀ L ≥ 1, IntegrableOn (fun v => weight v*Real.exp (-(rate v*L))) (Ioi 0)) :
    ConvexOn ℝ (Ici 1) (weightedLaplace weight rate) := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hnode : 1 ≤ a*x+b*y := by
    have h1 := mul_le_mul_of_nonneg_left hx ha
    have h2 := mul_le_mul_of_nonneg_left hy hb
    nlinarith
  have hdom := ((hi x hx).const_mul a).add ((hi y hy).const_mul b)
  have hh := setIntegral_mono_on (hi (a*x+b*y) hnode) hdom measurableSet_Ioi
    (fun v hv => ?_)
  · unfold weightedLaplace
    change (∫ v in Ioi 0,weight v*Real.exp (-(rate v*(a*x+b*y)))) ≤
      (∫ v in Ioi 0,a*(weight v*Real.exp (-(rate v*x)))+b*(weight v*Real.exp (-(rate v*y)))) at hh
    rw [integral_add (f := fun v => a*(weight v*Real.exp (-(rate v*x))))
      (g := fun v => b*(weight v*Real.exp (-(rate v*y))))
      ((hi x hx).const_mul a) ((hi y hy).const_mul b),
      integral_const_mul,integral_const_mul] at hh
    exact hh
  · have he := convexOn_exp.2 (mem_univ (-(rate v*x))) (mem_univ (-(rate v*y))) ha hb hab
    simp only [smul_eq_mul] at he
    have he' : Real.exp (-(rate v*(a*x+b*y))) ≤
        a*Real.exp (-(rate v*x))+b*Real.exp (-(rate v*y)) := by
      convert! he using 1 <;> congr 1 <;> ring
    have hm := mul_le_mul_of_nonneg_left he' (hw v hv)
    change weight v*Real.exp (-(rate v*(a*x+b*y))) ≤
      a*(weight v*Real.exp (-(rate v*x)))+b*(weight v*Real.exp (-(rate v*y)))
    convert! hm using 1 <;> ring

theorem affineLaplace_integrable {weight : ℝ → ℝ} {α β L : ℝ}
    (hwmeas : Measurable weight) (hw : ∀ v > 0, 0 ≤ weight v ∧ weight v ≤ 1)
    (hα : 0 ≤ α) (hβ : 0 < β) (hL : 1 ≤ L) :
    IntegrableOn (fun v => weight v*Real.exp (-((α+β*v)*L))) (Ioi 0) := by
  have hdom0 := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (0 : ℝ)) (p := (1 : ℝ)) (b := β) (by norm_num) (by norm_num) hβ
  have hdom : IntegrableOn (fun v : ℝ => Real.exp (-(β*v))) (Ioi 0) := by
    simpa only [Real.rpow_zero,Real.rpow_one,one_mul,neg_mul] using hdom0
  apply hdom.mono'
  · exact (hwmeas.mul (Real.measurable_exp.comp
      (((measurable_const.add (measurable_const.mul measurable_id)).mul_const L).neg))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    have hwv := hw v hv
    have hrate : 0 ≤ α+β*v := by positivity
    have hprod := mul_nonneg hrate (sub_nonneg.mpr hL)
    have he : Real.exp (-((α+β*v)*L)) ≤ Real.exp (-(β*v)) :=
      Real.exp_le_exp.mpr (by nlinarith only [hprod,hα])
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hwv.1 (Real.exp_nonneg _))]
    exact (mul_le_mul_of_nonneg_right hwv.2 (Real.exp_nonneg _)).trans (by simpa using he)

def resolventLaplaceKernel (v : ℝ) : ℝ := 1/(1+v)
def differenceLaplaceKernel (q v : ℝ) : ℝ := 1/(1+v)-1/(q*(q+v))

theorem resolventLaplaceKernel_bounds {v : ℝ} (hv : 0 < v) :
    0 ≤ resolventLaplaceKernel v ∧ resolventLaplaceKernel v ≤ 1 := by
  constructor
  · exact div_nonneg zero_le_one (by linarith)
  · exact (div_le_one (by linarith : 0 < 1+v)).mpr (by linarith)

theorem differenceLaplaceKernel_bounds {q v : ℝ} (hq : 1 < q) (hv : 0 < v) :
    0 ≤ differenceLaplaceKernel q v ∧ differenceLaplaceKernel q v ≤ 1 := by
  have hq0 : 0 < q := by linarith
  have h1 : 0 < 1+v := by linarith
  have h2 : 0 < q*(q+v) := by positivity
  have hd : 1+v ≤ q*(q+v) := by nlinarith [mul_nonneg (sub_nonneg.mpr hq.le) hv.le]
  have hi : 1/(q*(q+v)) ≤ 1/(1+v) := one_div_le_one_div_of_le h1 hd
  have hi0 : 0 ≤ 1/(q*(q+v)) := by positivity
  have hu := (resolventLaplaceKernel_bounds hv).2
  dsimp [differenceLaplaceKernel,resolventLaplaceKernel] at *
  exact ⟨by linarith,by linarith⟩

theorem affineLaplace_convex {weight : ℝ → ℝ} {α β : ℝ}
    (hm : Measurable weight) (hw : ∀ v > 0, 0 ≤ weight v ∧ weight v ≤ 1)
    (hα : 0 ≤ α) (hβ : 0 < β) :
    ConvexOn ℝ (Ici 1) (weightedLaplace weight (fun v => α+β*v)) :=
  weightedLaplace_convex (fun v hv => (hw v hv).1)
    (fun L hL => affineLaplace_integrable hm hw hα hβ hL)

theorem affineLaplace_antitone {weight : ℝ → ℝ} {α β : ℝ}
    (hm : Measurable weight) (hw : ∀ v > 0, 0 ≤ weight v ∧ weight v ≤ 1)
    (hα : 0 ≤ α) (hβ : 0 < β) :
    AntitoneOn (weightedLaplace weight (fun v => α+β*v)) (Ici 1) :=
  weightedLaplace_antitone (fun v hv => (hw v hv).1)
    (fun v hv => by positivity)
    (fun L hL => affineLaplace_integrable hm hw hα hβ hL)

end
end SingularValueBounds.KL

