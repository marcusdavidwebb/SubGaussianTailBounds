import SingularValueBounds.KL.Upper.GeneralMeanLaplace

open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

theorem exponentialResolvent_scaled {x r : ℝ} (hx : 0<x) (hr : 0<r) :
    (∫ v in Ioi 0,Real.exp (-(x*v))/(r+v)) = exponentialResolvent (x*r) := by
  have hs := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u)/(x*r+u)) (0 : ℝ) hx
  simp only [mul_zero,smul_eq_mul] at hs
  have hi : (∫ v in Ioi 0,Real.exp (-(x*v))/(x*r+x*v)) =
      (1/x)*(∫ v in Ioi 0,Real.exp (-(x*v))/(r+v)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hd : r+v≠0 := ne_of_gt (by have hv0 : 0<v := hv; linarith)
    dsimp only
    rw [show x*r+x*v=x*(r+v) by ring]
    field_simp
  rw [hi] at hs
  apply mul_left_cancel₀ (one_div_ne_zero hx.ne')
  simpa only [one_div,exponentialResolvent] using hs

theorem resolventLaplace_integrable {x r : ℝ} (hx : 0<x) (hr : 0<r) :
    IntegrableOn (fun v : ℝ => Real.exp (-(x*v))/(r+v)) (Ioi 0) := by
  have hdom := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (0 : ℝ)) (p := (1 : ℝ)) (b := x) (by norm_num) (by norm_num) hx
  have he : IntegrableOn (fun v : ℝ => Real.exp (-(x*v))) (Ioi 0) := by
    simpa only [Real.rpow_zero,Real.rpow_one,one_mul,neg_mul] using hdom
  apply (he.const_mul (1/r)).mono'
  · exact (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).div
      (measurable_const.add measurable_id) |>.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0<v := hv
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤Real.exp (-(x*v))/(r+v))]
    simpa [div_eq_mul_inv,mul_comm] using div_le_div_of_nonneg_left
      (Real.exp_nonneg (-(x*v))) hr (by linarith : r≤r+v)

theorem exponentialResolvent_laplace {x : ℝ} (hx : 0<x) :
    exponentialResolvent x = ∫ v in Ioi 0,resolventLaplaceKernel v*Real.exp (-(x*v)) := by
  have hs := exponentialResolvent_scaled hx (by norm_num : (0 : ℝ)<1)
  rw [mul_one] at hs
  rw [← hs]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  simp [resolventLaplaceKernel,div_eq_mul_inv,mul_comm]

theorem exponentialResolvent_difference_laplace {x q : ℝ} (hx : 0<x) (hq : 1<q) :
    exponentialResolvent x-exponentialResolvent (q*x)/q =
      ∫ v in Ioi 0,differenceLaplaceKernel q v*Real.exp (-(x*v)) := by
  have hq0 : 0<q := by linarith
  have hi1 := resolventLaplace_integrable hx (by norm_num : (0 : ℝ)<1)
  have hiq := (resolventLaplace_integrable hx hq0).div_const q
  have hid : (fun v : ℝ => differenceLaplaceKernel q v*Real.exp (-(x*v))) =
      (fun v => Real.exp (-(x*v))/(1+v)-(Real.exp (-(x*v))/(q+v))/q) := by
    funext v
    dsimp [differenceLaplaceKernel]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hid,integral_sub hi1 hiq,integral_div,
    exponentialResolvent_scaled hx (by norm_num : (0 : ℝ)<1),
    exponentialResolvent_scaled hx hq0,mul_one,mul_comm x q]

theorem exponentialResolvent_laplace_shift {x α L : ℝ} (hx : 0<x) (hL : 1≤L) :
    Real.exp (-(α*L))*exponentialResolvent (x*L) =
      weightedLaplace resolventLaplaceKernel (fun v => α+x*v) L := by
  rw [exponentialResolvent_laplace (by positivity : 0<x*L),← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [show -((α+x*v)*L)=-(α*L)+-((x*L)*v) by ring,Real.exp_add]
  ring

theorem exponentialResolvent_difference_shift {x α L q : ℝ}
    (hx : 0<x) (hL : 1≤L) (hq : 1<q) :
    Real.exp (-(α*L))*(exponentialResolvent (x*L)-exponentialResolvent (q*(x*L))/q) =
      weightedLaplace (differenceLaplaceKernel q) (fun v => α+x*v) L := by
  rw [exponentialResolvent_difference_laplace (by positivity : 0<x*L) hq,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [show -((α+x*v)*L)=-(α*L)+-((x*L)*v) by ring,Real.exp_add]
  ring

def generalMeanRemainder (A q c L : ℝ) : ℝ :=
  (2*A/q)*Real.exp (-2-(q*c/2-2)*L)*(1+exponentialResolvent (q*c*L/2))

def generalMeanContinuation (A q c s L : ℝ) : ℝ :=
  A*Real.exp (-2-(q*s/2-2)*L)*
    ((2-2/q)*(1+Real.log (s/c))+2*exponentialResolvent (s*L/2)-
      (2/q)*exponentialResolvent (q*s*L/2))

def generalMeanError (A q c s L : ℝ) : ℝ :=
  generalMeanRemainder A q c L+
    if 1<q then generalMeanContinuation A q c s L else 0

theorem affineExp_convex (α : ℝ) :
    ConvexOn ℝ (Ici (1 : ℝ)) (fun L => Real.exp (-(α*L))) := by
  refine ⟨convex_Ici _,?_⟩
  intro x hx y hy a b ha hb hab
  have h := convexOn_exp.2 (mem_univ (-(α*x))) (mem_univ (-(α*y))) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  convert h using 1 <;> congr 1 <;> ring

theorem affineExp_antitone {α : ℝ} (hα : 0≤α) :
    AntitoneOn (fun L => Real.exp (-(α*L))) (Ici (1 : ℝ)) := by
  intro x hx y hy hxy
  exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hxy hα])

theorem generalMeanRemainder_eq {A q c L : ℝ} (hq : 0<q) (hc : 0<c) (hL : 1≤L) :
    generalMeanRemainder A q c L =
      ((2*A/q)*Real.exp (-2))*(Real.exp (-((q*c/2-2)*L))+
        weightedLaplace resolventLaplaceKernel (fun v => (q*c/2-2)+(q*c/2)*v) L) := by
  rw [← exponentialResolvent_laplace_shift (by positivity : 0<q*c/2) hL]
  unfold generalMeanRemainder
  rw [show -2-(q*c/2-2)*L=(-2)+-((q*c/2-2)*L) by ring,Real.exp_add]
  rw [show q*c/2*L=q*c*L/2 by ring]
  ring

theorem generalMeanContinuation_eq {A q c s L : ℝ}
    (hs : 0<s) (hq : 1<q) (hL : 1≤L) :
    generalMeanContinuation A q c s L = (A*Real.exp (-2))*
      (((2-2/q)*(1+Real.log (s/c)))*Real.exp (-((q*s/2-2)*L))+
        2*weightedLaplace (differenceLaplaceKernel q)
          (fun v => (q*s/2-2)+(s/2)*v) L) := by
  rw [← exponentialResolvent_difference_shift (by positivity : 0<s/2) hL hq]
  unfold generalMeanContinuation
  rw [show -2-(q*s/2-2)*L=(-2)+-((q*s/2-2)*L) by ring,Real.exp_add]
  have hi : q*(s/2*L)=q*s*L/2 := by ring
  rw [hi]
  ring

theorem generalMeanRemainder_convex {A q c : ℝ}
    (hA : 0≤A) (hq : 0<q) (hc : 0<c) (hqc : 2≤q*c/2) :
    ConvexOn ℝ (Ici 1) (generalMeanRemainder A q c) := by
  have hres := affineLaplace_convex
    (weight := resolventLaplaceKernel) (by unfold resolventLaplaceKernel; fun_prop)
    (fun v hv => resolventLaplaceKernel_bounds hv) (by linarith : 0≤q*c/2-2)
    (by positivity : 0<q*c/2)
  have hh := (affineExp_convex (q*c/2-2)).add hres
  have hh' := ConvexOn.smul (show 0≤(2*A/q)*Real.exp (-2) by positivity) hh
  apply hh'.congr
  intro L hL
  simpa only [smul_eq_mul] using (generalMeanRemainder_eq hq hc hL).symm

theorem generalMeanContinuation_convex {A q c s : ℝ}
    (hA : 0≤A) (hq : 1<q) (hc : 0<c) (hsc : c≤s) (hqs : 2≤q*s/2) :
    ConvexOn ℝ (Ici 1) (generalMeanContinuation A q c s) := by
  have hs : 0<s := hc.trans_le hsc
  have hres := affineLaplace_convex (weight := differenceLaplaceKernel q)
    (by unfold differenceLaplaceKernel; fun_prop)
    (fun v hv => differenceLaplaceKernel_bounds hq hv)
    (by linarith : 0≤q*s/2-2) (by positivity : 0<s/2)
  have hcoeff : 0≤(2-2/q)*(1+Real.log (s/c)) := by
    have hl : 0≤Real.log (s/c) := Real.log_nonneg ((one_le_div hc).mpr hsc)
    have hd : 2/q≤2 := (div_le_iff₀ (by linarith : 0<q)).mpr (by linarith)
    exact mul_nonneg (sub_nonneg.mpr hd) (by linarith)
  have hh := (ConvexOn.smul hcoeff (affineExp_convex (q*s/2-2))).add
    (ConvexOn.smul (by norm_num : (0 : ℝ)≤2) hres)
  have hh' := ConvexOn.smul (show 0≤A*Real.exp (-2) by positivity) hh
  apply hh'.congr
  intro L hL
  simpa only [smul_eq_mul] using (generalMeanContinuation_eq hs hq hL).symm

theorem generalMeanRemainder_antitone {A q c : ℝ}
    (hA : 0≤A) (hq : 0<q) (hc : 0<c) (hqc : 2≤q*c/2) :
    AntitoneOn (generalMeanRemainder A q c) (Ici 1) := by
  have hres := affineLaplace_antitone (weight := resolventLaplaceKernel)
    (by unfold resolventLaplaceKernel; fun_prop)
    (fun v hv => resolventLaplaceKernel_bounds hv)
    (by linarith : 0≤q*c/2-2) (by positivity : 0<q*c/2)
  intro x hx y hy hxy
  rw [generalMeanRemainder_eq hq hc hx,generalMeanRemainder_eq hq hc hy]
  exact mul_le_mul_of_nonneg_left (add_le_add
    (affineExp_antitone (by linarith : 0≤q*c/2-2) hx hy hxy) (hres hx hy hxy))
    (by positivity)

theorem generalMeanContinuation_antitone {A q c s : ℝ}
    (hA : 0≤A) (hq : 1<q) (hc : 0<c) (hsc : c≤s) (hqs : 2≤q*s/2) :
    AntitoneOn (generalMeanContinuation A q c s) (Ici 1) := by
  have hs : 0<s := hc.trans_le hsc
  have hres := affineLaplace_antitone (weight := differenceLaplaceKernel q)
    (by unfold differenceLaplaceKernel; fun_prop)
    (fun v hv => differenceLaplaceKernel_bounds hq hv)
    (by linarith : 0≤q*s/2-2) (by positivity : 0<s/2)
  have hcoeff : 0≤(2-2/q)*(1+Real.log (s/c)) := by
    have hl : 0≤Real.log (s/c) := Real.log_nonneg ((one_le_div hc).mpr hsc)
    have hd : 2/q≤2 := (div_le_iff₀ (by linarith : 0<q)).mpr (by linarith)
    exact mul_nonneg (sub_nonneg.mpr hd) (by linarith)
  intro x hx y hy hxy
  rw [generalMeanContinuation_eq hs hq hx,generalMeanContinuation_eq hs hq hy]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (affineExp_antitone (by linarith : 0≤q*s/2-2) hx hy hxy) hcoeff)
    (mul_le_mul_of_nonneg_left (hres hx hy hxy) (by norm_num))

theorem generalMeanError_convex_antitone {A q c s : ℝ}
    (hA : 0≤A) (hq : 0<q) (hc : 0<c) (hqc : 2≤q*c/2)
    (hcont : 1<q → c≤s ∧ 2≤q*s/2) :
    ConvexOn ℝ (Ici 1) (generalMeanError A q c s) ∧
    AntitoneOn (generalMeanError A q c s) (Ici 1) := by
  by_cases hq1 : 1<q
  · have hd : generalMeanError A q c s = fun L =>
        generalMeanRemainder A q c L+generalMeanContinuation A q c s L := by
      funext L
      simp only [generalMeanError,if_pos hq1]
    rw [hd]
    exact ⟨(generalMeanRemainder_convex hA hq hc hqc).add
      (generalMeanContinuation_convex hA hq1 hc (hcont hq1).1 (hcont hq1).2),
      fun x hx y hy hxy => add_le_add
        (generalMeanRemainder_antitone hA hq hc hqc hx hy hxy)
        (generalMeanContinuation_antitone hA hq1 hc (hcont hq1).1 (hcont hq1).2 hx hy hxy)⟩
  · have hd : generalMeanError A q c s = generalMeanRemainder A q c := by
      funext L
      simp only [generalMeanError,if_neg hq1,add_zero]
    rw [hd]
    exact ⟨generalMeanRemainder_convex hA hq hc hqc,generalMeanRemainder_antitone hA hq hc hqc⟩

theorem exponentialResolvent_nonneg (x : ℝ) (hx : 0≤x) : 0≤exponentialResolvent x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0<u := hu
  exact div_nonneg (Real.exp_nonneg _) (by linarith)

theorem exponentialResolvent_difference_nonneg {x q : ℝ} (hx : 0<x) (hq : 1<q) :
    0≤exponentialResolvent x-exponentialResolvent (q*x)/q := by
  rw [exponentialResolvent_difference_laplace hx hq]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (differenceLaplaceKernel_bounds hq hu).1 (Real.exp_nonneg _)

theorem generalMeanContinuation_bracket_nonneg {q c s L : ℝ}
    (hq : 1<q) (hc : 0<c) (hcs : c≤s) (hL : 1≤L) :
    0≤(2-2/q)*(1+Real.log (s/c))+2*exponentialResolvent (s*L/2)-
      (2/q)*exponentialResolvent (q*s*L/2) := by
  have hs : 0<s := hc.trans_le hcs
  have hd := exponentialResolvent_difference_nonneg (by positivity : 0<s*L/2) hq
  have hl : 0≤Real.log (s/c) := Real.log_nonneg ((one_le_div hc).mpr hcs)
  have hi : 2/q≤2 := (div_le_iff₀ (by linarith : 0<q)).mpr (by linarith)
  have hh := mul_nonneg (sub_nonneg.mpr hi) (show 0≤1+Real.log (s/c) by linarith)
  rw [show q*(s*L/2)=q*s*L/2 by ring] at hd
  ring_nf at hh hd ⊢
  nlinarith

theorem generalMeanRemainder_bound {A q c L e I : ℝ}
    (hA : 0≤A) (hq : 0<q) (hc : 0<c) (hL : 1≤L)
    (he : Real.exp (-2-(q*c/2-2)*L)≤e)
    (hI : exponentialResolvent (q*c*L/2)≤I) :
    generalMeanRemainder A q c L≤(2*A/q)*e*(1+I) := by
  have hI0 := exponentialResolvent_nonneg (q*c*L/2) (by positivity)
  have he0 := Real.exp_nonneg (-2-(q*c/2-2)*L)
  have he0' : 0≤e := he0.trans he
  unfold generalMeanRemainder
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left he (by positivity))
    (add_le_add_left hI 1) (by linarith) (by positivity)

theorem generalMeanContinuation_bound {A q c s L e loghi Ihi Ilo : ℝ}
    (hA : 0≤A) (hq : 1<q) (hc : 0<c) (hcs : c≤s) (hL : 1≤L)
    (he : Real.exp (-2-(q*s/2-2)*L)≤e) (hl : Real.log (s/c)≤loghi)
    (hi : exponentialResolvent (s*L/2)≤Ihi)
    (hlo : Ilo≤exponentialResolvent (q*s*L/2)) :
    generalMeanContinuation A q c s L≤
      A*e*((2-2/q)*(1+loghi)+2*Ihi-(2/q)*Ilo) := by
  have hq0 : 0<q := by linarith
  have hcoeff : 0≤2-2/q := by
    have hh : 2/q≤2 := (div_le_iff₀ hq0).mpr (by linarith)
    linarith
  have hb := generalMeanContinuation_bracket_nonneg hq hc hcs hL
  have hbound : (2-2/q)*(1+Real.log (s/c))+2*exponentialResolvent (s*L/2)-
      (2/q)*exponentialResolvent (q*s*L/2)≤
        (2-2/q)*(1+loghi)+2*Ihi-(2/q)*Ilo := by
    nlinarith [mul_le_mul_of_nonneg_left hl hcoeff,
      mul_le_mul_of_nonneg_left hlo (show 0≤2/q by positivity)]
  unfold generalMeanContinuation
  exact mul_le_mul (mul_le_mul_of_nonneg_left he hA) hbound hb
    (mul_nonneg hA ((Real.exp_nonneg _).trans he))

end
end SingularValueBounds.KL
