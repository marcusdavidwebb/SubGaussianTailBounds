import Mathlib.Data.Real.Pi.Bounds
import SingularValueBounds.KL.Lower.CellAnalysis
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Scalar integrals and regularity of the two concrete lower profiles. -/
open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1500000

/-- The endpoint mixed cap, including its breakpoint at `73/100`. -/
def endpointLowerProfile (k : ℝ) : ℝ := min (2*k) (73/50)

/-- Nonsingular angular expression for the mixed-profile cost. -/
def profileAngularCost (h : ℝ → ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..Real.pi/2, Real.sin θ*h (Real.sin θ)

theorem generalLowerPolynomial_continuous : Continuous generalLowerPolynomial := by
  unfold generalLowerPolynomial
  fun_prop

theorem generalLowerProfile_continuous : Continuous generalLowerProfile :=
  continuous_const.min (continuous_const.max generalLowerPolynomial_continuous)

theorem endpointLowerProfile_continuous : Continuous endpointLowerProfile := by
  unfold endpointLowerProfile
  fun_prop

theorem endpointLowerProfile_mono : Monotone endpointLowerProfile := by
  intro x y hxy
  exact min_le_min_right _ (by linarith)

theorem endpointLowerProfile_nonneg {k : ℝ} (hk : 0 ≤ k) : 0 ≤ endpointLowerProfile k :=
  le_min (by linarith) (by norm_num)

theorem endpointLowerProfile_pos {k : ℝ} (hk : 0 < k) : 0 < endpointLowerProfile k :=
  lt_min (by linarith) (by norm_num)

theorem generalLowerProfile_pos (k : ℝ) : 0 < generalLowerProfile k :=
  lt_of_lt_of_le (by norm_num) (generalLowerProfile_bounds k).1

theorem profileAngularCost_nonneg {h : ℝ → ℝ} (hc : Continuous h)
    (hp : ∀ k ∈ Icc (0:ℝ) 1, 0 ≤ h k) : 0 ≤ profileAngularCost h := by
  apply intervalIntegral.integral_nonneg Real.pi_div_two_pos.le
  intro θ hθ
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2,Real.pi_pos])
  exact mul_nonneg hs (hp _ ⟨hs,Real.sin_le_one _⟩)

/-- Cumulative integrals of the four powers occurring in the cubic profile. -/
theorem profile_sin_moments (t : ℝ) :
    (∫ θ in (0:ℝ)..t, Real.sin θ) = 1-Real.cos t ∧
    (∫ θ in (0:ℝ)..t, Real.sin θ^2) = (t-Real.sin t*Real.cos t)/2 ∧
    (∫ θ in (0:ℝ)..t, Real.sin θ^3) = 2/3-Real.cos t+(Real.cos t)^3/3 ∧
    (∫ θ in (0:ℝ)..t, Real.sin θ^4) =
      3*t/8-Real.sin t*Real.cos t*(3+2*Real.sin t^2)/8 := by
  have hs := Real.sin_sq_add_cos_sq t
  constructor
  · simpa using integral_sin (a := (0:ℝ)) (b := t)
  constructor
  · rw [integral_sin_sq]
    simp
    ring
  constructor
  · rw [integral_sin_pow_three]
    simp
    ring
  · rw [show (4:ℕ)=2+2 by norm_num,integral_sin_pow,integral_sin_sq]
    norm_num
    nlinarith [mul_eq_mul_left_iff.mp (show Real.sin t*Real.cos t*(Real.sin t^2+Real.cos t^2)=Real.sin t*Real.cos t*1 by rw [hs])]

/-- A derivative comparison anchored at zero, used for alternating sine bounds. -/
theorem profile_nonneg_of_deriv {f f' : ℝ → ℝ}
    (hc : Continuous f) (hd : ∀ x, HasDerivAt f (f' x) x)
    (h0 : 0 ≤ f 0) (hp : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc.continuousOn
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hp x (le_of_lt (show 0 < x from by simpa using hx)))
  exact h0.trans (hm (by simp) hx hx)

theorem profile_sin_lower3 {x : ℝ} (hx : 0 ≤ x) : x-x^3/6 ≤ Real.sin x := by
  have hh := profile_nonneg_of_deriv
    (f := fun x => Real.sin x-x+x^3/6)
    (f' := fun x => Real.cos x-1+x^2/2) (by fun_prop)
    (by intro x; convert (((Real.hasDerivAt_sin x).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 3).div_const 6)) using 1 <;> simp [id_eq] <;> ring)
    (by norm_num) (fun x _ => by linarith [Real.one_sub_sq_div_two_le_cos (x := x)]) hx
  linarith

theorem profile_cos_upper4 {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1-x^2/2+x^4/24 := by
  have hh := profile_nonneg_of_deriv
    (f := fun x => 1-x^2/2+x^4/24-Real.cos x)
    (f' := fun x => Real.sin x-x+x^3/6) (by fun_prop)
    (by intro x; convert (((hasDerivAt_const x 1).sub
      (((hasDerivAt_id x).pow 2).div_const 2)).add
      (((hasDerivAt_id x).pow 4).div_const 24)).sub (Real.hasDerivAt_cos x) using 1 <;> simp [id_eq] <;> ring)
    (by norm_num) (fun x hx => by linarith [profile_sin_lower3 hx]) hx
  linarith

theorem profile_sin_upper5 {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x-x^3/6+x^5/120 := by
  have hh := profile_nonneg_of_deriv
    (f := fun x => x-x^3/6+x^5/120-Real.sin x)
    (f' := fun x => 1-x^2/2+x^4/24-Real.cos x) (by fun_prop)
    (by intro x; convert (((hasDerivAt_id x).sub
      (((hasDerivAt_id x).pow 3).div_const 6)).add
      (((hasDerivAt_id x).pow 5).div_const 120)).sub (Real.hasDerivAt_sin x) using 1 <;> simp [id_eq] <;> ring)
    (by norm_num) (fun x hx => by linarith [profile_cos_upper4 hx]) hx
  linarith

theorem profile_cos_lower6 {x : ℝ} (hx : 0 ≤ x) :
    1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  have hh := profile_nonneg_of_deriv
    (f := fun x => Real.cos x-1+x^2/2-x^4/24+x^6/720)
    (f' := fun x => x-x^3/6+x^5/120-Real.sin x) (by fun_prop)
    (by intro x; convert (((((Real.hasDerivAt_cos x).sub_const 1).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub
      (((hasDerivAt_id x).pow 4).div_const 24)).add
      (((hasDerivAt_id x).pow 6).div_const 720)) using 1 <;> simp [id_eq] <;> ring)
    (by norm_num) (fun x hx => by linarith [profile_sin_upper5 hx]) hx
  linarith

/-- Degree-seven alternating sine bound, proved analytically from derivatives. -/
theorem profile_sin_lower7 {x : ℝ} (hx : 0 ≤ x) :
    x-x^3/6+x^5/120-x^7/5040 ≤ Real.sin x := by
  have hh := profile_nonneg_of_deriv
    (f := fun x => Real.sin x-x+x^3/6-x^5/120+x^7/5040)
    (f' := fun x => Real.cos x-1+x^2/2-x^4/24+x^6/720) (by fun_prop)
    (by intro x; convert (((((Real.hasDerivAt_sin x).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 3).div_const 6)).sub
      (((hasDerivAt_id x).pow 5).div_const 120)).add
      (((hasDerivAt_id x).pow 7).div_const 5040)) using 1 <;> simp [id_eq] <;> ring)
    (by norm_num) (fun x hx => by linarith [profile_cos_lower6 hx]) hx
  linarith

theorem general_profile_arcsin_enclosure :
    Real.arcsin (713/1000) < (793769/1000000:ℝ) := by
  apply (Real.arcsin_lt_iff_lt_sin (by norm_num)
    (show (793769/1000000:ℝ) ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_gt_three])).mpr
  have hh := profile_sin_lower7 (show (0:ℝ) ≤ 793769/1000000 by norm_num)
  norm_num at hh ⊢
  linarith

theorem general_profile_sqrt_enclosures :
    Real.sqrt (1-(713/1000:ℝ)^2) < 701165/1000000 ∧
    (999444/1000000:ℝ) < Real.sqrt (1-(1/30:ℝ)^2) := by
  constructor
  · apply (Real.sqrt_lt' (by norm_num)).mpr
    norm_num
  · apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num

/-- Exact angular primitive for the cubic, with a constant tail. -/
theorem general_profile_polynomial_integral (t : ℝ) :
    (∫ θ in (0:ℝ)..t, Real.sin θ*generalLowerPolynomial (Real.sin θ)) +
      (4137/1000)*Real.cos t =
      57/40+2*(47/20)/3+(83/80)*t+
        (4137/1000-57/40-2*(47/20)/3-(47/20)*Real.sin t^2/3-
          (23/10)*Real.sin t/2-(-3/10)*Real.sin t*(3+2*Real.sin t^2)/8)*Real.cos t := by
  have he : (fun θ => Real.sin θ*generalLowerPolynomial (Real.sin θ)) =
      (fun θ => (57/40)*Real.sin θ+(23/10)*Real.sin θ^2+
        (47/20)*Real.sin θ^3-(3/10)*Real.sin θ^4) := by
    funext θ
    unfold generalLowerPolynomial
    ring
  rw [he]
  have hi (n : ℕ) : IntervalIntegrable (fun θ => Real.sin θ^n) volume 0 t :=
    (Real.continuous_sin.pow n).intervalIntegrable _ _
  have hi1 : IntervalIntegrable Real.sin volume 0 t := Real.continuous_sin.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub
    ((hi1.const_mul _).add ((hi 2).const_mul _) |>.add ((hi 3).const_mul _))
    ((hi 4).const_mul _)]
  rw [intervalIntegral.integral_add
    ((hi1.const_mul _).add ((hi 2).const_mul _)) ((hi 3).const_mul _)]
  rw [intervalIntegral.integral_add (hi1.const_mul _) ((hi 2).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  have hm := profile_sin_moments t
  simp only [pow_one] at *
  rw [hm.1,hm.2.1,hm.2.2.1,hm.2.2.2]
  have hs := congrArg (fun u : ℝ => u*Real.cos t) (Real.sin_sq_add_cos_sq t)
  dsimp at hs
  nlinarith only [hs]

theorem generalLowerProfile_small_majorant {k : ℝ} (hk : k ∈ Icc (0:ℝ) 1) :
    generalLowerProfile k ≤ generalLowerPolynomial k+3/40 := by
  have hp := generalLowerPolynomial_mono (show (0:ℝ) ∈ Icc 0 1 by norm_num) hk hk.1
  norm_num [generalLowerPolynomial] at hp
  change _ ≤ generalLowerPolynomial k at hp
  unfold generalLowerProfile
  exact (min_le_right _ _).trans (max_le (by linarith) (by linarith))

theorem generalLowerProfile_polynomial_majorant {k : ℝ}
    (hk : k ∈ Icc (1/30:ℝ) 1) : generalLowerProfile k ≤ generalLowerPolynomial k := by
  have hp := generalLowerPolynomial_mono (show (1/30:ℝ) ∈ Icc 0 1 by norm_num)
    ⟨by linarith [hk.1],hk.2⟩ hk.1
  norm_num [generalLowerPolynomial] at hp
  change _ ≤ generalLowerPolynomial k at hp
  unfold generalLowerProfile
  exact (min_le_right _ _).trans (max_le (by linarith) le_rfl)

/-- Split the actual profile integral into its two polynomial pieces and its cap. -/
theorem generalLowerProfile_angularCost_majorant :
    profileAngularCost generalLowerProfile ≤
      57/40+2*(47/20)/3+(83/80)*Real.arcsin (713/1000)+
        (4137/1000-57/40-2*(47/20)/3-(47/20)*(713/1000)^2/3-
          (23/10)*(713/1000)/2-(-3/10)*(713/1000)*(3+2*(713/1000)^2)/8)*
          Real.sqrt (1-(713/1000)^2)+
        (3/40)*(1-Real.sqrt (1-(1/30)^2)) := by
  let a : ℝ := Real.arcsin (1/30)
  let b : ℝ := Real.arcsin (713/1000)
  have ha : 0 ≤ a := Real.arcsin_nonneg.mpr (by norm_num)
  have hab : a ≤ b := Real.arcsin_le_arcsin (by norm_num)
  have hb : b ≤ Real.pi/2 := Real.arcsin_le_pi_div_two _
  have hc : Continuous (fun θ => Real.sin θ*generalLowerProfile (Real.sin θ)) :=
    Real.continuous_sin.mul (generalLowerProfile_continuous.comp Real.continuous_sin)
  have hp : Continuous (fun θ => Real.sin θ*generalLowerPolynomial (Real.sin θ)) := by
    exact Real.continuous_sin.mul (generalLowerPolynomial_continuous.comp Real.continuous_sin)
  have hs : Continuous (fun θ => (3/40:ℝ)*Real.sin θ) := by fun_prop
  have ht : Continuous (fun θ => (4137/1000:ℝ)*Real.sin θ) := by fun_prop
  have hsin {x : ℝ} (hx : x ∈ Icc (0:ℝ) (Real.pi/2)) : Real.sin x ∈ Icc (0:ℝ) 1 :=
    ⟨Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos]),Real.sin_le_one x⟩
  have h1 := intervalIntegral.integral_mono_on (μ := volume) ha (hc.intervalIntegrable 0 a)
    ((hp.add hs).intervalIntegrable 0 a) (fun θ hθ => by
      have hθ' : θ ∈ Icc (0:ℝ) (Real.pi/2) := ⟨hθ.1,hθ.2.trans (hab.trans hb)⟩
      have hm := mul_le_mul_of_nonneg_left (generalLowerProfile_small_majorant (hsin hθ')) (hsin hθ').1
      nlinarith only [hm])
  have h2 := intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable a b)
    (hp.intervalIntegrable a b) (fun θ hθ => by
      have hθ' : θ ∈ Icc (0:ℝ) (Real.pi/2) := ⟨ha.trans hθ.1,hθ.2.trans hb⟩
      have hslo : (1/30:ℝ) ≤ Real.sin θ := by
        have hh := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos,ha]) hθ'.2 hθ.1
        have heq : Real.sin a = (1/30:ℝ) := Real.sin_arcsin (by norm_num) (by norm_num)
        rwa [heq] at hh
      exact mul_le_mul_of_nonneg_left (generalLowerProfile_polynomial_majorant ⟨hslo,(hsin hθ').2⟩) (hsin hθ').1)
  have h3 := intervalIntegral.integral_mono_on (μ := volume) hb (hc.intervalIntegrable b (Real.pi/2))
    (ht.intervalIntegrable b (Real.pi/2)) (fun θ hθ => by
      have hθ' : θ ∈ Icc (0:ℝ) (Real.pi/2) := ⟨(ha.trans hab).trans hθ.1,hθ.2⟩
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (generalLowerProfile_bounds (Real.sin θ)).2 (hsin hθ').1)
  rw [intervalIntegral.integral_add (μ := volume) (hp.intervalIntegrable 0 a) (hs.intervalIntegrable 0 a)] at h1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 b) (hc.intervalIntegrable b (Real.pi/2))
  have hpoly := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hp.intervalIntegrable 0 a) (hp.intervalIntegrable a b)
  have htail : (∫ θ in b..Real.pi/2, (4137/1000:ℝ)*Real.sin θ) = (4137/1000)*Real.cos b := by
    rw [intervalIntegral.integral_const_mul,integral_sin,Real.cos_pi_div_two,sub_zero]
  have hsmall : (∫ θ in (0:ℝ)..a, (3/40:ℝ)*Real.sin θ) = (3/40)*(1-Real.cos a) := by
    rw [intervalIntegral.integral_const_mul,integral_sin,Real.cos_zero]
  rw [htail] at h3
  rw [hsmall] at h1
  have hbound : profileAngularCost generalLowerProfile ≤
      (∫ θ in (0:ℝ)..b, Real.sin θ*generalLowerPolynomial (Real.sin θ))+
        (4137/1000)*Real.cos b+(3/40)*(1-Real.cos a) := by
    dsimp [profileAngularCost]
    linarith
  rw [general_profile_polynomial_integral] at hbound
  have heq : Real.sin b = (713/1000:ℝ) := Real.sin_arcsin (by norm_num) (by norm_num)
  rw [heq] at hbound
  simpa only [a,b,Real.cos_arcsin] using hbound

/-- The general profile has the printed strict correction coefficient. -/
theorem generalLowerProfile_angularCost_lt : profileAngularCost generalLowerProfile < 96/25 := by
  have hb := generalLowerProfile_angularCost_majorant
  have ha := general_profile_arcsin_enclosure
  have hr := general_profile_sqrt_enclosures
  have hq : (0:ℝ) < 4137/1000-57/40-2*(47/20)/3-(47/20)*(713/1000)^2/3-
      (23/10)*(713/1000)/2-(-3/10)*(713/1000)*(3+2*(713/1000)^2)/8 := by norm_num
  have hh := mul_lt_mul_of_pos_left hr.1 hq
  norm_num at hb hh hr ⊢
  nlinarith only [hb,ha,hh,hr.2]

/-- Elementary square-root majorant used in the endpoint cost. -/
theorem profile_sqrt_upper {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    Real.sqrt (1-y^2) ≤ 1-y^2/2-y^4/8 := by
  have hy2 : 0 ≤ y^2 := sq_nonneg y
  have hy2' : y^2 ≤ 1 := by nlinarith [hy.1,hy.2]
  have hy4 : y^4 ≤ 1 := by nlinarith [sq_nonneg (1-y^2)]
  have hpos : 0 ≤ 1-y^2/2-y^4/8 := by linarith
  apply (Real.sqrt_le_left hpos).mpr
  have h6 : 0 ≤ y^6 := by positivity
  have h8 : 0 ≤ y^8 := by positivity
  nlinarith only [h6,h8]

/-- The quarter-circle primitive, established by the sine substitution. -/
theorem profile_sqrt_integral {k : ℝ} (hk : k ∈ Icc (0:ℝ) 1) :
    (∫ y in (0:ℝ)..k, Real.sqrt (1-y^2)) =
      (Real.arcsin k+k*Real.sqrt (1-k^2))/2 := by
  let t := Real.arcsin k
  have ht0 : 0 ≤ t := Real.arcsin_nonneg.mpr hk.1
  have ht1 : t ≤ Real.pi/2 := Real.arcsin_le_pi_div_two _
  have heq : Real.sin t=k := Real.sin_arcsin (by linarith [hk.1]) hk.2
  have hc : Continuous (fun y : ℝ => Real.sqrt (1-y^2)) := by fun_prop
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0:ℝ)) (b := t) (g := fun y : ℝ => Real.sqrt (1-y^2))
    (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn hc
  rw [Real.sin_zero,heq] at hsub
  have hfun : (∫ x in (0:ℝ)..t, Real.sqrt (1-Real.sin x^2)*Real.cos x) =
      ∫ x in (0:ℝ)..t, Real.cos x^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ht0] at hx
    have hcos := Real.cos_nonneg_of_mem_Icc (show x ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    dsimp only
    rw [show 1-Real.sin x^2=Real.cos x^2 by nlinarith [Real.sin_sq_add_cos_sq x],Real.sqrt_sq hcos]
    ring
  change (∫ x in (0:ℝ)..t, Real.sqrt (1-Real.sin x^2)*Real.cos x) = _ at hsub
  rw [← hsub,hfun,integral_cos_sq]
  simp only [Real.sin_zero,Real.cos_zero,zero_mul,mul_zero,sub_zero,add_zero]
  rw [heq]
  simp only [t,Real.cos_arcsin]
  ring

/-- Exact evaluation of every linear capped profile, including both endpoints. -/
theorem profile_linearCap_angularCost {k : ℝ} (hk : k ∈ Icc (0:ℝ) 1) :
    profileAngularCost (fun y => min (2*y) (2*k)) =
      Real.arcsin k+k*Real.sqrt (1-k^2) := by
  let t := Real.arcsin k
  have ht0 : 0 ≤ t := Real.arcsin_nonneg.mpr hk.1
  have ht1 : t ≤ Real.pi/2 := Real.arcsin_le_pi_div_two _
  have heq : Real.sin t=k := Real.sin_arcsin (by linarith [hk.1]) hk.2
  have hc : Continuous (fun θ => Real.sin θ*min (2*Real.sin θ) (2*k)) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t (Real.pi/2))
  have h1 : (∫ θ in (0:ℝ)..t, Real.sin θ*min (2*Real.sin θ) (2*k)) =
      2*(∫ θ in (0:ℝ)..t, Real.sin θ^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le ht0] at hθ
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hθ.1,Real.pi_pos]) ht1 hθ.2
    rw [heq] at hh
    dsimp only
    rw [min_eq_left (by linarith)]
    ring
  have h2 : (∫ θ in t..Real.pi/2, Real.sin θ*min (2*Real.sin θ) (2*k)) =
      (2*k)*(∫ θ in t..Real.pi/2, Real.sin θ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le ht1] at hθ
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [ht0,Real.pi_pos]) hθ.2 hθ.1
    rw [heq] at hh
    dsimp only
    rw [min_eq_right (by linarith)]
    ring
  rw [h1,h2,integral_sin,Real.cos_pi_div_two,sub_zero,(profile_sin_moments t).2.1] at hsplit
  dsimp [profileAngularCost]
  rw [← hsplit,heq]
  simp only [t,Real.cos_arcsin]
  ring

theorem endpointLowerProfile_angularCost_eq :
    profileAngularCost endpointLowerProfile = Real.arcsin (73/100)+
      (73/100)*Real.sqrt (1-(73/100)^2) := by
  have h := profile_linearCap_angularCost (show (73/100:ℝ) ∈ Icc 0 1 by norm_num)
  change profileAngularCost (fun y => min (2*y) (73/50)) = _
  convert h using 2 <;> norm_num

theorem endpointLowerProfile_angularCost_lt : profileAngularCost endpointLowerProfile < 33/25 := by
  have hpoly : (∫ y in (0:ℝ)..(73/100), (1-y^2/2-y^4/8)) =
      (73/100:ℝ)-(73/100)^3/6-(73/100)^5/40 := by
    have hd (y : ℝ) : HasDerivAt (fun y : ℝ => y-y^3/6-y^5/40)
        (1-y^2/2-y^4/8) y := by
      convert ((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 3).div_const 6)).sub
        (((hasDerivAt_id y).pow 5).div_const 40) using 1 <;> simp [id_eq] <;> ring
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
      (show IntervalIntegrable (fun y : ℝ => 1-y^2/2-y^4/8) volume 0 (73/100) from
        (show Continuous (fun y : ℝ => 1-y^2/2-y^4/8) by fun_prop).intervalIntegrable _ _)
    simpa using hi
  have hm := intervalIntegral.integral_mono_on (μ := volume)
    (show (0:ℝ) ≤ 73/100 by norm_num)
    ((show Continuous (fun y : ℝ => Real.sqrt (1-y^2)) by fun_prop).intervalIntegrable 0 (73/100))
    ((show Continuous (fun y : ℝ => 1-y^2/2-y^4/8) by fun_prop).intervalIntegrable 0 (73/100))
    (fun y hy => profile_sqrt_upper ⟨hy.1,by linarith [hy.2]⟩)
  rw [hpoly,profile_sqrt_integral (by norm_num)] at hm
  rw [endpointLowerProfile_angularCost_eq]
  norm_num at hm ⊢
  linarith

/-- The printed integral side condition for the general mixed profile. -/
theorem generalLowerProfile_integral_condition :
    generalLowerProfile 1 ≤ 2*(∫ k in (0:ℝ)..1, generalLowerProfile k) := by
  have hfirst := intervalIntegral.integral_mono_on (μ := volume) (show (0:ℝ) ≤ 1/2 by norm_num)
    (continuous_const.intervalIntegrable 0 (1/2)) (generalLowerProfile_continuous.intervalIntegrable 0 (1/2))
    (fun k _ => (generalLowerProfile_bounds k).1)
  have hsecond := intervalIntegral.integral_mono_on (μ := volume) (show (1/2:ℝ) ≤ 1 by norm_num)
    (continuous_const.intervalIntegrable (1/2) 1) (generalLowerProfile_continuous.intervalIntegrable (1/2) 1)
    (fun k hk => show (3:ℝ) ≤ generalLowerProfile k from by
      have hh := generalLowerProfile_mono (show (1/2:ℝ) ∈ Icc 0 1 by norm_num)
        ⟨by linarith [hk.1],hk.2⟩ hk.1
      have heq : generalLowerProfile (1/2) = (25/8:ℝ) := by norm_num [generalLowerProfile,generalLowerPolynomial]
      rw [heq] at hh
      linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (generalLowerProfile_continuous.intervalIntegrable 0 (1/2))
    (generalLowerProfile_continuous.intervalIntegrable (1/2) 1)
  norm_num at hfirst hsecond
  have hb := (generalLowerProfile_bounds 1).2
  linarith

/-- The endpoint profile satisfies the integral side condition strictly. -/
theorem endpointLowerProfile_integral_condition :
    endpointLowerProfile 1 ≤ 2*(∫ k in (0:ℝ)..1, endpointLowerProfile k) := by
  have hpoint {k : ℝ} (hk : k ∈ Icc (0:ℝ) 1) : (73/50)*k ≤ endpointLowerProfile k := by
    unfold endpointLowerProfile
    exact le_min (by nlinarith [hk.1]) (by nlinarith [hk.2])
  have hm := intervalIntegral.integral_mono_on (μ := volume) (show (0:ℝ) ≤ 1 by norm_num)
    ((show Continuous (fun k : ℝ => (73/50)*k) by fun_prop).intervalIntegrable 0 1)
    (endpointLowerProfile_continuous.intervalIntegrable 0 1) (fun k hk => hpoint hk)
  rw [intervalIntegral.integral_const_mul,integral_id] at hm
  norm_num [endpointLowerProfile] at hm ⊢
  linarith

end
end SingularValueBounds.KL
