import SingularValueBounds.KL.Lower.ProfileIntegral
import Mathlib.MeasureTheory.Function.Jacobian

/-! Endpoint substitution and regularity for the actual mixed profiles. -/
open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1500000

def profileSingularCost (h : ℝ → ℝ) : ℝ :=
  ∫ k in (0:ℝ)..1, k*h k/Real.sqrt (1-k^2)

theorem profile_sin_image : Real.sin '' Ioo (0:ℝ) (Real.pi/2) = Ioo (0:ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    constructor
    · exact Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2,Real.pi_pos])
    · have hh := Real.strictMonoOn_sin
        (show x ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
        (show Real.pi/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos]) hx.2
      simpa using hh
  · intro hy
    refine ⟨Real.arcsin y,⟨Real.arcsin_pos.mpr hy.1,Real.arcsin_lt_pi_div_two.mpr hy.2⟩,?_⟩
    exact Real.sin_arcsin (by linarith [hy.1]) hy.2.le

theorem profile_sin_injective : InjOn Real.sin (Ioo (0:ℝ) (Real.pi/2)) := by
  apply Real.strictMonoOn_sin.injOn.mono
  intro x hx
  constructor <;> linarith [hx.1,hx.2,Real.pi_pos]

theorem profile_singular_substitution_point (h : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Ioo (0:ℝ) (Real.pi/2)) :
    |Real.cos x| • (Real.sin x*h (Real.sin x)/Real.sqrt (1-Real.sin x^2)) =
      Real.sin x*h (Real.sin x) := by
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
  rw [abs_of_pos hc,show 1-Real.sin x^2=Real.cos x^2 by nlinarith [Real.sin_sq_add_cos_sq x],Real.sqrt_sq hc.le]
  change Real.cos x*(Real.sin x*h (Real.sin x)/Real.cos x)=_
  field_simp

/-- Sine substitution handles the singular endpoint without assuming its integrability. -/
theorem profileSingularCost_eq_angularCost (h : ℝ → ℝ) :
    profileSingularCost h = profileAngularCost h := by
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x (_ : x ∈ Ioo (0:ℝ) (Real.pi/2)) => (Real.hasDerivAt_sin x).hasDerivWithinAt)
    profile_sin_injective (fun k => k*h k/Real.sqrt (1-k^2))
  rw [profile_sin_image] at hj
  have he : (∫ x in Ioo (0:ℝ) (Real.pi/2),
      |Real.cos x| • (Real.sin x*h (Real.sin x)/Real.sqrt (1-Real.sin x^2))) =
      ∫ x in Ioo (0:ℝ) (Real.pi/2), Real.sin x*h (Real.sin x) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    exact profile_singular_substitution_point h hx
  rw [he] at hj
  simpa only [profileSingularCost,profileAngularCost,intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_of_le Real.pi_div_two_pos.le,integral_Ioc_eq_integral_Ioo] using hj

/-- In particular the singular integrand is genuinely integrable for continuous profiles. -/
theorem profileSingularCost_integrable {h : ℝ → ℝ} (hc : Continuous h) :
    IntervalIntegrable (fun k => k*h k/Real.sqrt (1-k^2)) volume 0 1 := by
  have hj := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun x (_ : x ∈ Ioo (0:ℝ) (Real.pi/2)) => (Real.hasDerivAt_sin x).hasDerivWithinAt)
    profile_sin_injective (fun k => k*h k/Real.sqrt (1-k^2))
  rw [profile_sin_image] at hj
  have hi : IntegrableOn (fun x => Real.sin x*h (Real.sin x)) (Ioo (0:ℝ) (Real.pi/2)) := by
    apply ((Real.continuous_sin.mul (hc.comp Real.continuous_sin)).integrableOn_Icc).mono_set
    exact Ioo_subset_Icc_self
  have htrans : IntegrableOn (fun x => |Real.cos x| •
      (Real.sin x*h (Real.sin x)/Real.sqrt (1-Real.sin x^2))) (Ioo (0:ℝ) (Real.pi/2)) := by
    apply hi.congr
    apply (ae_restrict_mem measurableSet_Ioo).mono
    intro x hx
    exact (profile_singular_substitution_point h hx).symm
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  exact hj.mpr htrans

theorem generalLowerProfile_singularCost_lt : profileSingularCost generalLowerProfile < 96/25 := by
  rw [profileSingularCost_eq_angularCost]
  exact generalLowerProfile_angularCost_lt

theorem endpointLowerProfile_singularCost_lt : profileSingularCost endpointLowerProfile < 33/25 := by
  rw [profileSingularCost_eq_angularCost]
  exact endpointLowerProfile_angularCost_lt

theorem generalLowerPolynomial_hasDerivAt (x : ℝ) :
    HasDerivAt generalLowerPolynomial (23/10+(47/10)*x-(9/10)*x^2) x := by
  unfold generalLowerPolynomial
  convert! ((((hasDerivAt_const x (57/40)).add ((hasDerivAt_id x).const_mul (23/10))).add
    (((hasDerivAt_id x).pow 2).const_mul (47/20))).sub
    (((hasDerivAt_id x).pow 3).const_mul (3/10))) using 1 <;> simp [id_eq] <;> ring

/-- A single uniform Lipschitz bound covers the cubic and both clipping points. -/
theorem generalLowerPolynomial_lipschitzOn :
    LipschitzOnWith 8 generalLowerPolynomial (Icc (0:ℝ) 1) := by
  apply (convex_Icc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ => (generalLowerPolynomial_hasDerivAt x).hasDerivWithinAt)
  intro x hx
  have hx2 : x^2 ≤ 1 := by nlinarith [hx.1,hx.2]
  have hh : |23/10+(47/10)*x-(9/10)*x^2| ≤ (8:ℝ) := by
    apply abs_le.mpr
    constructor <;> nlinarith [hx.1,hx.2,sq_nonneg x]
  exact_mod_cast hh

theorem generalLowerProfile_lipschitzOn :
    LipschitzOnWith 8 generalLowerProfile (Icc (0:ℝ) 1) := by
  apply lipschitzOnWith_iff_restrict.mpr
  exact (generalLowerPolynomial_lipschitzOn.to_restrict.const_max (3/2)).const_min (4137/1000)

theorem endpointLowerProfile_lipschitz : LipschitzWith 2 endpointLowerProfile := by
  have hh' : LipschitzWith 2 (fun k : ℝ => 2*k) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq,← mul_sub,abs_mul]
    norm_num
  exact hh'.min_const (73/50)

/-- Strict monotonicity gives unambiguous cubic breakpoints, without radicals. -/
theorem generalLowerPolynomial_strictMono : StrictMonoOn generalLowerPolynomial (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hx2 : x^2 ≤ x := by nlinarith [hx.1,hx.2]
  have hy2 : y^2 ≤ y := by nlinarith [hy.1,hy.2]
  have hxy' : x*y ≤ x := by nlinarith [hx.1,hy.2]
  have hb : 0 < (23/10:ℝ)+47/20*(y+x)-3/10*(y^2+x*y+x^2) := by
    nlinarith [hx.1,hy.1]
  have hh := mul_pos (sub_pos.mpr hxy) hb
  unfold generalLowerPolynomial
  nlinarith only [hh]

/-- Both clipping levels have unique roots in the increasing cubic's domain. -/
theorem generalLowerProfile_breakpoints :
    (∃! k, k ∈ Icc (0:ℝ) 1 ∧ generalLowerPolynomial k=3/2) ∧
    (∃! k, k ∈ Icc (0:ℝ) 1 ∧ generalLowerPolynomial k=4137/1000) := by
  have hroot {v : ℝ} (hv : v ∈ Icc (57/40:ℝ) (231/40)) :
      ∃! k, k ∈ Icc (0:ℝ) 1 ∧ generalLowerPolynomial k=v := by
    have hv' : v ∈ Icc (generalLowerPolynomial 0) (generalLowerPolynomial 1) := by
      norm_num [generalLowerPolynomial] at *
      exact hv
    obtain ⟨k,hk,hkv⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num)
      generalLowerPolynomial_continuous.continuousOn hv'
    refine ⟨k,⟨hk,hkv⟩,?_⟩
    intro y hy
    exact generalLowerPolynomial_strictMono.injOn hy.1 hk (hy.2.trans hkv.symm)
  exact ⟨hroot (by norm_num),hroot (by norm_num)⟩

end
end SingularValueBounds.KL
