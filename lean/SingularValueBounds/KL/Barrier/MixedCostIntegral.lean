import SingularValueBounds.KL.Barrier.MixedScalarCap
import SingularValueBounds.KL.Barrier.MixedInitialization
import SingularValueBounds.KL.Barrier.MixedAngular

/-! # Evaluation of the scalar mixed-cap budget integral -/
open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1800000

/-- Angular coordinates of the flat spectral shape. -/
def mixedInitialAngle (n : ℕ) : ℝ := Real.arcsin (1/Real.sqrt (n:ℝ))
def mixedAngularCoordinate (n : ℕ) (θ : ℝ) : ℝ := 1/(Real.sqrt (n:ℝ)*Real.cos θ)

lemma mixedInitialAngle_range {n : ℕ} (hn : 0<n) :
    mixedInitialAngle n ∈ Ioc (0:ℝ) (Real.pi/2) := by
  have hs := mixedInitialShape_mem hn
  exact ⟨Real.arcsin_pos.mpr hs.1,Real.arcsin_le_pi_div_two _⟩

lemma mixedInitialAngle_sin {n : ℕ} (hn : 0<n) :
    Real.sin (mixedInitialAngle n)=1/Real.sqrt (n:ℝ) := by
  have hs := mixedInitialShape_mem hn
  exact Real.sin_arcsin (by linarith [hs.1]) hs.2

lemma mixedInitialAngle_cos {n : ℕ} (hn : 0<n) :
    Real.cos (mixedInitialAngle n)=Real.sqrt (1-1/(n:ℝ)) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn0
  have hsq := Real.sq_sqrt hn0.le
  rw [mixedInitialAngle,Real.cos_arcsin]
  congr 1
  field_simp

lemma mixedAngularCoordinate_cos_pos {n : ℕ} (hn : 0<n) {θ : ℝ}
    (hθ : θ ∈ Icc (0:ℝ) (Real.pi/2-mixedInitialAngle n)) : 0<Real.cos θ := by
  have hφ := mixedInitialAngle_range hn
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1,Real.pi_pos],by linarith [hθ.2,hφ.1]⟩

lemma mixedAngularCoordinate_shape {n : ℕ} (hn : 0<n) {θ : ℝ}
    (hθ : θ ∈ Icc (0:ℝ) (Real.pi/2-mixedInitialAngle n)) :
    mixedShapeEnvelope n (mixedAngularCoordinate n θ)=Real.sin (θ+mixedInitialAngle n) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn0
  have hsq := Real.sq_sqrt hn0.le
  have hc := mixedAngularCoordinate_cos_pos hn hθ
  have ht0 := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by have hh := mixedInitialAngle_range hn; linarith [hθ.2,hh.1,Real.pi_pos])
  have harg : 1-1/((n:ℝ)*(mixedAngularCoordinate n θ)^2)=Real.sin θ^2 := by
    unfold mixedAngularCoordinate
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ,congrArg (fun z : ℝ => z*Real.cos θ^2) hsq]
  have hfirst : 1/((n:ℝ)*mixedAngularCoordinate n θ)=Real.cos θ/Real.sqrt (n:ℝ) := by
    unfold mixedAngularCoordinate
    field_simp
    nlinarith only [congrArg (fun z : ℝ => z*Real.cos θ) hsq]
  rw [mixedShapeEnvelope,harg,Real.sqrt_sq ht0,hfirst,Real.sin_add,
    mixedInitialAngle_sin hn,mixedInitialAngle_cos hn]
  ring

lemma mixedAngularCoordinate_hasDerivAt {n : ℕ} (hn : 0<n) {θ : ℝ}
    (hθ : θ ∈ Icc (0:ℝ) (Real.pi/2-mixedInitialAngle n)) :
    HasDerivAt (mixedAngularCoordinate n)
      (Real.sin θ/(Real.sqrt (n:ℝ)*Real.cos θ^2)) θ := by
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hc := mixedAngularCoordinate_cos_pos hn hθ
  convert (((Real.hasDerivAt_cos θ).const_mul (Real.sqrt (n:ℝ))).inv
    (mul_ne_zero hs.ne' hc.ne')) using 1
  · funext y
    simp [mixedAngularCoordinate,one_div,mul_comm]
  · field_simp
    ring

/-- Exact transformation of the scalar budget integral. It includes `n=1`
through the degenerate angular interval. -/
theorem mixedScalarCap_integral_eq {n : ℕ} (hn : 0<n) (a : ℝ)
    {h : ℝ → ℝ} (hc : Continuous h) :
    mixedScalarCap n a h 1+
      (∫ x in (1/Real.sqrt (n:ℝ))..1, 2*mixedScalarCap n a h x/x^3) =
      a*n+Real.sqrt (n:ℝ)*mixedAngularExpression h (mixedInitialAngle n) := by
  let φ := mixedInitialAngle n
  let T := Real.pi/2-φ
  have hφ := mixedInitialAngle_range hn
  have hT : 0 ≤ T := by dsimp [T,φ]; linarith [hφ.2]
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn0
  have hsq := Real.sq_sqrt hn0.le
  have hcoord0 : mixedAngularCoordinate n 0=1/Real.sqrt (n:ℝ) := by
    simp [mixedAngularCoordinate]
  have hcoordT : mixedAngularCoordinate n T=1 := by
    dsimp [mixedAngularCoordinate,T,φ]
    rw [Real.cos_pi_div_two_sub,mixedInitialAngle_sin hn]
    field_simp
  have hg : ContinuousOn (fun x => 2*mixedScalarCap n a h x/x^3)
      (mixedAngularCoordinate n '' uIcc (0:ℝ) T) := by
    rintro y ⟨θ,hθ,rfl⟩
    rw [uIcc_of_le hT] at hθ
    have ht : θ ∈ Icc (0:ℝ) (Real.pi/2-mixedInitialAngle n) := hθ
    have hcos := mixedAngularCoordinate_cos_pos hn ht
    have hx : 0 < mixedAngularCoordinate n θ := div_pos zero_lt_one (mul_pos hs hcos)
    have hpsi : ContinuousAt (mixedShapeEnvelope n) (mixedAngularCoordinate n θ) := by
      unfold mixedShapeEnvelope
      exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
        (mul_ne_zero hn0.ne' hx.ne')).add
        (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
          (continuousAt_const.sub (continuousAt_const.div
            (continuousAt_const.mul (continuousAt_id.pow 2))
            (mul_ne_zero hn0.ne' (pow_ne_zero 2 hx.ne'))))))
    have hcap : ContinuousAt (mixedScalarCap n a h) (mixedAngularCoordinate n θ) :=
      continuousAt_const.add (continuousAt_id.mul (hc.continuousAt.comp hpsi))
    exact ((continuousAt_const.mul hcap).div (continuousAt_id.pow 3)
      (pow_ne_zero 3 hx.ne')).continuousWithinAt
  have hd : ∀ θ ∈ uIcc (0:ℝ) T, HasDerivAt (mixedAngularCoordinate n)
      (Real.sin θ/(Real.sqrt (n:ℝ)*Real.cos θ^2)) θ := by
    intro θ hθ
    rw [uIcc_of_le hT] at hθ
    exact mixedAngularCoordinate_hasDerivAt hn hθ
  have hdc : ContinuousOn (fun θ => Real.sin θ/(Real.sqrt (n:ℝ)*Real.cos θ^2)) (uIcc (0:ℝ) T) := by
    intro θ hθ
    rw [uIcc_of_le hT] at hθ
    have hcos := mixedAngularCoordinate_cos_pos hn hθ
    exact (Real.continuous_sin.continuousAt.div
      (continuousAt_const.mul (Real.continuous_cos.continuousAt.pow 2))
      (mul_ne_zero hs.ne' (pow_ne_zero 2 hcos.ne'))).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv' hd hdc hg
  rw [hcoord0,hcoordT] at hsub
  have hpoint {θ : ℝ} (hθ : θ ∈ uIcc (0:ℝ) T) :
      (2*mixedScalarCap n a h (mixedAngularCoordinate n θ)/(mixedAngularCoordinate n θ)^3)*
        (Real.sin θ/(Real.sqrt (n:ℝ)*Real.cos θ^2)) =
      (2*a*(n:ℝ))*(Real.sin θ*Real.cos θ)+
        (2*Real.sqrt (n:ℝ))*(h (Real.sin (θ+φ))*Real.sin θ) := by
    rw [uIcc_of_le hT] at hθ
    have hcos := mixedAngularCoordinate_cos_pos hn hθ
    rw [mixedScalarCap,mixedAngularCoordinate_shape hn hθ]
    change (2*(a+mixedAngularCoordinate n θ*h (Real.sin (θ+φ)))/(mixedAngularCoordinate n θ)^3)*
        (Real.sin θ/(Real.sqrt (n:ℝ)*Real.cos θ^2)) = _
    unfold mixedAngularCoordinate
    generalize hsdef : Real.sqrt (n:ℝ)=s at *
    rw [← hsq]
    field_simp [hs.ne',hcos.ne']
    ring
  have hsub' : (∫ x in (1/Real.sqrt (n:ℝ))..1, 2*mixedScalarCap n a h x/x^3) =
      ∫ θ in (0:ℝ)..T, (2*a*(n:ℝ))*(Real.sin θ*Real.cos θ)+
        (2*Real.sqrt (n:ℝ))*(h (Real.sin (θ+φ))*Real.sin θ) := by
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact hpoint hθ
  have hi1 : Continuous (fun θ => (2*a*(n:ℝ))*(Real.sin θ*Real.cos θ)) := by fun_prop
  have hi2 : Continuous (fun θ => (2*Real.sqrt (n:ℝ))*(h (Real.sin (θ+φ))*Real.sin θ)) := by fun_prop
  rw [hsub',intervalIntegral.integral_add (hi1.intervalIntegrable _ _) (hi2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_sin_mul_cos₁,
    Real.sin_zero,zero_pow,sub_zero,mixedScalarCap_one hn]
  rw [mixedAngularExpression_eq_truncated hc]
  change a+h 1+((2*a*(n:ℝ))*(Real.sin T^2/2)+
      (2*Real.sqrt (n:ℝ))*(∫ θ in (0:ℝ)..T, h (Real.sin (θ+φ))*Real.sin θ)) =
    a*n+Real.sqrt (n:ℝ)*(h 1*Real.sin φ+
      2*(∫ θ in (0:ℝ)..T, h (Real.sin (θ+φ))*Real.sin θ))
  have hsinφ : Real.sin φ=1/Real.sqrt (n:ℝ) := mixedInitialAngle_sin hn
  have hsinT : Real.sin T=Real.cos φ := Real.sin_pi_div_two_sub φ
  rw [hsinφ,hsinT]
  have hid := Real.sin_sq_add_cos_sq φ
  rw [hsinφ] at hid
  field_simp [hs.ne'] at hid ⊢
  nlinarith only [congrArg (fun z : ℝ => a*z) hid]
  all_goals norm_num

/-- Dimension-independent scalar budget after the proved angular comparison. -/
theorem mixedScalarCap_integral_le {n : ℕ} (hn : 0<n) (a : ℝ)
    {h : ℝ → ℝ} (hc : Continuous h) (hm : MonotoneOn h (Icc (0:ℝ) 1))
    (hside : h 1 ≤ 2*(∫ k in (0:ℝ)..1,h k)) :
    mixedScalarCap n a h 1+
      (∫ x in (1/Real.sqrt (n:ℝ))..1, 2*mixedScalarCap n a h x/x^3) ≤
      a*n+2*Real.sqrt (n:ℝ)*profileAngularCost h := by
  rw [mixedScalarCap_integral_eq hn a hc]
  have hφ := mixedInitialAngle_range hn
  have hh := mul_le_mul_of_nonneg_left
    (mixedAngularExpression_le hc hm hside ⟨hφ.1.le,hφ.2⟩) (Real.sqrt_nonneg (n:ℝ))
  nlinarith only [hh]

end
end SingularValueBounds.KL
