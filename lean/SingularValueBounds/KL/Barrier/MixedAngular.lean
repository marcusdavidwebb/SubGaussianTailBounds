import SingularValueBounds.KL.Lower.ProfileIntegral

/-! The angular comparison for mixed-profile correction budgets. Only
continuity and monotonicity of the profile are needed; its derivative is
never assumed. -/
open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

theorem profileAngularCost_pos {h : ℝ → ℝ} (hc : Continuous h)
    (hp : ∀ k ∈ Ioc (0:ℝ) 1, 0 < h k) : 0 < profileAngularCost h := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (((Real.continuous_sin).mul (hc.comp Real.continuous_sin)).intervalIntegrable _ _)
    (fun θ hθ => ?_) Real.pi_div_two_pos
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2,Real.pi_pos])
  exact mul_pos hs (hp _ ⟨hs,Real.sin_le_one _⟩)

theorem generalLowerProfile_angularCost_pos : 0 < profileAngularCost generalLowerProfile :=
  profileAngularCost_pos generalLowerProfile_continuous (fun k _ => generalLowerProfile_pos k)

theorem endpointLowerProfile_angularCost_pos : 0 < profileAngularCost endpointLowerProfile :=
  profileAngularCost_pos endpointLowerProfile_continuous
    (fun _ hk => endpointLowerProfile_pos hk.1)

def mixedAngularA (h : ℝ → ℝ) (φ : ℝ) : ℝ :=
  ∫ θ in φ..Real.pi/2, h (Real.sin θ)*Real.sin θ

def mixedAngularB (h : ℝ → ℝ) (φ : ℝ) : ℝ :=
  ∫ θ in φ..Real.pi/2, h (Real.sin θ)*Real.cos θ

def mixedAngularExpression (h : ℝ → ℝ) (φ : ℝ) : ℝ :=
  h 1*Real.sin φ+2*Real.cos φ*mixedAngularA h φ-2*Real.sin φ*mixedAngularB h φ

theorem mixedAngularA_hasDerivAt {h : ℝ → ℝ} (hc : Continuous h) (φ : ℝ) :
    HasDerivAt (mixedAngularA h) (-h (Real.sin φ)*Real.sin φ) φ := by
  have hf : Continuous (fun θ => h (Real.sin θ)*Real.sin θ) :=
    (hc.comp Real.continuous_sin).mul Real.continuous_sin
  simpa only [mixedAngularA, neg_mul] using
    intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable _ _)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt

theorem mixedAngularB_hasDerivAt {h : ℝ → ℝ} (hc : Continuous h) (φ : ℝ) :
    HasDerivAt (mixedAngularB h) (-h (Real.sin φ)*Real.cos φ) φ := by
  have hf : Continuous (fun θ => h (Real.sin θ)*Real.cos θ) :=
    (hc.comp Real.continuous_sin).mul Real.continuous_cos
  simpa only [mixedAngularB, neg_mul] using
    intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable _ _)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt

theorem mixedAngularExpression_hasDerivAt {h : ℝ → ℝ} (hc : Continuous h) (φ : ℝ) :
    HasDerivAt (mixedAngularExpression h)
      (h 1*Real.cos φ-2*Real.sin φ*mixedAngularA h φ-
        2*Real.cos φ*mixedAngularB h φ) φ := by
  convert (((Real.hasDerivAt_sin φ).const_mul (h 1)).add
    (((Real.hasDerivAt_cos φ).const_mul 2).mul (mixedAngularA_hasDerivAt hc φ))).sub
    (((Real.hasDerivAt_sin φ).const_mul 2).mul (mixedAngularB_hasDerivAt hc φ)) using 1 <;>
    dsimp [mixedAngularExpression] <;> ring

theorem mixedAngularB_zero {h : ℝ → ℝ} (hc : Continuous h) :
    mixedAngularB h 0 = ∫ k in (0:ℝ)..1, h k := by
  simpa only [mixedAngularB, Function.comp_apply, Real.sin_zero, Real.sin_pi_div_two] using
    intervalIntegral.integral_comp_mul_deriv (a := (0:ℝ)) (b := Real.pi/2)
      (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn hc

theorem mixedAngularA_lower {h : ℝ → ℝ} (hc : Continuous h)
    (hm : MonotoneOn h (Icc (0:ℝ) 1)) {φ : ℝ} (hφ : φ ∈ Icc (0:ℝ) (Real.pi/2)) :
    h (Real.sin φ)*Real.cos φ ≤ mixedAngularA h φ := by
  have hsφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 (by linarith [hφ.2,Real.pi_pos])
  have hf : Continuous (fun θ => h (Real.sin θ)*Real.sin θ) :=
    (hc.comp Real.continuous_sin).mul Real.continuous_sin
  have hg : Continuous (fun θ => h (Real.sin φ)*Real.sin θ) := continuous_const.mul Real.continuous_sin
  have hh := intervalIntegral.integral_mono_on (μ := volume) hφ.2 (hg.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _) (fun θ hθ => by
      have hsθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi
        (hφ.1.trans hθ.1) (by linarith [hθ.2,Real.pi_pos])
      exact mul_le_mul_of_nonneg_right
        (hm ⟨hsφ,Real.sin_le_one _⟩ ⟨hsθ,Real.sin_le_one _⟩
          (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hφ.1,Real.pi_pos]) hθ.2 hθ.1)) hsθ)
  simpa only [intervalIntegral.integral_const_mul, integral_sin, Real.cos_pi_div_two,
    sub_zero, mixedAngularA] using hh

theorem mixedAngularB_initial_upper {h : ℝ → ℝ} (hc : Continuous h)
    (hm : MonotoneOn h (Icc (0:ℝ) 1)) {φ : ℝ} (hφ : φ ∈ Icc (0:ℝ) (Real.pi/2)) :
    (∫ θ in (0:ℝ)..φ, h (Real.sin θ)*Real.cos θ) ≤ h (Real.sin φ)*Real.sin φ := by
  have hsφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 (by linarith [hφ.2,Real.pi_pos])
  have hf : Continuous (fun θ => h (Real.sin θ)*Real.cos θ) :=
    (hc.comp Real.continuous_sin).mul Real.continuous_cos
  have hg : Continuous (fun θ => h (Real.sin φ)*Real.cos θ) := continuous_const.mul Real.continuous_cos
  have hh := intervalIntegral.integral_mono_on (μ := volume) hφ.1 (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _) (fun θ hθ => by
      have hsθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2,hφ.2,Real.pi_pos])
      have hcθ : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],hθ.2.trans hφ.2⟩
      exact mul_le_mul_of_nonneg_right
        (hm ⟨hsθ,Real.sin_le_one _⟩ ⟨hsφ,Real.sin_le_one _⟩
          (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hθ.1,Real.pi_pos]) hφ.2 hθ.2)) hcθ)
  simpa only [intervalIntegral.integral_const_mul, integral_cos, Real.sin_zero,
    sub_zero] using hh

theorem mixedAngularExpression_antitone {h : ℝ → ℝ} (hc : Continuous h)
    (hm : MonotoneOn h (Icc (0:ℝ) 1))
    (hside : h 1 ≤ 2*(∫ k in (0:ℝ)..1, h k)) :
    AntitoneOn (mixedAngularExpression h) (Icc (0:ℝ) (Real.pi/2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (show Continuous (mixedAngularExpression h) from
      continuous_iff_continuousAt.mpr (fun φ => (mixedAngularExpression_hasDerivAt hc φ).continuousAt)).continuousOn
    (fun φ _ => (mixedAngularExpression_hasDerivAt hc φ).hasDerivWithinAt)
  intro φ hφ
  have hφ' : φ ∈ Icc (0:ℝ) (Real.pi/2) := interior_subset hφ
  have hs : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ'.1 (by linarith [hφ'.2,Real.pi_pos])
  have hcφ : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ'.1,Real.pi_pos],hφ'.2⟩
  have ha := mul_le_mul_of_nonneg_left (mixedAngularA_lower hc hm hφ') hs
  have hb := mul_le_mul_of_nonneg_left (mixedAngularB_initial_upper hc hm hφ') hcφ
  have hf : Continuous (fun θ => h (Real.sin θ)*Real.cos θ) :=
    (hc.comp Real.continuous_sin).mul Real.continuous_cos
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 φ) (hf.intervalIntegrable φ (Real.pi/2))
  change (∫ θ in (0:ℝ)..φ, h (Real.sin θ)*Real.cos θ)+mixedAngularB h φ = mixedAngularB h 0 at hsplit
  have hside' := mul_le_mul_of_nonneg_left hside hcφ
  rw [← mixedAngularB_zero hc] at hside'
  nlinarith

theorem mixedAngularExpression_le {h : ℝ → ℝ} (hc : Continuous h)
    (hm : MonotoneOn h (Icc (0:ℝ) 1))
    (hside : h 1 ≤ 2*(∫ k in (0:ℝ)..1, h k))
    {φ : ℝ} (hφ : φ ∈ Icc (0:ℝ) (Real.pi/2)) :
    mixedAngularExpression h φ ≤ 2*profileAngularCost h := by
  have hh := mixedAngularExpression_antitone hc hm hside
    (show (0:ℝ) ∈ Icc (0:ℝ) (Real.pi/2) by constructor; rfl; positivity) hφ hφ.1
  simpa only [mixedAngularExpression, Real.sin_zero, Real.cos_zero, mul_zero, zero_add,
    mul_one, zero_mul, sub_zero, mixedAngularA, profileAngularCost, mul_comm, one_mul] using hh

theorem mixedAngularExpression_eq_truncated {h : ℝ → ℝ} (hc : Continuous h) (φ : ℝ) :
    mixedAngularExpression h φ = h 1*Real.sin φ+
      2*(∫ θ in (0:ℝ)..Real.pi/2-φ, h (Real.sin (θ+φ))*Real.sin θ) := by
  have hshift : (∫ θ in (0:ℝ)..Real.pi/2-φ, h (Real.sin (θ+φ))*Real.sin θ) =
      ∫ θ in φ..Real.pi/2, h (Real.sin θ)*Real.sin (θ-φ) := by
    simpa only [zero_add, sub_add_cancel, add_sub_cancel_right] using
      (intervalIntegral.integral_comp_add_right
        (fun θ => h (Real.sin θ)*Real.sin (θ-φ)) φ
        (a := (0:ℝ)) (b := Real.pi/2-φ))
  have ha : Continuous (fun θ => (h (Real.sin θ)*Real.sin θ)*Real.cos φ) := by fun_prop
  have hb : Continuous (fun θ => (h (Real.sin θ)*Real.cos θ)*Real.sin φ) := by fun_prop
  have hi : (∫ θ in φ..Real.pi/2, h (Real.sin θ)*Real.sin (θ-φ)) =
      mixedAngularA h φ*Real.cos φ-mixedAngularB h φ*Real.sin φ := by
    calc
      _ = ∫ θ in φ..Real.pi/2,
          (h (Real.sin θ)*Real.sin θ)*Real.cos φ-
            (h (Real.sin θ)*Real.cos θ)*Real.sin φ := by
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only
        rw [Real.sin_sub]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _),
          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
        rfl
  rw [hshift,hi,mixedAngularExpression]
  ring

theorem angular_truncation_bound {h : ℝ → ℝ} (hc : Continuous h)
    (hm : MonotoneOn h (Icc (0:ℝ) 1))
    (hside : h 1 ≤ 2*(∫ k in (0:ℝ)..1, h k))
    {φ : ℝ} (hφ : φ ∈ Icc (0:ℝ) (Real.pi/2)) :
    h 1*Real.sin φ+2*(∫ θ in (0:ℝ)..Real.pi/2-φ,
      h (Real.sin (θ+φ))*Real.sin θ) ≤ 2*profileAngularCost h := by
  rw [← mixedAngularExpression_eq_truncated hc]
  exact mixedAngularExpression_le hc hm hside hφ

end
end SingularValueBounds.KL
