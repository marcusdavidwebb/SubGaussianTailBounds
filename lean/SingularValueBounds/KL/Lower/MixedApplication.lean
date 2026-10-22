import SingularValueBounds.KL.Barrier.MixedTransfer
import SingularValueBounds.KL.Barrier.MixedAngular
import SingularValueBounds.KL.Lower.FinalTransfer

/-! Application of the proved mixed-profile process to the two actual lower
row estimates. The only numerical premises are their finite certificates. -/
open MeasureTheory ProbabilityTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1400000

theorem profileAngularCost_const_mul (c : ℝ) (h : ℝ → ℝ) :
    profileAngularCost (fun k => c*h k) = c*profileAngularCost h := by
  unfold profileAngularCost
  calc
    _ = ∫ θ in (0:ℝ)..Real.pi/2, c*(Real.sin θ*h (Real.sin θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

private theorem scaled_general_profile_mono {c : ℝ} (hc : 0 ≤ c) :
    MonotoneOn (fun k => c*generalLowerProfile k) (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  exact mul_le_mul_of_nonneg_left (generalLowerProfile_mono hx hy hxy) hc

private theorem scaled_general_profile_integral_condition {c : ℝ} (hc : 0 ≤ c) :
    c*generalLowerProfile 1 ≤ 2*(∫ k in (0:ℝ)..1, c*generalLowerProfile k) := by
  rw [intervalIntegral.integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left generalLowerProfile_integral_condition hc
  nlinarith only [hh]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m n : ℕ} [NeZero n]

theorem lower_tail_general_of_certificates
    (hdata : GeneralLowerCertificateConditions)
    (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ) {K : ℝ} (hK : 1 ≤ K)
    (hindep : iIndepFun X μ) (hiso : ∀ i, CentredIsotropic μ (X i))
    (hsg : ∀ i, SubGaussianMGF μ (X i) K) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | smallestSingularValue (rowMatrix X ω) ≤
      LowerThreshold generalConstants m n K t} ≤ Real.exp (-t^2/2) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL : 0 < logParameter K := lt_of_lt_of_le zero_lt_one (one_le_logParameter hK)
  have hc0 : 0 < K^2*logParameter K := by positivity
  apply lower_tail_general_from_mixed_input hnm X hK generalLowerProfile_angularCost_pos
    generalLowerProfile_angularCost_lt.le ?_ ht
  intro b hb
  have hinput := mixedLowerTransferInput X (fun i => (hiso i).measurable) hindep
    (sq_nonneg K) (continuous_const.mul generalLowerProfile_continuous)
    (scaled_general_profile_mono hc0.le)
    (fun k _ => mul_nonneg hc0.le (generalLowerProfile_pos k).le)
    (fun k _ => mul_pos hc0 (generalLowerProfile_pos k))
    (scaled_general_profile_integral_condition hc0.le) hb
    ((499/100:ℝ)*K^2*logParameter K)
    (fun i => lower_mixed_row_general_of_certificates hdata (hsg i) (hiso i) hK)
  have hN : K^2*n+2*profileAngularCost
      (fun k => K^2*logParameter K*generalLowerProfile k)*Real.sqrt n =
      K^2*n+2*K^2*logParameter K*profileAngularCost generalLowerProfile*Real.sqrt n := by
    rw [profileAngularCost_const_mul]
    ring
  rw [hN] at hinput
  exact ⟨hinput⟩

theorem lower_tail_one_of_certificates
    (htable : Certificates.EndpointTableConditions) (hfar : Certificates.EndpointFarConditions)
    (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ)
    (hindep : iIndepFun X μ) (hiso : ∀ i, CentredIsotropic μ (X i))
    (hsg : ∀ i, SubGaussianMGF μ (X i) 1) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | smallestSingularValue (rowMatrix X ω) ≤
      LowerThreshold oneConstants m n 1 t} ≤ Real.exp (-t^2/2) := by
  apply lower_tail_one_from_mixed_input hnm X endpointLowerProfile_angularCost_pos
    endpointLowerProfile_angularCost_lt.le ?_ ht
  intro b hb
  have hinput := mixedLowerTransferInput X (fun i => (hiso i).measurable) hindep
    (show (0:ℝ) ≤ 1 by norm_num) endpointLowerProfile_continuous
    (endpointLowerProfile_mono.monotoneOn _)
    (fun k hk => endpointLowerProfile_nonneg hk.1)
    (fun k hk => endpointLowerProfile_pos hk.1)
    endpointLowerProfile_integral_condition hb (5/2)
    (fun i => lower_mixed_row_one_of_certificates htable hfar (hsg i) (hiso i))
  simpa only [one_mul] using (show Nonempty _ from ⟨hinput⟩)

end
end SingularValueBounds.KL
