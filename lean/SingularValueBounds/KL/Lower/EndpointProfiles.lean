import SingularValueBounds.KL.Lower.EndpointMatrix
import SingularValueBounds.KL.Lower.EndpointCertificateBridges

/-! # Admissibility of the endpoint comparison profiles -/

open scoped BigOperators Matrix
namespace SingularValueBounds.KL
open Certificates
noncomputable section

theorem endpoint_tangent_profile (k : ℝ) {A c : ℝ}
    (hA0 : 0 ≤ A) (hc : 1 ≤ c) (hA : 1+(c-1)^2 ≤ A^2) :
    LowerComparisonProfile k A c := by
  intro z hz0 hz1
  have hzz : 0 ≤ 1-z^2 := by nlinarith
  have hs := Real.sq_sqrt hzz
  have hid : (Real.sqrt (1-z^2)+(c-1)*z)^2+
      ((c-1)*Real.sqrt (1-z^2)-z)^2 = 1+(c-1)^2 := by
    calc
      _ = (1+(c-1)^2)*((Real.sqrt (1-z^2))^2+z^2) := by ring
      _ = _ := by rw [hs]; ring
  have hc1 : 0 ≤ c-1 := sub_nonneg.mpr hc
  have hleft0 : 0 ≤ Real.sqrt (1-z^2)+(c-1)*z := by positivity
  have hle : Real.sqrt (1-z^2)+(c-1)*z ≤ A := by
    apply (sq_le_sq₀ hleft0 hA0).mp
    nlinarith only [hid,hA,sq_nonneg ((c-1)*Real.sqrt (1-z^2)-z)]
  have hm := min_le_right k (Real.sqrt (1-z^2))
  linarith

theorem endpoint_profile_convex {k A₁ A₂ c₁ c₂ θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h1 : LowerComparisonProfile k A₁ c₁) (h2 : LowerComparisonProfile k A₂ c₂) :
    LowerComparisonProfile k (θ*A₁+(1-θ)*A₂) (θ*c₁+(1-θ)*c₂) := by
  intro z hz0 hz1
  have hs := add_le_add (mul_le_mul_of_nonneg_left (h1 z hz0 hz1) hθ0)
    (mul_le_mul_of_nonneg_left (h2 z hz0 hz1) (sub_nonneg.mpr hθ1))
  convert! hs using 1 <;> ring

theorem endpoint_canonical_profile (k : ℝ) : LowerComparisonProfile k k 1 := by
  intro z _ _
  simp only [sub_self, zero_mul, add_zero]
  exact min_le_left _ _

theorem endpoint_blend_profile (k : ℝ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    LowerComparisonProfile k (θ*k+(1-θ)*(73/55)) (θ+(1-θ)*(103/55)) := by
  have ht : LowerComparisonProfile k (73/55) (103/55) :=
    endpoint_tangent_profile k (by norm_num) (by norm_num) (by norm_num)
  simpa only [mul_one] using endpoint_profile_convex hθ0 hθ1 (endpoint_canonical_profile k) ht

theorem endpoint_blend_parameters {k θ : ℝ}
    (hk0 : 0 ≤ k) (hk : k ≤ 7/9) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 < θ+(1-θ)*(103/55) ∧
      (θ*k+(1-θ)*(73/55))^2 ≤ θ+(1-θ)*(103/55) ∧
      k^2 ≤ endpointComparisonEigen (θ*k+(1-θ)*(73/55)) (θ+(1-θ)*(103/55)) k := by
  have hk1 : k ≤ 1 := by linarith
  have hc : 1 ≤ θ+(1-θ)*(103/55) := by nlinarith
  have hksq : k^2 ≤ 1 := by nlinarith
  have h1 := mul_nonneg hθ0 (sub_nonneg.mpr hksq)
  have h2 := mul_nonneg (sub_nonneg.mpr hθ1)
    (show (0 : ℝ) ≤ 103/55-(73/55)^2 by norm_num)
  have h3 := mul_nonneg (mul_nonneg hθ0 (sub_nonneg.mpr hθ1)) (sq_nonneg (k-73/55))
  have hAsq : (θ*k+(1-θ)*(73/55))^2 ≤ θ+(1-θ)*(103/55) := by
    nlinarith only [h1,h2,h3]
  have hkm : k^2 ≤ (4/5)*k := by nlinarith
  have ht : 0 ≤ 1+(73/55-1)*k-(103/55)*k^2 := by
    nlinarith only [hkm,hk]
  have hcan : 0 ≤ 1-k := by linarith
  have hb1 := mul_nonneg hθ0 hcan
  have hb2 := mul_nonneg (sub_nonneg.mpr hθ1) ht
  have hpoly : 0 ≤ 1+((θ*k+(1-θ)*(73/55))-1)*k-(θ+(1-θ)*(103/55))*k^2 := by
    nlinarith only [hb1,hb2]
  have hmul := mul_nonneg hk0 hpoly
  refine ⟨by linarith, hAsq, ?_⟩
  dsimp [endpointComparisonEigen]
  nlinarith only [hmul]

theorem endpoint_table_parameters (i : Fin 2) {k : ℝ}
    (hk0 : 0 ≤ k) (hk : k ≤ 7/9) :
    0 < (endpointC i : ℝ) ∧
      endpointTableA i k ^ 2 ≤ (endpointC i : ℝ) ∧
      k^2 ≤ endpointComparisonEigen (endpointTableA i k) (endpointC i) k ∧
      LowerComparisonProfile k (endpointTableA i k) (endpointC i) := by
  have hθ : 0 ≤ (endpointTheta i : ℝ) ∧ (endpointTheta i : ℝ) ≤ 1 := by
    fin_cases i <;> norm_num [endpointTheta]
  have hc : (endpointC i : ℝ) = (endpointTheta i : ℝ)+(1-(endpointTheta i : ℝ))*(103/55) := by
    fin_cases i <;> norm_num [endpointC,endpointTheta]
  have hb := endpoint_blend_parameters hk0 hk hθ.1 hθ.2
  have hp := endpoint_blend_profile k hθ.1 hθ.2
  rw [hc]
  exact ⟨hb.1,hb.2.1,hb.2.2,hp⟩

end
end SingularValueBounds.KL
