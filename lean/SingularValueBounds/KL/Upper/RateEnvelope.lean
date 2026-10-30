import SingularValueBounds.KL.Upper.TailExtension

/-! # The monotone envelope for every rate below a tabulated rate (P16)
This is the continuous rescaling step of supplementary Lemma S1.7. A finite
certificate at a listed rate controls every smaller rate, not merely grid
points. -/
open Set
namespace SingularValueBounds.KL
noncomputable section

theorem upperRateF_rescaled {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) :
    upperRateF (r+1) (1+r*u) = upperRateRescaled r u := by
  have h1 : 0 < 1+r*u := by positivity
  have h2 : 0 < 1+u := by positivity
  have h3 : 0 < 1+r*u^2 := by positivity
  have hd : (1+r*u-1)^2+(r+1)-1 ≠ 0 := by nlinarith [sq_nonneg (r*u)]
  have he : (1+r*u)*(1+r*u+(r+1)-2)/((1+r*u-1)^2+(r+1)-1) =
      (1+r*u)*(1+u)/(1+r*u^2) := by
    field_simp [hd,h3.ne']
    ring
  unfold upperRateF upperRateRescaled
  rw [he, Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
  have hden : (1+r*u)*((r+1)-1) ≠ 0 := by simpa using mul_ne_zero h1.ne' hr.ne'
  field_simp [hden,h1.ne',hr.ne']
  ring

theorem upperRateF_envelope {vsmall vlarge C theta : ℝ}
    (hsmall : 1 < vsmall) (hlarge : vsmall ≤ vlarge)
    (hbound : ∀ theta ∈ Icc (1:ℝ) vlarge, upperRateF vlarge theta ≤ C)
    (htheta : theta ∈ Icc (1:ℝ) vsmall) : upperRateF vsmall theta ≤ C := by
  let u := (theta-1)/(vsmall-1)
  have hs : 0 < vsmall-1 := by linarith
  have hl : 0 < vlarge-1 := by linarith
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr htheta.1) hs.le
  have hu1 : u ≤ 1 := (div_le_one hs).2 (by linarith [htheta.2])
  have hid : 1+(vsmall-1)*u = theta := by dsimp [u]; field_simp <;> ring
  have hloc : 1+(vlarge-1)*u ∈ Icc (1:ℝ) vlarge := by
    constructor
    · nlinarith [mul_nonneg hl.le hu0]
    · nlinarith [mul_le_mul_of_nonneg_left hu1 hl.le]
  have hm := upperRateRescaled_mono hu0 hs.le hl.le (by linarith : vsmall-1 ≤ vlarge-1)
  change upperRateRescaled (vsmall-1) u ≤ upperRateRescaled (vlarge-1) u at hm
  have he1 := upperRateF_rescaled hs hu0
  have he2 := upperRateF_rescaled hl hu0
  rw [← he1, ← he2] at hm
  simp only [sub_add_cancel] at hm
  rw [hid] at hm
  exact hm.trans (hbound _ hloc)

end
end SingularValueBounds.KL
