import SingularValueBounds.KL.Lower.PlateauCertificates
import SingularValueBounds.KL.Lower.LogMGF

/-! # Comparison geometry for the two concentrated spectral ranges -/
open Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
open LowerCertificates
noncomputable section

def plateauA (k : ℝ) : ℝ := k+(7/10)*(1+(347/500)^2-k^2)/(2*(347/500))
def plateauV (A : ℝ) : ℝ := 1631/1000+((167/100-1631/1000)/(1211/1000-6/5))*(A-6/5)

theorem plateauA_bounds {k : ℝ} (hk : k ∈ Icc (71/100 : ℝ) (147/200)) :
    plateauA k ∈ Icc (6/5 : ℝ) (1211/1000) := by
  have hm {x y : ℝ} (hx : x ∈ Icc (71/100 : ℝ) (147/200))
      (hy : y ∈ Icc (71/100 : ℝ) (147/200)) (hxy : x ≤ y) : plateauA x ≤ plateauA y := by
    have hp : 0 ≤ 1-(7/10)*(x+y)/(2*(347/500)) := by norm_num [div_eq_mul_inv]; linarith [hx.2,hy.2]
    have hmul := mul_nonneg (sub_nonneg.mpr hxy) hp
    dsimp [plateauA]
    norm_num [div_eq_mul_inv] at hmul ⊢
    nlinarith only [hmul]
  have hl := hm (show (71/100 : ℝ) ∈ Icc (71/100 : ℝ) (147/200) by norm_num) hk hk.1
  have hh := hm hk (show (147/200 : ℝ) ∈ Icc (71/100 : ℝ) (147/200) by norm_num) hk.2
  norm_num [plateauA] at hl hh
  dsimp [plateauA]
  norm_num [div_eq_mul_inv] at hl hh ⊢
  exact ⟨by linarith,by linarith⟩

/-- The two-scale minimum has its maximum at the crossing point in this range. -/
theorem plateau_minimum_bound {k q z : ℝ} (hk : 0 < k) (hk1 : k ≤ 1)
    (hq : 0 ≤ q) (hthreshold : q*k ≤ Real.sqrt (1-k^2))
    (hz : z ∈ Icc (0 : ℝ) 1) :
    min k (Real.sqrt (1-z^2))+q*z ≤ k+q*Real.sqrt (1-k^2) := by
  let s := Real.sqrt (1-k^2)
  have hs : s^2=1-k^2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  by_cases hzs : z ≤ s
  · have hm := min_le_left k (Real.sqrt (1-z^2))
    nlinarith [mul_le_mul_of_nonneg_left hzs hq]
  · let y := Real.sqrt (1-z^2)
    have hy : y^2=1-z^2 := Real.sq_sqrt (by nlinarith [hz.1,hz.2])
    have hy0 : 0 ≤ y := Real.sqrt_nonneg _
    have hcs : k*y+s*z ≤ 1 := by
      have hnon : 0 ≤ k*y+s*z := add_nonneg (mul_nonneg hk.le hy0) (mul_nonneg hs0 hz.1)
      nlinarith [sq_nonneg (k*z-s*y)]
    have hp := mul_nonneg (show 0 ≤ s-q*k from sub_nonneg.mpr hthreshold)
      (show 0 ≤ z-s from sub_nonneg.mpr (le_of_not_ge hzs))
    have hm := min_le_right k y
    change min k y+q*z ≤ k+q*s
    nlinarith

/-- Actual near-range profile for the exact lower-shift comparison. -/
theorem plateau_near_profile {k : ℝ} (hk : k ∈ Icc (71/100 : ℝ) (147/200)) :
    LowerComparisonProfile k (plateauA k) (17/10) := by
  have hk0 : 0 < k := by linarith [hk.1]
  have hk1 : k ≤ 1 := by linarith [hk.2]
  have hs := Real.sq_sqrt (show 0 ≤ 1-k^2 by nlinarith [hk.1,hk.2])
  have hth : (7/10)*k ≤ Real.sqrt (1-k^2) := by
    nlinarith [Real.sqrt_nonneg (1-k^2),hk.1,hk.2]
  have ht : Real.sqrt (1-k^2) ≤ (1+(347/500)^2-k^2)/(2*(347/500)) := by
    norm_num [div_eq_mul_inv]
    nlinarith [sq_nonneg (Real.sqrt (1-k^2)-(347/500))]
  intro z hz0 hz1
  have hm := plateau_minimum_bound hk0 hk1 (by norm_num : (0:ℝ) ≤ 7/10) hth ⟨hz0,hz1⟩
  dsimp [plateauA]
  norm_num [div_eq_mul_inv] at ht ⊢
  nlinarith

/-- Constant far-range profile; Cauchy--Schwarz proves the tangent inequality. -/
theorem plateau_far_profile (k : ℝ) : LowerComparisonProfile k (74/55) (19/10) := by
  intro z hz0 hz1
  let y := Real.sqrt (1-z^2)
  have hy : y^2=1-z^2 := Real.sq_sqrt (by nlinarith)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hcs : y+(9/10)*z ≤ (74/55 : ℝ) := by
    nlinarith [sq_nonneg ((9/10)*y-z)]
  have hm := min_le_right k y
  change min k y+(19/10-1)*z ≤ 74/55
  linarith

/-- Interpolate the proved scalar log inequalities in their affine parameter A. -/
theorem plateau_near_scalar (h : PlateauCertificateConditions)
    {A r : ℝ} (hA : A ∈ Icc (6/5 : ℝ) (1211/1000))
    (hr : r ∈ Icc (0 : ℝ) (147/200)) :
    0 < 1-(1207/1000)*(r+A*r^2-(17/10)*r^3) ∧
      0 ≤ (1207/1000)*r+2*plateauV A*r^2-2*(26/25)*r^4+
        Real.log (1-(1207/1000)*(r+A*r^2-(17/10)*r^3)) := by
  have h0 := h.1.scalar (by norm_num; exact hr)
  have h1 := h.2.1.scalar (by norm_num; exact hr)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h0 h1
  let b := (A-6/5)/(1211/1000-6/5)
  let a := 1-b
  have hb : 0 ≤ b := by dsimp [b]; norm_num; linarith [hA.1]
  have ha : 0 ≤ a := by dsimp [a,b]; norm_num; linarith [hA.2]
  have hab : a+b=1 := by dsimp [a]; ring
  have hh := scalar_log_interpolation h0.1 h1.1 h0.2 h1.2 ha hb hab
  have hd : a*(1-(1207/1000)*(r+(6/5)*r^2-(17/10)*r^3))+
      b*(1-(1207/1000)*(r+(1211/1000)*r^2-(17/10)*r^3)) =
      1-(1207/1000)*(r+A*r^2-(17/10)*r^3) := by dsimp [a,b]; ring
  have hp : a*((1207/1000)*r+2*(1631/1000)*r^2-2*(26/25)*r^4)+
      b*((1207/1000)*r+2*(167/100)*r^2-2*(26/25)*r^4) =
      (1207/1000)*r+2*plateauV A*r^2-2*(26/25)*r^4 := by dsimp [a,b,plateauV]; ring
  rw [hd] at hh
  norm_num at hp
  rw [hp] at hh
  norm_num at hh ⊢
  exact hh

theorem plateau_far_scalar (h : PlateauCertificateConditions) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    0 < 1-(6/5)*(r+(74/55)*r^2-(19/10)*r^3) ∧
      0 ≤ (6/5)*r+2*(27/16)*r^2-2*(21/20)*r^4+
        Real.log (1-(6/5)*(r+(74/55)*r^2-(19/10)*r^3)) := by
  simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using h.2.2.scalar (by simpa using hr)

/-- Positive endpoint values of the concave quadratic give a strictly positive
comparison matrix in every normalized finite-dimensional spectrum. -/
theorem plateau_comparison_posDef {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R=1) {A c : ℝ}
    (hc : 0 ≤ c) (hendpoint : 0 < 1+A-c) : (lowerComparison R A c).PosDef := by
  rw [lowerComparison_spectral hR,normalized_trace_square hR hF,hF]
  apply unitary_conjugate_posDef
  apply Matrix.PosDef.diagonal
  intro i
  let r := hR.isHermitian.eigenvalues i
  have hr : 0 < r := hR.eigenvalues_pos i
  have hr1 : r ≤ 1 := (eigenvalue_le_spectralMaximum hR.isHermitian i).trans
    (by simpa only [hF] using spectralMaximum_le_frobenius hR.posSemidef)
  have hbase : 0 < 1+A*r-c*r^2 := by
    by_cases he : r=1
    · simpa only [he,one_pow,mul_one] using hendpoint
    · have hlt : r < 1 := lt_of_le_of_ne hr1 he
      have hp : 0 < (1-r)+r*(1+A-c)+c*r*(1-r) := by
        exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (sub_pos.mpr hlt)
          (mul_nonneg hr.le hendpoint.le))
          (mul_nonneg (mul_nonneg hc hr.le) (sub_nonneg.mpr hr1))
      nlinarith only [hp]
  change 0 < r+r^2/1*(A*1-c*r)
  convert mul_pos hr hbase using 1 <;> ring

end
end SingularValueBounds.KL
