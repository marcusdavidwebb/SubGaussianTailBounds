import SingularValueBounds.KL.Lower.CellData
import SingularValueBounds.KL.Lower.HigherEntropy

/-! Real-domain monotonicity and enclosure interpretation for P11 cells. -/
open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

def generalLowerPolynomial (k : ℝ) : ℝ := 57/40+23/10*k+47/20*k^2-3/10*k^3
def generalLowerProfile (k : ℝ) : ℝ := min (4137/1000) (max (3/2) (generalLowerPolynomial k))
def momentD (k p : ℝ) : ℝ := 1+2*p*k^2-4*k^4
def momentB (k p : ℝ) : ℝ := 2*k^2+1/(p-2*k^2)
def momentLogM (k p : ℝ) : ℝ := Real.log (momentD k p)/(2*k^2)

theorem generalLowerPolynomial_mono : MonotoneOn generalLowerPolynomial (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hx2 : x^2 ≤ 1 := by nlinarith [hx.1,hx.2]
  have hy2 : y^2 ≤ 1 := by nlinarith [hy.1,hy.2]
  have hxy1 : x*y ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) hy.1]
  have hb : 0 ≤ (23/10:ℝ)+47/20*(y+x)-3/10*(y^2+x*y+x^2) := by nlinarith [hx.1,hy.1]
  have hh := mul_nonneg (sub_nonneg.mpr hxy) hb
  dsimp [generalLowerPolynomial]
  nlinarith

theorem generalLowerProfile_mono : MonotoneOn generalLowerProfile (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  exact min_le_min_left _ (max_le_max_left _ (generalLowerPolynomial_mono hx hy hxy))

theorem generalLowerProfile_bounds (k : ℝ) : (3/2:ℝ) ≤ generalLowerProfile k ∧
    generalLowerProfile k ≤ 4137/1000 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

@[simp] theorem cast_generalLowerProfileQ (k : ℚ) :
    (LowerCertificates.generalLowerProfileQ k:ℝ) = generalLowerProfile k := by
  simp [LowerCertificates.generalLowerProfileQ,generalLowerProfile,generalLowerPolynomial]

@[simp] theorem cast_momentDq (k p : ℚ) : (LowerCertificates.momentDq k p:ℝ) = momentD k p := by
  simp [LowerCertificates.momentDq,momentD]
@[simp] theorem cast_momentBq (k p : ℚ) : (LowerCertificates.momentBq k p:ℝ) = momentB k p := by
  simp [LowerCertificates.momentBq,momentB]

theorem momentD_gt_one {k p : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) (hp : (19:ℝ)/4 ≤ p) :
    1 < momentD k p := by
  have hk2 : k^2 ≤ 1 := by nlinarith
  have hb : 0 < p-2*k^2 := by linarith
  have hh := mul_pos (sq_pos_of_pos hk) hb
  dsimp [momentD]
  nlinarith

theorem momentB_mono {x y p : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1)
    (hp : (19:ℝ)/4 ≤ p) : momentB x p ≤ momentB y p := by
  have hy0 := hx.trans hxy
  have hy2 : y^2 ≤ 1 := by nlinarith
  have hx2 : x^2 ≤ y^2 := pow_le_pow_left₀ hx hxy 2
  have hd : 0 < p-2*y^2 := by linarith
  have hh := one_div_le_one_div_of_le hd (by linarith : p-2*y^2 ≤ p-2*x^2)
  dsimp [momentB]
  linarith

theorem momentLogM_antitone {p : ℝ} (hp : (19:ℝ)/4 ≤ p) :
    AntitoneOn (fun k => momentLogM k p) (Ioc (0:ℝ) 1) := by
  have hD (x : ℝ) (hx : x ∈ Ioc (0:ℝ) 1) : 0 < momentD x p :=
    (by linarith [momentD_gt_one hx.1 hx.2 hp])
  have hderiv (x : ℝ) (hx : x ∈ Ioc (0:ℝ) 1) :
      HasDerivAt (fun k => momentLogM k p)
        ((2*x^2*(p-4*x^2)-momentD x p*Real.log (momentD x p))/(x^3*momentD x p)) x := by
    have hd : HasDerivAt (fun k => momentD k p) (4*p*x-16*x^3) x := by
      convert! ((hasDerivAt_const x 1).add (((hasDerivAt_id x).pow 2).const_mul (2*p))).sub
        (((hasDerivAt_id x).pow 4).const_mul 4) using 1 <;> simp [momentD] <;> ring
    have h := (hd.log (hD x hx).ne').div (((hasDerivAt_id x).pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx.1.ne'))
    convert! h using 1
    simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    field_simp [hx.1.ne',(hD x hx).ne']
    <;> ring
  refine antitoneOn_of_deriv_nonpos (convex_Ioc _ _) ?_ ?_ ?_
  · intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hderiv x ⟨hx.1,hx.2.le⟩).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(hderiv x ⟨hx.1,hx.2.le⟩).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (mul_nonneg (pow_nonneg hx.1.le _) (hD x ⟨hx.1,hx.2.le⟩).le)
    have hd := hD x ⟨hx.1,hx.2.le⟩
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
    rw [Real.log_inv] at hl
    have hm := mul_le_mul_of_nonneg_left hl hd.le
    rw [mul_sub,mul_inv_cancel₀ hd.ne',mul_one] at hm
    dsimp [momentD] at *
    nlinarith [sq_nonneg (x^2)]

end
end SingularValueBounds.KL
