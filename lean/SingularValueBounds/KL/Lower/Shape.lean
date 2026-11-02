import SingularValueBounds.KL.Lower.Comparison
import SingularValueBounds.KL.Certificates.Polynomial

/-! # The lower spectral shape envelope (supplementary S1.4, P11)

The cubic critical-point argument is proved without a root-counting oracle:
an intermediate root is factored out, and the remaining quadratic is
negative throughout the interval by convexity.
-/
open Set Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 800000

def lowerJ (q : ℝ) : ℝ := -Real.log (1-q)-q
def lowerM (q : ℝ) : ℝ := q-2*(1-q)/q*lowerJ q
def lowerShapeEigenvalue (k r : ℝ) : ℝ := r+r^2*(k-r)

theorem lowerJ_pos {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : 0 < lowerJ q := by
  have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1-q)
    (by linarith : 1-q ≠ 1)
  dsimp [lowerJ]
  linarith

/-- A cubic with positive leading and constant coefficients, and negative
value at the right endpoint, has exactly the sign pattern needed here. -/
theorem cubic_one_crossing {A B C D k : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hk : 0 < k) (hkval : A+B*k+C*k^2+D*k^3 < 0) :
    ∃ r ∈ Ioo (0:ℝ) k,
      (∀ x ∈ Icc (0:ℝ) r, 0 ≤ A+B*x+C*x^2+D*x^3) ∧
      (∀ x ∈ Icc r k, A+B*x+C*x^2+D*x^3 ≤ 0) := by
  let p := fun x : ℝ => A+B*x+C*x^2+D*x^3
  have hp : Continuous p := by fun_prop
  have hp0 : 0 < p 0 := by simpa [p] using hA
  have hpk : p k < 0 := hkval
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc' hk.le hp.continuousOn ⟨hpk.le,hp0.le⟩
  have hr0 : 0 < r := by
    rcases hr.1.eq_or_lt with h | h
    · subst r; linarith
    · exact h
  have hrk : r < k := by
    rcases hr.2.eq_or_lt with h | h
    · subst r; linarith
    · exact h
  let E := C+D*r
  let F := B+C*r+D*r^2
  let q := fun x : ℝ => D*x^2+E*x+F
  have hfactor (x : ℝ) : p x = (x-r)*q x := by
    dsimp [p] at he
    dsimp [p,q,E,F]
    nlinarith only [he]
  have hF : F < 0 := by
    have h := hfactor 0
    dsimp [p,q] at h
    nlinarith
  have hqk : q k < 0 := by
    rw [hfactor] at hpk
    exact neg_of_mul_neg_right hpk (sub_pos.mpr hrk).le
  have hq (x : ℝ) (hx : x ∈ Icc (0:ℝ) k) : q x < 0 := by
    have hsq : x^2 ≤ k*x := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
    have hbound : q x ≤ F+(E+D*k)*x := by
      dsimp [q]
      nlinarith [mul_le_mul_of_nonneg_left hsq hD.le]
    by_cases hc : 0 ≤ E+D*k
    · have hc' := mul_le_mul_of_nonneg_left hx.2 hc
      dsimp [q] at hqk
      nlinarith
    · have hc' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hx.1
      linarith
  refine ⟨r,⟨hr0,hrk⟩,?_,?_⟩
  · intro x hx
    rw [show A+B*x+C*x^2+D*x^3 = p x from rfl,hfactor]
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx.2)
      (hq x ⟨hx.1,hx.2.trans hrk.le⟩).le
  · intro x hx
    rw [show A+B*x+C*x^2+D*x^3 = p x from rfl,hfactor]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1)
      (hq x ⟨hr0.le.trans hx.1,hx.2⟩).le

theorem lowerShapeEigenvalue_bounds {k r : ℝ} (hk1 : k ≤ 1)
    (hr : r ∈ Icc (0:ℝ) k) : 0 ≤ lowerShapeEigenvalue k r ∧ lowerShapeEigenvalue k r ≤ k := by
  have hr1 : r ≤ 1 := hr.2.trans hk1
  have hsq : 0 ≤ 1-r^2 := by nlinarith [hr.1]
  have hprod := mul_nonneg (sub_nonneg.mpr hr.2) hsq
  unfold lowerShapeEigenvalue
  constructor
  · exact add_nonneg hr.1 (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hr.2))
  · nlinarith

/-- Shape envelope under the two strict cubic endpoint signs. The concrete
moment cells establish those signs from the printed M/J inequalities. -/
theorem lower_shape_envelope_of_cubic {u k c : ℝ} (hu : 0 < u) (hk : 0 < k)
    (hk1 : k ≤ 1) (huk : u*k < 1) (hc : 0 < c)
    (hcdef : c*k^2 = lowerJ (u*k))
    (hleft : 0 < 2*c-u^2-2*u*k)
    (hright : (2*c-u^2-2*u*k)+(3*u-u^2*k-2*u*c)*k+
      (u^2-2*u*c*k)*k^2+2*u*c*k^3 < 0)
    {r : ℝ} (hr : r ∈ Icc (0:ℝ) k) :
    -Real.log (1-u*lowerShapeEigenvalue k r)-u*r ≤ c*r^2 := by
  let d := fun x => 1-u*lowerShapeEigenvalue k x
  let F := fun x => u*x+c*x^2+Real.log (d x)
  have hd (x : ℝ) (hx : x ∈ Icc (0:ℝ) k) : 0 < d x := by
    have h := (lowerShapeEigenvalue_bounds hk1 hx).2
    dsimp [d]
    nlinarith [mul_le_mul_of_nonneg_left h hu.le]
  have hderiv (x : ℝ) (hx : x ∈ Icc (0:ℝ) k) :
      HasDerivAt F
        (x/d x*((2*c-u^2-2*u*k)+(3*u-u^2*k-2*u*c)*x+
          (u^2-2*u*c*k)*x^2+2*u*c*x^3)) x := by
    have hb : HasDerivAt (lowerShapeEigenvalue k) (1+2*k*x-3*x^2) x := by
      convert! (hasDerivAt_id x).add (((hasDerivAt_id x).pow 2).mul
        ((hasDerivAt_const x k).sub (hasDerivAt_id x))) using 1 <;>
        simp <;> ring
    have hdd := (hasDerivAt_const x (1:ℝ)).sub (hb.const_mul u)
    convert! (((hasDerivAt_id x).const_mul u).add
      (((hasDerivAt_id x).pow 2).const_mul c)).add (hdd.log (hd x hx).ne') using 1
    norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    change x / d x * _ = u+c*(2*x)+(0-u*(1+2*k*x-3*x^2))/d x
    have hn := (hd x hx).ne'
    field_simp [hn]
    dsimp [d,lowerShapeEigenvalue]
    ring
  have hF0 : F 0 = 0 := by simp [F,d,lowerShapeEigenvalue]
  have hFk : F k = 0 := by
    dsimp [F,d,lowerShapeEigenvalue]
    simp only [sub_self,mul_zero,add_zero]
    dsimp [lowerJ] at hcdef
    linarith
  obtain ⟨turn,hturn,hpos,hneg⟩ := cubic_one_crossing hleft (by positivity : 0 < 2*u*c) hk hright
  have hmono : MonotoneOn F (Icc (0:ℝ) turn) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx
      exact (hderiv x ⟨hx.1,hx.2.trans hturn.2.le⟩).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x ⟨(interior_subset hx).1,(interior_subset hx).2.trans hturn.2.le⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hderiv x ⟨hx'.1,hx'.2.trans hturn.2.le⟩).deriv]
      exact mul_nonneg (div_nonneg hx'.1 (hd x ⟨hx'.1,hx'.2.trans hturn.2.le⟩).le) (hpos x hx')
  have hanti : AntitoneOn F (Icc turn k) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro x hx
      exact (hderiv x ⟨hturn.1.le.trans hx.1,hx.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x ⟨hturn.1.le.trans (interior_subset hx).1,(interior_subset hx).2⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hderiv x ⟨hturn.1.le.trans hx'.1,hx'.2⟩).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (hturn.1.le.trans hx'.1) (hd x ⟨hturn.1.le.trans hx'.1,hx'.2⟩).le) (hneg x hx')
  have hF : 0 ≤ F r := by
    by_cases hrt : r ≤ turn
    · have h := hmono ⟨le_rfl,hturn.1.le⟩ ⟨hr.1,hrt⟩ hr.1
      rwa [hF0] at h
    · have h := hanti ⟨(lt_of_not_ge hrt).le,hr.2⟩ ⟨hturn.2.le,le_rfl⟩ hr.2
      rwa [hFk] at h
  dsimp [F,d] at hF
  linarith

end
end SingularValueBounds.KL
