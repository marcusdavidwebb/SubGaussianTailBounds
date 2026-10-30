import SingularValueBounds.KL.Upper.ExactTails
import SingularValueBounds.KL.Certificates.Enclosures

/-! # Upper-tail rates exceeding two (supplementary Lemma S1.7)
The rate correction is bounded by the finite degree-27 numerator using the
proved logarithm remainder rule. Numerical polynomial positivity is separate. -/
open Set Finset
open scoped BigOperators Matrix
namespace SingularValueBounds.KL
noncomputable section

/-- Scalar correction in Lemma S1.7. -/
def upperRateF (v theta : ℝ) : ℝ :=
  Real.log (theta*(theta+v-2)/((theta-1)^2+v-1)) -
    v*(theta-1)/(theta*(v-1))

/-- Equivalent coordinates used to compare two different rates. -/
def upperRateRescaled (r u : ℝ) : ℝ :=
  Real.log (1+u)+Real.log (1+r*u)-Real.log (1+r*u^2)-
    (r+1)*u/(1+r*u)

/-- Exact degree-27 expression of the externally checked polynomial. -/
def upperRateNumerator (v C y : ℝ) : ℝ :=
  let V := v*y
  let W := 2*y^2+v*y+2*v-2
  let A := (v-1)*(1+y)
  (C*A+v*y)*W^11*(W^2-V^2)-
    2*A*((∑ j ∈ range 6, V^(2*j+1)*W^(10-2*j)*(W^2-V^2)/(2*(j:ℝ)+1))+V^13/13)

/-- All logarithmic and cleared denominators have the required positive signs. -/
theorem upperRate_denominators {v y : ℝ} (hv : 1 < v) (hy : 0 ≤ y) :
    let V := v*y
    let W := 2*y^2+v*y+2*v-2
    let A := (v-1)*(1+y)
    0 < A ∧ 0 < W ∧ 0 ≤ V/W ∧ V/W < 1 ∧ 0 < A*W^11*(W^2-V^2) := by
  dsimp only
  have hv0 : 0 < v := by linarith
  have hA : 0 < (v-1)*(1+y) := mul_pos (by linarith) (by linarith)
  have hV : 0 ≤ v*y := mul_nonneg hv0.le hy
  have hW : 0 < 2*y^2+v*y+2*v-2 := by nlinarith [sq_nonneg y]
  have hWV : v*y < 2*y^2+v*y+2*v-2 := by nlinarith [sq_nonneg y]
  refine ⟨hA,hW,div_nonneg hV hW.le,(div_lt_one hW).2 hWV,?_⟩
  apply mul_pos (mul_pos hA (pow_pos hW _))
  nlinarith

/-- The logarithmic substitution behind the degree-27 certificate. -/
theorem upperRate_log_transform {v y : ℝ} (hv : 1 < v) (hy : 0 ≤ y) :
    upperRateF v (1+y) =
      Real.log ((1+(v*y)/(2*y^2+v*y+2*v-2))/(1-(v*y)/(2*y^2+v*y+2*v-2))) -
        v*y/((v-1)*(1+y)) := by
  have hd := upperRate_denominators hv hy
  have hW : 0 < 2*y^2+v*y+2*v-2 := hd.2.1
  have hbase : y^2+v-1 ≠ 0 := by nlinarith [sq_nonneg y]
  have hdiff : 2*y^2+v*y+2*v-2-v*y ≠ 0 := by nlinarith [sq_nonneg y]
  have he : (1+y)*(1+y+v-2)/(y^2+v-1) =
      (1+(v*y)/(2*y^2+v*y+2*v-2))/(1-(v*y)/(2*y^2+v*y+2*v-2)) := by
    have hquot : (1+(v*y)/(2*y^2+v*y+2*v-2))/(1-(v*y)/(2*y^2+v*y+2*v-2)) =
        ((2*y^2+v*y+2*v-2)+v*y)/((2*y^2+v*y+2*v-2)-v*y) := by
      rw [one_add_div hW.ne',one_sub_div hW.ne', div_div_div_cancel_right₀ hW.ne']
    rw [hquot]
    apply (div_eq_div_iff hbase hdiff).2
    ring
  unfold upperRateF
  simp only [add_sub_cancel_left]
  rw [he]
  congr 1
  ring

/-- The finite logarithm remainder is exactly represented by the printed
cleared numerator, not by an assumed analytic inequality. -/
theorem upperRateNumerator_identity {v C y : ℝ} (hv : 1 < v) (hy : 0 ≤ y) :
    C+v*y/((v-1)*(1+y))-
      Certificates.logTaylorUpper 6 ((v*y)/(2*y^2+v*y+2*v-2)) =
    upperRateNumerator v C y /
      (((v-1)*(1+y))*(2*y^2+v*y+2*v-2)^11*
        ((2*y^2+v*y+2*v-2)^2-(v*y)^2)) := by
  have hd := upperRate_denominators hv hy
  have hz : 0 < (2*y^2+v*y+2*v-2)^2-(v*y)^2 := by
    have hv0 : 0 < v := by linarith
    have hV : 0 ≤ v*y := by positivity
    have hW := hd.2.1
    have hWV : v*y < 2*y^2+v*y+2*v-2 := by nlinarith [sq_nonneg y]
    nlinarith
  have hgeneric (V W A B C : ℝ) (hW : W ≠ 0) (hA : A ≠ 0) (hZ : W^2-V^2 ≠ 0) :
      C+B/A-Certificates.logTaylorUpper 6 (V/W) =
      ((C*A+B)*W^11*(W^2-V^2)-2*A*((∑ j ∈ range 6,
        V^(2*j+1)*W^(10-2*j)*(W^2-V^2)/(2*(j:ℝ)+1))+V^13/13)) /
        (A*W^11*(W^2-V^2)) := by
    have hOne : 1-(V/W)^2 ≠ 0 := by
      have he : 1-(V/W)^2 = (W^2-V^2)/W^2 := by
        field_simp [hW] <;> ring
      rw [he]
      exact div_ne_zero hZ (pow_ne_zero 2 hW)
    have hDen : 1-(V/W)^2 = (W^2-V^2)/W^2 := by
      field_simp [hW] <;> ring
    unfold Certificates.logTaylorUpper Certificates.logTaylor
    norm_num only [Finset.sum_range_succ, pow_zero, pow_one, Nat.cast_zero,
      Nat.cast_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
    simp_rw [div_pow]
    simp only [div_pow] at hDen
    rw [hDen]
    field_simp [hW,hA,hZ] <;> ring
  exact hgeneric _ _ _ _ _ hd.2.1.ne' hd.1.ne' hz.ne'

/-- Whole-domain analytic consequence of a finite polynomial certificate. -/
theorem upperRateF_le_of_numerator {v C theta : ℝ} (hv : 1 < v) (htheta : 1 ≤ theta)
    (hp : 0 ≤ upperRateNumerator v C (theta-1)) : upperRateF v theta ≤ C := by
  have hy : 0 ≤ theta-1 := by linarith
  have hd := upperRate_denominators hv hy
  have hl := Certificates.log_ratio_le_logTaylorUpper 6 hd.2.2.1 hd.2.2.2.1
  have hi := upperRateNumerator_identity (C := C) hv hy
  have hn := div_nonneg hp hd.2.2.2.2.le
  have ht := upperRate_log_transform hv hy
  rw [show 1+(theta-1) = theta by ring] at ht
  rw [ht]
  simp only [show 1+(theta-1) = theta by ring] at hi hn
  linarith

/-- Derivative of the rate-rescaled correction: this sign is uniform on the
whole interval used to compare rates. -/
theorem upperRateRescaled_hasDerivAt {r u : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u) :
    HasDerivAt (fun r => upperRateRescaled r u)
      (r*u^2*(1-u)^2/((1+r*u)^2*(1+r*u^2))) r := by
  have hd : 0 < 1+r*u := by positivity
  have he : 0 < 1+r*u^2 := by positivity
  have h1 := ((hasDerivAt_const r (1:ℝ)).add ((hasDerivAt_id r).mul_const u)).log hd.ne'
  have h2 := ((hasDerivAt_const r (1:ℝ)).add ((hasDerivAt_id r).mul_const (u^2))).log he.ne'
  have h3 := (((hasDerivAt_id r).add_const 1).mul_const u).div
    ((hasDerivAt_const r (1:ℝ)).add ((hasDerivAt_id r).mul_const u)) hd.ne'
  simp only [Pi.add_apply, Pi.div_apply, id_eq, zero_add, one_mul] at h1 h2 h3
  convert! (((hasDerivAt_const r (Real.log (1+u))).add h1).sub h2).sub h3 using 1
  field_simp [hd.ne', he.ne'] <;> ring

/-- Increasing the allowed rate can only increase its rescaled correction. -/
theorem upperRateRescaled_mono {u : ℝ} (hu : 0 ≤ u) :
    MonotoneOn (fun r => upperRateRescaled r u) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro r hr
    exact (upperRateRescaled_hasDerivAt hr hu).continuousAt.continuousWithinAt
  · intro r hr
    exact (upperRateRescaled_hasDerivAt (interior_subset hr) hu).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [(upperRateRescaled_hasDerivAt (interior_subset hr) hu).deriv]
    have hr0 : 0 ≤ r := interior_subset hr
    positivity
/-- A third-derivative test for the quadratic rescaling used in Lemma S1.7.
The proof differentiates `x f''-f'`, then `x f'-2f`, then `f/x²`. -/
theorem quadratic_rescaling_of_third_deriv {f f1 f2 f3 : ℝ → ℝ} {b x : ℝ}
    (hb : 0 < b) (hx : 0 ≤ x) (hxb : x ≤ b) (hf0 : f 0 = 0) (hf10 : f1 0 = 0)
    (hf : ∀ t ∈ Icc 0 b,HasDerivAt f (f1 t) t)
    (hf1 : ∀ t ∈ Icc 0 b,HasDerivAt f1 (f2 t) t)
    (hf2 : ∀ t ∈ Icc 0 b,HasDerivAt f2 (f3 t) t)
    (hf3 : ∀ t ∈ Icc 0 b,0 ≤ f3 t) : f x ≤ (x/b)^2*f b := by
  let H := fun t => t*f2 t-f1 t
  let G := fun t => t*f1 t-2*f t
  have hH (t : ℝ) (ht : t ∈ Icc 0 b) : HasDerivAt H (t*f3 t) t := by
    convert! ((hasDerivAt_id t).mul (hf2 t ht)).sub (hf1 t ht) using 1 <;> simp [H] <;> ring
  have hHm : MonotoneOn H (Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hH t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hH t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hH t (interior_subset ht)).deriv]
      exact mul_nonneg (interior_subset ht).1 (hf3 t (interior_subset ht))
  have hH0 : H 0 = 0 := by simp [H,hf10]
  have hHpos (t : ℝ) (ht : t ∈ Icc 0 b) : 0 ≤ H t := by
    have ht0 := hHm ⟨le_rfl,hb.le⟩ ht ht.1
    rwa [hH0] at ht0
  have hG (t : ℝ) (ht : t ∈ Icc 0 b) : HasDerivAt G (H t) t := by
    convert! ((hasDerivAt_id t).mul (hf1 t ht)).sub ((hf t ht).const_mul 2) using 1 <;>
      simp [G,H] <;> ring
  have hGm : MonotoneOn G (Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hG t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hG t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hG t (interior_subset ht)).deriv]
      exact hHpos t (interior_subset ht)
  have hG0 : G 0 = 0 := by simp [G,hf0]
  have hGpos (t : ℝ) (ht : t ∈ Icc 0 b) : 0 ≤ G t := by
    have ht0 := hGm ⟨le_rfl,hb.le⟩ ht ht.1
    rwa [hG0] at ht0
  rcases hx.eq_or_lt with rfl | hx
  · simp [hf0]
  have hR (t : ℝ) (ht : t ∈ Icc x b) : HasDerivAt (fun t => f t/t^2) (G t/t^3) t := by
    have ht0 : 0 < t := hx.trans_le ht.1
    convert! (hf t ⟨ht0.le,ht.2⟩).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht0.ne') using 1
    dsimp [G]
    field_simp [ht0.ne'] <;> ring
  have hRm : MonotoneOn (fun t => f t/t^2) (Icc x b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hR t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hR t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hR t (interior_subset ht)).deriv]
      exact div_nonneg (hGpos t ⟨hx.le.trans (interior_subset ht).1,(interior_subset ht).2⟩)
        (pow_nonneg (hx.le.trans (interior_subset ht).1) _)
  have hr := hRm ⟨le_rfl,hxb⟩ ⟨hxb,le_rfl⟩ hxb
  have hh := (div_le_div_iff₀ (sq_pos_of_pos hx) (sq_pos_of_pos hb)).1 hr
  apply (le_div_iff₀ (sq_pos_of_pos hb)).2 at hh
  simpa only [div_pow,div_mul_eq_mul_div,mul_div_assoc,mul_comm] using hh

end
end SingularValueBounds.KL
