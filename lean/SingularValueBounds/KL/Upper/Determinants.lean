import SingularValueBounds.KL.Upper.Comparison
import SingularValueBounds.KL.Certificates.Enclosures

/-! # Determinant scalar majorants (supplementary S1.6.2)
The rational Padé upper bound is proved on its complete domain `z<1`,
including negative `z`. Finite Bernstein certificates enter only for the
polynomial comparisons with the six prescribed majorants. -/
open Set
open scoped BigOperators Matrix
namespace SingularValueBounds.KL
noncomputable section

/-- Common denominator in `eq:app-up-scalar-logdet`. -/
def upperPadeD (z : ℝ) : ℝ :=
  1 - (16/7)*z + (12/7)*z^2 - (16/35)*z^3 + (1/35)*z^4

/-- Common numerator in `eq:app-up-scalar-logdet`. -/
def upperPadeN (z : ℝ) : ℝ :=
  z - (25/14)*z^2 + (19/21)*z^3 - (47/420)*z^4

/-- The denominator factorisation proves positivity throughout the valid domain. -/
theorem upperPadeD_pos {z : ℝ} (hz : z < 1) : 0 < upperPadeD z := by
  have he : upperPadeD z = (1-z)/35 *
      (4+18*(1-z)+12*(1-z)^2+(1-z)^3) := by unfold upperPadeD; ring
  rw [he]
  have hz0 : 0 < 1-z := by linarith
  positivity

private theorem upperPade_deriv {z : ℝ} (hz : z < 1) :
    HasDerivAt (fun z => upperPadeN z / upperPadeD z + Real.log (1-z))
      (z^7 / (1225 * upperPadeD z^2)) z := by
  have hn : HasDerivAt upperPadeN
      (1-(25/7)*z+(19/7)*z^2-(47/105)*z^3) z := by
    convert (((hasDerivAt_id z).sub (((hasDerivAt_id z).pow 2).const_mul (25/14))).add
      (((hasDerivAt_id z).pow 3).const_mul (19/21))).sub
      (((hasDerivAt_id z).pow 4).const_mul (47/420)) using 1 <;>
      simp [upperPadeN] <;> ring
  have hd : HasDerivAt upperPadeD
      (-(16/7)+(24/7)*z-(48/35)*z^2+(4/35)*z^3) z := by
    convert ((((hasDerivAt_const z (1:ℝ)).sub ((hasDerivAt_id z).const_mul (16/7))).add
      (((hasDerivAt_id z).pow 2).const_mul (12/7))).sub
      (((hasDerivAt_id z).pow 3).const_mul (16/35))).add
      (((hasDerivAt_id z).pow 4).const_mul (1/35)) using 1 <;>
      simp [upperPadeD] <;> ring
  convert (hn.div hd (upperPadeD_pos hz).ne').add
    (((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).log (by linarith : 1-z ≠ 0)) using 1
  have hDn := (upperPadeD_pos hz).ne'
  have hzn : 1-z ≠ 0 := by linarith
  simp only [id_eq]
  field_simp only [hDn,hzn]
  unfold upperPadeD upperPadeN
  ring

/-- The common Padé majorant, valid on both sides of zero. -/
theorem neg_log_one_sub_le_upperPade {z : ℝ} (hz : z < 1) :
    -Real.log (1-z) ≤ upperPadeN z / upperPadeD z := by
  let f := fun z => upperPadeN z / upperPadeD z + Real.log (1-z)
  have hf (x : ℝ) (hx : x < 1) : HasDerivAt f (x^7 / (1225 * upperPadeD x^2)) x :=
    upperPade_deriv hx
  have hf0 : f 0 = 0 := by simp [f, upperPadeN, upperPadeD]
  by_cases hz0 : 0 ≤ z
  · have hm : MonotoneOn f (Icc 0 z) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · intro x hx
        exact (hf x (hx.2.trans_lt hz)).continuousAt.continuousWithinAt
      · intro x hx
        exact (hf x ((interior_subset hx).2.trans_lt hz)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hf x ((interior_subset hx).2.trans_lt hz)).deriv]
        exact div_nonneg (pow_nonneg (interior_subset hx).1 _) (by positivity)
    have hh := hm ⟨le_rfl,hz0⟩ ⟨hz0,le_rfl⟩ hz0
    rw [hf0] at hh
    dsimp [f] at hh
    linarith
  · have hz0 : z ≤ 0 := le_of_not_ge hz0
    have hm : AntitoneOn f (Icc z 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · intro x hx
        exact (hf x (by linarith [hx.2])).continuousAt.continuousWithinAt
      · intro x hx
        exact (hf x (by linarith [(interior_subset hx).2])).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hf x (by linarith [(interior_subset hx).2])).deriv]
        exact div_nonpos_of_nonpos_of_nonneg (Odd.pow_nonpos (by decide : Odd 7) (interior_subset hx).2)
          (by positivity)
    have hh := hm ⟨le_rfl,hz0⟩ ⟨hz0,le_rfl⟩ hz0
    rw [hf0] at hh
    dsimp [f] at hh
    linarith

/-- The normalized comparison eigenvalue. -/
def upperComparisonZ (a x : ℝ) : ℝ := 2 * (x+a*x^2-2*x^3)

/-- Every one of the six printed rectangles lies in the Padé domain. -/
theorem upperComparisonZ_lt_one {a x : ℝ} (ha : a ≤ 5/6) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    upperComparisonZ a x < 1 := by
  have hax := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg x)
  have hf : x+(5/6)*x^2-2*x^3 ≤ 17/36 := by
    by_cases hh : x ≤ 1/2
    · have hx2 : x^2 ≤ 1/4 := by nlinarith
      have hb : 0 ≤ 11/12-x/6-2*x^2 := by nlinarith
      have hp := mul_nonneg (show 0 ≤ 1/2-x by linarith) hb
      nlinarith
    · have hu : 0 ≤ x-1/2 := by linarith
      have hcube : 0 ≤ (x-1/2)^3 := pow_nonneg hu _
      nlinarith [sq_nonneg (x-1/2-1/12),sq_nonneg (x-1/2)]
  unfold upperComparisonZ
  nlinarith

/-- The six coefficient functions `B_i`. -/
def upperMajorantB (i : Fin 6) (a : ℝ) : ℝ :=
  match i.val with
  | 0 => 13/6
  | 1 => 13/6-4*(a-1/4)^2
  | 2 => 13/5
  | 3 => 13/6-4*(a-1/4)^2-1/30
  | 4 => 13/6-1/40
  | _ => let v := a-7/20; 413/200-(1339/1000)*v-(10009/1000)*v^2-(25197/1000)*v^3

/-- The six coefficient functions `A_i`. -/
def upperMajorantA (i : Fin 6) (a : ℝ) : ℝ :=
  match i.val with
  | 0 => 1+9*a
  | 1 => 20*a-2
  | 2 => 24*a-22/3
  | 3 => 20*a-2
  | 4 => 1+9*a
  | _ => let v := a-7/20; 816/125+(7307/200)*v+(9971/100)*v^2+(18903/250)*v^3

def upperMajorantH (i : Fin 6) (a x : ℝ) : ℝ :=
  2*x+upperMajorantB i a*x^2-upperMajorantA i a*x^2*(x-a)

/-- Interprets a nonnegative cleared polynomial, rather than assuming the
analytic logarithmic inequality as a certificate. -/
theorem upper_scalar_majorant_of_polynomial (i : Fin 6) {a x : ℝ}
    (hz : upperComparisonZ a x < 1)
    (hpoly : 0 ≤ upperMajorantH i a x * upperPadeD (upperComparisonZ a x) -
      upperPadeN (upperComparisonZ a x)) :
    -Real.log (1-upperComparisonZ a x) ≤ upperMajorantH i a x := by
  apply (neg_log_one_sub_le_upperPade hz).trans
  exact (div_le_iff₀ (upperPadeD_pos hz)).2 (by linarith)

/-- Summation cancels the cubic correction in every one of the six scalar
majorants, exactly as in the printed determinant argument. -/
theorem upperMajorantH_sum {ι : Type*} [Fintype ι] (i : Fin 6) (x : ι → ℝ)
    (hnorm : ∑ j, x j^2 = 1) :
    (∑ j, upperMajorantH i (∑ k, x k^3) (x j)) =
      2*(∑ j,x j)+upperMajorantB i (∑ k,x k^3) := by
  simp only [upperMajorantH, mul_sub, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hnorm, mul_one]
  have he : (∑ j, x j^2*(x j-(∑ k,x k^3))) = 0 := by
    simp_rw [mul_sub, ← pow_succ, Finset.sum_sub_distrib, ← Finset.sum_mul, hnorm, one_mul]
    ring
  simp only [mul_assoc, ← Finset.mul_sum]
  simp_rw [← pow_succ]
  ring
end
end SingularValueBounds.KL
