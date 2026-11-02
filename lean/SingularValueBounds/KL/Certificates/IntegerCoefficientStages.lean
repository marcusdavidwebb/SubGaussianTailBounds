import Mathlib.Algebra.BigOperators.Field
import SingularValueBounds.KL.Certificates.IntegerMatrixNotation
import SingularValueBounds.KL.Certificates.EndpointPolynomialStages

/-!
Denominator clearing for finite tensor coefficient transforms. Integer tables
are proposals: every entry identity and every resulting sign is a Lean premise.
The generic implication below converts those checked integer identities back
to the existing rational Bernstein certificate, without changing its meaning.
-/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates

private theorem sum_mul_int_div {ι : Type*} [Fintype ι]
    (a b : ι → ℤ) (d e : ℤ) :
    (∑ k, (a k : ℚ) / (d : ℚ) * ((b k : ℚ) / (e : ℚ))) =
      ((∑ k, a k * b k : ℤ) : ℚ) / ((d * e : ℤ) : ℚ) := by
  simp only [div_mul_div_comm, Int.cast_mul, Int.cast_sum, Finset.sum_div]

/-- Four integer matrix products, with exact rational weight identities,
certify a polynomial on a closed rational rectangle. Each stage has its own
positive denominator; cross-multiplication permits common factors to be cancelled
in the proposed tables without assuming their identities. -/
theorem boxCertificate_of_integerStages (n m : ℕ)
    (a : Fin (n+1) → Fin (m+1) → ℚ) (box : RationalBox)
    (aa ax b bx : Fin (n+1) → Fin (m+1) → ℤ)
    (wx ux : Fin (n+1) → Fin (n+1) → ℤ)
    (wy uy : Fin (m+1) → Fin (m+1) → ℤ)
    (da dax db dbx dx dy du dv : ℤ)
    (hda : 0 < da) (hdax : 0 < dax) (hdb : 0 < db) (hdbx : 0 < dbx)
    (hdx : 0 < dx) (hdy : 0 < dy)
    (hdu : 0 < du) (hdv : 0 < dv)
    (hx : box.left < box.right) (hy : box.bottom < box.top)
    (ha : ∀ k l, a k l = (aa k l : ℚ) / (da : ℚ))
    (hwx : ∀ i k,
      box.left^(k.val-i.val)*(k.val.choose i.val : ℚ)*(box.right-box.left)^i.val =
        (wx i k : ℚ) / (dx : ℚ))
    (hwy : ∀ j l,
      box.bottom^(l.val-j.val)*(l.val.choose j.val : ℚ)*(box.top-box.bottom)^j.val =
        (wy j l : ℚ) / (dy : ℚ))
    (hux : ∀ i k, (i.val.choose k.val : ℚ)/n.choose k.val =
      (ux i k : ℚ) / (du : ℚ))
    (huy : ∀ j l, (j.val.choose l.val : ℚ)/m.choose l.val =
      (uy j l : ℚ) / (dv : ℚ))
    (hax : ∀ i l, (∑ k, aa k l * wx i k) * dax = ax i l * (da*dx))
    (hb : ∀ i j, (∑ l, ax i l * wy j l) * db = b i j * (dax*dy))
    (hbx : ∀ i l, (∑ k, b k l * ux i k) * dbx = bx i l * (db*du))
    (hby : ∀ i j, 0 ≤ ∑ l, bx i l * uy j l) :
    BoxCertificate (tensorOfFn n m a) n m box := by
  apply boxCertificate_of_tensorStages n m a
    (fun i l => (ax i l : ℚ) / (dax : ℚ))
    (fun i j => (b i j : ℚ) / (db : ℚ))
    (fun i l => (bx i l : ℚ) / (dbx : ℚ)) box hx hy
  · intro i l
    simp only [ha, hwx]
    rw [sum_mul_int_div]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    exact_mod_cast hax _ _
  · intro i j
    simp only [hwy]
    rw [sum_mul_int_div]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    exact_mod_cast hb _ _
  · intro i l
    simp only [hux]
    rw [sum_mul_int_div]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    exact_mod_cast hbx _ _
  · intro i j
    simp only [huy]
    rw [sum_mul_int_div]
    apply div_nonneg
    · exact_mod_cast hby i j
    · exact_mod_cast (mul_pos hdbx hdv).le


/-- Fixed integer Bernstein weights, shared by every degree-(6,15) box. -/
noncomputable def bernsteinIntegerWeights6 : Fin 7 → Fin 7 → ℤ :=
  fun i k => (integer_matrix![![60, 0, 0, 0, 0, 0, 0],
    ![60, 10, 0, 0, 0, 0, 0],
    ![60, 20, 4, 0, 0, 0, 0],
    ![60, 30, 12, 3, 0, 0, 0],
    ![60, 40, 24, 12, 4, 0, 0],
    ![60, 50, 40, 30, 20, 10, 0],
    ![60, 60, 60, 60, 60, 60, 60]]) i k

theorem bernsteinIntegerWeights6_exact (i k : Fin 7) :
    (i.val.choose k.val : ℚ)/(6 : ℕ).choose k.val =
      (bernsteinIntegerWeights6 i k : ℚ)/60 := by
  revert i k
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

noncomputable def bernsteinIntegerWeights15 : Fin 16 → Fin 16 → ℤ :=
  fun i k => (integer_matrix![![45045, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![45045, 3003, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![45045, 6006, 429, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![45045, 9009, 1287, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![45045, 12012, 2574, 396, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![45045, 15015, 4290, 990, 165, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![45045, 18018, 6435, 1980, 495, 90, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![45045, 21021, 9009, 3465, 1155, 315, 63, 7, 0, 0, 0, 0, 0, 0, 0, 0],
    ![45045, 24024, 12012, 5544, 2310, 840, 252, 56, 7, 0, 0, 0, 0, 0, 0, 0],
    ![45045, 27027, 15444, 8316, 4158, 1890, 756, 252, 63, 9, 0, 0, 0, 0, 0, 0],
    ![45045, 30030, 19305, 11880, 6930, 3780, 1890, 840, 315, 90, 15, 0, 0, 0, 0, 0],
    ![45045, 33033, 23595, 16335, 10890, 6930, 4158, 2310, 1155, 495, 165, 33, 0, 0, 0, 0],
    ![45045, 36036, 28314, 21780, 16335, 11880, 8316, 5544, 3465, 1980, 990, 396, 99, 0, 0, 0],
    ![45045, 39039, 33462, 28314, 23595, 19305, 15444, 12012, 9009, 6435, 4290, 2574, 1287, 429, 0, 0],
    ![45045, 42042, 39039, 36036, 33033, 30030, 27027, 24024, 21021, 18018, 15015, 12012, 9009, 6006, 3003, 0],
    ![45045, 45045, 45045, 45045, 45045, 45045, 45045, 45045, 45045, 45045, 45045, 45045, 45045, 45045, 45045, 45045]]) i k

theorem bernsteinIntegerWeights15_exact (i k : Fin 16) :
    (i.val.choose k.val : ℚ)/(15 : ℕ).choose k.val =
      (bernsteinIntegerWeights15 i k : ℚ)/45045 := by
  revert i k
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

/-- Degree-(6,15) specialization sharing the exact Bernstein weights. -/
theorem boxCertificate_of_integerStages_6_15
    (a : Fin 7 → Fin 16 → ℚ) (box : RationalBox)
    (aa ax b bx : Fin 7 → Fin 16 → ℤ)
    (wx : Fin 7 → Fin 7 → ℤ) (wy : Fin 16 → Fin 16 → ℤ)
    (da dax db dbx dx dy : ℤ) (hda : 0 < da) (hdax : 0 < dax)
    (hdb : 0 < db) (hdbx : 0 < dbx) (hdx : 0 < dx) (hdy : 0 < dy)
    (hx : box.left < box.right) (hy : box.bottom < box.top)
    (ha : ∀ k l, a k l = (aa k l : ℚ) / (da : ℚ))
    (hwx : ∀ i k,
      box.left^(k.val-i.val)*(k.val.choose i.val : ℚ)*(box.right-box.left)^i.val =
        (wx i k : ℚ) / (dx : ℚ))
    (hwy : ∀ j l,
      box.bottom^(l.val-j.val)*(l.val.choose j.val : ℚ)*(box.top-box.bottom)^j.val =
        (wy j l : ℚ) / (dy : ℚ))
    (hax : ∀ i l, (∑ k, aa k l * wx i k) * dax = ax i l * (da*dx))
    (hb : ∀ i j, (∑ l, ax i l * wy j l) * db = b i j * (dax*dy))
    (hbx : ∀ i l, (∑ k, b k l * bernsteinIntegerWeights6 i k) * dbx = bx i l * (db*60))
    (hby : ∀ i j, 0 ≤ ∑ l, bx i l * bernsteinIntegerWeights15 j l) :
    BoxCertificate (tensorOfFn 6 15 a) 6 15 box :=
  boxCertificate_of_integerStages 6 15 a box aa ax b bx wx
    bernsteinIntegerWeights6 wy bernsteinIntegerWeights15 da dax db dbx dx dy 60 45045
    hda hdax hdb hdbx hdx hdy (by decide) (by decide) hx hy ha hwx hwy
    bernsteinIntegerWeights6_exact bernsteinIntegerWeights15_exact hax hb hbx hby

end SingularValueBounds.KL.Certificates
