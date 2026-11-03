import SingularValueBounds.KL.Certificates.IntegerMatrixNotation
import SingularValueBounds.KL.Certificates.IntegerCoefficientStages

/-! Shared integer Bernstein weights for the degree-(8,15) general-mean tests. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates

noncomputable def bernsteinIntegerWeights8 : Fin 9 → Fin 9 → ℤ :=
  fun i k => (integer_matrix![![280, 0, 0, 0, 0, 0, 0, 0, 0],
    ![280, 35, 0, 0, 0, 0, 0, 0, 0],
    ![280, 70, 10, 0, 0, 0, 0, 0, 0],
    ![280, 105, 30, 5, 0, 0, 0, 0, 0],
    ![280, 140, 60, 20, 4, 0, 0, 0, 0],
    ![280, 175, 100, 50, 20, 5, 0, 0, 0],
    ![280, 210, 150, 100, 60, 30, 10, 0, 0],
    ![280, 245, 210, 175, 140, 105, 70, 35, 0],
    ![280, 280, 280, 280, 280, 280, 280, 280, 280]]) i k

theorem bernsteinIntegerWeights8_exact (i k : Fin 9) :
    (i.val.choose k.val : ℚ)/(8 : ℕ).choose k.val =
      (bernsteinIntegerWeights8 i k : ℚ)/280 := by
  revert i k
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

/-- Compact degree-(8,15) certificates, sharing the checked Bernstein weights. -/
theorem boxCertificate_of_computedIntegerStages_8_15
    (a : Fin 9 → Fin 16 → ℚ) (box : RationalBox)
    (aa : Fin 9 → Fin 16 → ℤ)
    (wx : Fin 9 → Fin 9 → ℤ) (wy : Fin 16 → Fin 16 → ℤ)
    (da dx dy : ℤ) (hda : 0 < da) (hdx : 0 < dx) (hdy : 0 < dy)
    (hx : box.left < box.right) (hy : box.bottom < box.top)
    (ha : ∀ k l, a k l = (aa k l : ℚ) / (da : ℚ))
    (hwx : ∀ i k,
      box.left^(k.val-i.val)*(k.val.choose i.val : ℚ)*(box.right-box.left)^i.val =
        (wx i k : ℚ) / (dx : ℚ))
    (hwy : ∀ j l,
      box.bottom^(l.val-j.val)*(l.val.choose j.val : ℚ)*(box.top-box.bottom)^j.val =
        (wy j l : ℚ) / (dy : ℚ))
    (hs : ∀ i j, 0 ≤ ∑ l,
      integerStageBX aa wx wy bernsteinIntegerWeights8 i l * bernsteinIntegerWeights15 j l) :
    BoxCertificate (tensorOfFn 8 15 a) 8 15 box :=
  boxCertificate_of_computedIntegerStages 8 15 a box aa wx bernsteinIntegerWeights8
    wy bernsteinIntegerWeights15 da dx dy 280 45045 hda hdx hdy (by decide) (by decide)
    hx hy ha hwx hwy bernsteinIntegerWeights8_exact bernsteinIntegerWeights15_exact hs

end SingularValueBounds.KL.Certificates
