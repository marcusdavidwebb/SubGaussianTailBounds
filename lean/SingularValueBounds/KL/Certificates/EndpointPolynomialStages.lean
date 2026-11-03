import SingularValueBounds.KL.Certificates.TensorAffineIdentity

/-! Separable finite coefficient checks for endpoint rectangle certificates.
Keeping the two coordinate transforms separate avoids repeating inner sums. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates

/-- Four one-coordinate transforms certify a tensor polynomial on a rational box. -/
theorem boxCertificate_of_tensorStages (n m : ℕ)
    (a ax b bx : Fin (n+1) → Fin (m+1) → ℚ) (box : RationalBox)
    (hx : box.left < box.right) (hy : box.bottom < box.top)
    (hax : ∀ i : Fin (n+1), ∀ l : Fin (m+1),
      (∑ k : Fin (n+1), a k l *
        (box.left^(k.val-i.val)*(k.val.choose i.val : ℚ)*
          (box.right-box.left)^i.val)) = ax i l)
    (hay : ∀ i : Fin (n+1), ∀ j : Fin (m+1),
      (∑ l : Fin (m+1), ax i l *
        (box.bottom^(l.val-j.val)*(l.val.choose j.val : ℚ)*
          (box.top-box.bottom)^j.val)) = b i j)
    (hbx : ∀ i : Fin (n+1), ∀ l : Fin (m+1),
      (∑ k : Fin (n+1), b k l *
        ((i.val.choose k.val : ℚ)/n.choose k.val)) = bx i l)
    (hby : ∀ i : Fin (n+1), ∀ j : Fin (m+1), 0 ≤
      ∑ l : Fin (m+1), bx i l *
        ((j.val.choose l.val : ℚ)/m.choose l.val)) :
    BoxCertificate (tensorOfFn n m a) n m box := by
  apply boxCertificate_of_tensorOfFn n m a b box hx hy
  · intro i j
    simpa only [hax] using hay i j
  · intro i j
    rw [Finset.sum_comm]
    conv_rhs => arg 2; ext l; rw [← Finset.sum_mul, hbx]
    exact hby i j

/-- Computed rational stages for the small degree-(4,1) branch. -/
noncomputable def rationalStageX {n m : ℕ}
    (a : Fin (n+1) → Fin (m+1) → ℚ) (box : RationalBox)
    (i : Fin (n+1)) (l : Fin (m+1)) : ℚ :=
  ∑ k, a k l * (box.left^(k.val-i.val)*(k.val.choose i.val : ℚ)*
    (box.right-box.left)^i.val)

noncomputable def rationalStageY {n m : ℕ}
    (a : Fin (n+1) → Fin (m+1) → ℚ) (box : RationalBox)
    (i : Fin (n+1)) (j : Fin (m+1)) : ℚ :=
  ∑ l, rationalStageX a box i l * (box.bottom^(l.val-j.val)*(l.val.choose j.val : ℚ)*
    (box.top-box.bottom)^j.val)

noncomputable def rationalStageBX {n m : ℕ}
    (a : Fin (n+1) → Fin (m+1) → ℚ) (box : RationalBox)
    (i : Fin (n+1)) (l : Fin (m+1)) : ℚ :=
  ∑ k, rationalStageY a box k l * ((i.val.choose k.val : ℚ)/n.choose k.val)

theorem boxCertificate_of_computedTensorStages (n m : ℕ)
    (a : Fin (n+1) → Fin (m+1) → ℚ) (box : RationalBox)
    (hx : box.left < box.right) (hy : box.bottom < box.top)
    (hs : ∀ i : Fin (n+1), ∀ j : Fin (m+1), 0 ≤
      ∑ l, rationalStageBX a box i l * ((j.val.choose l.val : ℚ)/m.choose l.val)) :
    BoxCertificate (tensorOfFn n m a) n m box :=
  boxCertificate_of_tensorStages n m a (rationalStageX a box) (rationalStageY a box)
    (rationalStageBX a box) box hx hy (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) hs

end SingularValueBounds.KL.Certificates
