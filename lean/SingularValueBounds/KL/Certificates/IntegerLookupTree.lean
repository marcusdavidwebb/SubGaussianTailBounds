import Mathlib.Data.Int.Basic

/-! A balanced integer lookup used only during exact finite proof checking. -/
namespace SingularValueBounds.KL.Certificates

inductive IntegerLookupTree where
  | leaf (value : ℤ)
  | branch (cutoff : ℕ) (left right : IntegerLookupTree)

def IntegerLookupTree.get : IntegerLookupTree → ℕ → ℤ
  | .leaf value, _ => value
  | .branch cutoff left right, j =>
      if j < cutoff then left.get j else right.get j

end SingularValueBounds.KL.Certificates
