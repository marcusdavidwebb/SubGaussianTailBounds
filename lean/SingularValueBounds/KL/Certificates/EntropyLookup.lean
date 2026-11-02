import Mathlib.Data.Nat.Notation

/-! The generic finite lookup tree used by the exact entropy tables.
The original bitwise lookup and its leaf behavior are preserved verbatim. -/
namespace SingularValueBounds.KL.Certificates

inductive EntropyLookup (α : Type) where
  | leaf : α → EntropyLookup α
  | branch : EntropyLookup α → EntropyLookup α → EntropyLookup α

def EntropyLookup.get {α : Type} : EntropyLookup α → ℕ → α
  | .leaf a, _ => a
  | .branch l r, j => if j % 2 = 0 then l.get (j/2) else r.get (j/2)

end SingularValueBounds.KL.Certificates
