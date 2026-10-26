import SingularValueBounds.KL.Certificates.AffineCoefficientIdentity
import SingularValueBounds.KL.Certificates.TensorBernsteinIdentity

/-! Exact finite coefficient transforms for affine substitutions in two variables. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 2000000

lemma ofFn_eval_affine_sum (n : ℕ) (a : Fin (n+1) → ℚ) (s w x : ℚ) :
    (∑ k : Fin (n+1), a k * (s+w*x)^k.val) =
      ∑ j : Fin (n+1),
        (∑ k : Fin (n+1), a k * (s^(k.val-j.val)*(k.val.choose j.val : ℚ)*w^j.val)) * x^j.val := by
  have he := ofFn_comp_affine_eq n a
    (fun j => ∑ k : Fin (n+1), a k * (s^(k.val-j.val)*(k.val.choose j.val : ℚ)*w^j.val))
    s w (fun _ => rfl)
  have hv := congrArg (Polynomial.eval x) he
  simpa only [Polynomial.eval_comp, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finset_sum, Polynomial.eval_monomial, affine, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X] using hv

lemma tensorOfFn_eval (n m : ℕ) (a : Fin (n+1) → Fin (m+1) → ℚ) (x y : ℚ) :
    (tensorOfFn n m a).eval₂ (Polynomial.evalRingHom x) y =
      ∑ l : Fin (m+1), (∑ k : Fin (n+1), a k l*x^k.val)*y^l.val := by
  simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval₂_finset_sum, Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom,
    Polynomial.eval_finset_sum, Polynomial.eval_monomial]

/-- A finite double binomial transform certifies an affine change of both variables. -/
theorem tensorOfFn_affine_eq (n m : ℕ)
    (a b : Fin (n+1) → Fin (m+1) → ℚ) (s w c h : ℚ)
    (hb : ∀ i : Fin (n+1), ∀ j : Fin (m+1),
      (∑ l : Fin (m+1), (∑ k : Fin (n+1),
        a k l * (s^(k.val-i.val)*(k.val.choose i.val : ℚ)*w^i.val)) *
          (c^(l.val-j.val)*(l.val.choose j.val : ℚ)*h^j.val)) = b i j) :
    tensorAffine (tensorOfFn n m a) s w c h = tensorOfFn n m b := by
  apply tensor_eq_of_eval
  intro x y
  rw [tensorAffine_eval, tensorOfFn_eval, tensorOfFn_eval]
  simp_rw [ofFn_eval_affine_sum n _ s w x]
  conv_lhs => arg 2; ext l; rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hexpand (i : Fin (n+1)) :
      (∑ l : Fin (m+1),
        (∑ k : Fin (n+1), a k l * (s^(k.val-i.val)*(k.val.choose i.val : ℚ)*w^i.val)) *
          x^i.val*(c+h*y)^l.val) =
      ∑ j : Fin (m+1), b i j*x^i.val*y^j.val := by
    calc
      _ = (∑ l : Fin (m+1),
          (∑ k : Fin (n+1), a k l * (s^(k.val-i.val)*(k.val.choose i.val : ℚ)*w^i.val)) *
            (c+h*y)^l.val) * x^i.val := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro l _
              ring
      _ = _ := by
        rw [ofFn_eval_affine_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [hb]
        ring
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]

/-- Finite coefficient identities and signs give a closed-box certificate. -/
theorem boxCertificate_of_tensorOfFn (n m : ℕ)
    (a b : Fin (n+1) → Fin (m+1) → ℚ) (box : RationalBox)
    (hx : box.left < box.right) (hy : box.bottom < box.top)
    (hb : ∀ i : Fin (n+1), ∀ j : Fin (m+1),
      (∑ l : Fin (m+1), (∑ k : Fin (n+1),
        a k l * (box.left^(k.val-i.val)*(k.val.choose i.val : ℚ)*
          (box.right-box.left)^i.val)) *
          (box.bottom^(l.val-j.val)*(l.val.choose j.val : ℚ)*
            (box.top-box.bottom)^j.val)) = b i j)
    (hs : ∀ i : Fin (n+1), ∀ j : Fin (m+1), 0 ≤
      ∑ k : Fin (n+1), ∑ l : Fin (m+1),
        b k l * ((i.val.choose k.val : ℚ)/n.choose k.val) *
          ((j.val.choose l.val : ℚ)/m.choose l.val)) :
    BoxCertificate (tensorOfFn n m a) n m box := by
  refine ⟨hx, hy, ?_⟩
  change TensorCertificate
    (tensorAffine (tensorOfFn n m a) box.left (box.right-box.left)
      box.bottom (box.top-box.bottom)) n m _
  rw [tensorOfFn_affine_eq n m a b _ _ _ _ hb]
  exact ⟨tensorOfFn_bernstein_identity n m b, by simpa only [tensorCoefficients_ofFn] using hs⟩

end SingularValueBounds.KL.Certificates
