import SingularValueBounds.KL.Certificates.BernsteinIdentity

/-! Exact, coefficientwise affine substitution for finite polynomial vectors. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0

/-- Binomial coefficients compute every coefficient of an affine monomial. -/
theorem affine_pow_coeff (a w : ℚ) (n k : ℕ) :
    ((affine a w)^n).coeff k = a^(n-k)*(n.choose k : ℚ)*w^k := by
  have he : (affine a w)^n = ((X+C a)^n).comp (C w*X) := by
    simp [affine, Polynomial.pow_comp, add_comm]
  rw [he, comp_C_mul_X_coeff, coeff_X_add_C_pow]

/-- Finite vector coefficients under affine substitution, without polynomial reduction. -/
theorem ofFn_comp_affine_coeff (n : ℕ) (a : Fin (n+1) → ℚ) (s w : ℚ) (j : ℕ) :
    ((Polynomial.ofFn (n+1) a).comp (affine s w)).coeff j =
      ∑ k : Fin (n+1), a k * (s^(k.val-j)*(k.val.choose j : ℚ)*w^j) := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp_rw [← C_mul_X_pow_eq_monomial]
  simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.pow_comp, Polynomial.X_comp, finset_sum_coeff, coeff_C_mul,
    affine_pow_coeff]

/-- A checked finite binomial transform determines the entire substituted polynomial. -/
theorem ofFn_comp_affine_eq (n : ℕ) (a b : Fin (n+1) → ℚ) (s w : ℚ)
    (h : ∀ j : Fin (n+1),
      (∑ k : Fin (n+1), a k * (s^(k.val-j.val)*(k.val.choose j.val : ℚ)*w^j.val)) = b j) :
    (Polynomial.ofFn (n+1) a).comp (affine s w) = Polynomial.ofFn (n+1) b := by
  ext j
  rw [ofFn_comp_affine_coeff]
  by_cases hj : j < n+1
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt b hj]
    exact h ⟨j,hj⟩
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge b (Nat.le_of_not_gt hj)]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Nat.choose_eq_zero_of_lt (show k.val < j by omega)]
    simp

end SingularValueBounds.KL.Certificates
