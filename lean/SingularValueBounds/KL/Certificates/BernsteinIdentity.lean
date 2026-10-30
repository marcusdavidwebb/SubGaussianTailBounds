import SingularValueBounds.KL.Certificates.Polynomial
import Mathlib.Algebra.Polynomial.ofFn

/-! Exact Bernstein inversion for every rational polynomial within the degree
bound. The identity is proved algebraically; concrete coefficient signs remain
separate kernel obligations. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private theorem bernstein_monomial_summand (n k j : ℕ) (hk : k ≤ n) (hj : j ≤ n-k) :
    C ((Nat.choose (k+j) k : ℚ)/(Nat.choose n k : ℚ)) *
      bernsteinPolynomial ℚ n (k+j) =
    X^k * bernsteinPolynomial ℚ (n-k) j := by
  have hnz : (Nat.choose n k : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  have hmul : (Nat.choose n (k+j) : ℚ) * (Nat.choose (k+j) k : ℚ) =
      (Nat.choose n k : ℚ) * (Nat.choose (n-k) j : ℚ) := by
    have hnat := Nat.choose_mul (show k+j ≤ n by omega) (show k ≤ k+j by omega)
    exact_mod_cast (by simpa using hnat :
      Nat.choose n (k+j) * Nat.choose (k+j) k = Nat.choose n k * Nat.choose (n-k) j)
  have hc : (Nat.choose (k+j) k : ℚ)/(Nat.choose n k : ℚ) * Nat.choose n (k+j) =
      (Nat.choose (n-k) j : ℚ) := by
    field_simp
    nlinarith [hmul]
  calc
    C ((Nat.choose (k+j) k : ℚ)/(Nat.choose n k : ℚ)) *
        bernsteinPolynomial ℚ n (k+j) =
      C (((Nat.choose (k+j) k : ℚ)/(Nat.choose n k : ℚ)) * Nat.choose n (k+j)) *
        X^(k+j) * (1-X)^(n-(k+j)) := by
          simp only [bernsteinPolynomial, map_mul, map_natCast]
          ring
    _ = X^k * bernsteinPolynomial ℚ (n-k) j := by
      rw [hc]
      have he : n-(k+j) = n-k-j := by omega
      simp only [bernsteinPolynomial, he, pow_add, map_natCast]
      ring

/-- Exact monomial expansion in a degree-`n` Bernstein basis. -/
theorem monomial_bernstein_identity (n k : ℕ) (hk : k ≤ n) :
    X^k = bernsteinExpansion n
      (fun i => (Nat.choose i.val k : ℚ)/(Nat.choose n k : ℚ)) := by
  unfold bernsteinExpansion
  change X^k = ∑ i : Fin (n+1),
    C ((Nat.choose i.val k : ℚ)/(Nat.choose n k : ℚ)) * bernsteinPolynomial ℚ n i.val
  rw [← Finset.sum_range (n := n+1) (fun i =>
    C ((Nat.choose i k : ℚ)/(Nat.choose n k : ℚ)) * bernsteinPolynomial ℚ n i)]
  have hsplit : n+1 = k+(n-k+1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hz : ∑ i ∈ Finset.range k,
      C ((Nat.choose i k : ℚ)/(Nat.choose n k : ℚ)) * bernsteinPolynomial ℚ n i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
  rw [hz, zero_add]
  have he : ∑ j ∈ Finset.range (n-k+1),
      C ((Nat.choose (k+j) k : ℚ)/(Nat.choose n k : ℚ)) *
        bernsteinPolynomial ℚ n (k+j) =
      ∑ j ∈ Finset.range (n-k+1), X^k * bernsteinPolynomial ℚ (n-k) j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact bernstein_monomial_summand n k j hk (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  rw [he, ← Finset.mul_sum, bernsteinPolynomial.sum, mul_one]


/-- Inversion of the coefficient conversion, with no numerical premise. -/
theorem polynomial_bernstein_identity (p : ℚ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    p = bernsteinExpansion n (bernsteinCoefficients p n) := by
  calc
    p = ∑ k ∈ Finset.range (n+1), C (p.coeff k) * X^k := by
      simpa only [C_mul_X_pow_eq_monomial] using p.as_sum_range' (n+1) (by omega)
    _ = ∑ k ∈ Finset.range (n+1), C (p.coeff k) *
        bernsteinExpansion n (fun i => (Nat.choose i.val k : ℚ)/(Nat.choose n k : ℚ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [monomial_bernstein_identity n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = bernsteinExpansion n (bernsteinCoefficients p n) := by
      unfold bernsteinExpansion bernsteinCoefficients
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [map_sum, map_mul, Finset.sum_mul, mul_assoc]

/-- Vector coefficients expose finite arithmetic without evaluating polynomial quotients. -/
theorem bernsteinCoefficients_ofFn (n : ℕ) (a : Fin (n+1) → ℚ) (i : Fin (n+1)) :
    bernsteinCoefficients (Polynomial.ofFn (n+1) a) n i =
      ∑ k : Fin (n+1), a k * ((i.val.choose k.val : ℚ)/(n.choose k.val : ℚ)) := by
  unfold bernsteinCoefficients
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.ofFn_coeff_eq_val_of_lt a k.isLt]

end SingularValueBounds.KL.Certificates
