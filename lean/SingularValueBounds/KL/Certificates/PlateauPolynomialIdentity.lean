import SingularValueBounds.KL.Certificates.AffineCoefficientIdentity
import SingularValueBounds.KL.Lower.PlateauCostData
import SingularValueBounds.KL.Certificates.IntegerMomentEvaluation
import SingularValueBounds.KL.Certificates.BernsteinIdentity
import Mathlib.Tactic.ComputeDegree
import SingularValueBounds.KL.Certificates.PlateauScalarIdentity

/-! Exact plateau polynomial identities from bounded-degree interpolation and
integer coefficient transforms. The original rational vectors remain unchanged;
every encoding, grid evaluation, affine identity and Bernstein sign is checked
inside Lean. Integer evaluations use the proved Taylor recurrence. -/

open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates

/-- A denominator-cleared coefficient of an affine monomial. -/
def affineIntegerWeight (n : ℕ) (s w d : ℤ) (j k : ℕ) : ℤ :=
  if j ≤ k then s^(k-j) * (k.choose j : ℤ) * w^j * d^(n-k) else 0

theorem affineIntegerWeight_exact (n : ℕ) (s w d : ℤ) (hd : d ≠ 0)
    (j k : ℕ) (hk : k ≤ n) :
    ((s : ℚ) / d)^(k-j) * (k.choose j : ℚ) * ((w : ℚ) / d)^j =
      (affineIntegerWeight n s w d j k : ℚ) / (d : ℚ)^n := by
  by_cases hj : j ≤ k
  · rw [affineIntegerWeight, if_pos hj]
    push_cast
    have hp : (d : ℚ)^n = (d : ℚ)^(k-j) * (d : ℚ)^j * (d : ℚ)^(n-k) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [hp]
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    simp only [div_pow]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)]
    simp [affineIntegerWeight, hj]

/-- Exact integer affine coefficient equations imply the original rational transform. -/
theorem ofFn_comp_affine_eq_of_integer (n : ℕ)
    (a b : Fin (n+1) → ℚ) (aa bb : Fin (n+1) → ℤ)
    (da db s w d : ℤ) (hda : da ≠ 0) (hdb : db ≠ 0) (hd : d ≠ 0)
    (ha : ∀ k, a k = (aa k : ℚ) / da)
    (hb : ∀ k, b k = (bb k : ℚ) / db)
    (h : ∀ j : Fin (n+1),
      (∑ k : Fin (n+1), aa k * affineIntegerWeight n s w d j.val k.val) * db =
        bb j * (da * d^n)) :
    (Polynomial.ofFn (n+1) a).comp (affine ((s : ℚ)/d) ((w : ℚ)/d)) =
      Polynomial.ofFn (n+1) b := by
  apply ofFn_comp_affine_eq n
  intro j
  have hw (k : Fin (n+1)) := affineIntegerWeight_exact n s w d hd j.val k.val (by omega)
  simp_rw [ha, hw]
  simp only [div_mul_div_comm, ← Finset.sum_div, hb]
  apply (div_eq_div_iff (by exact_mod_cast mul_ne_zero hda (pow_ne_zero n hd))
    (by exact_mod_cast hdb)).2
  exact_mod_cast h j

/-- Factorial-scaled Bernstein weights avoid rational normalization in the sum. -/
def bernsteinIntegerWeight (n i k : ℕ) : ℤ :=
  (i.choose k : ℤ) * k.factorial * (n-k).factorial

theorem bernsteinIntegerWeight_exact (n i k : ℕ) (hk : k ≤ n) :
    (i.choose k : ℚ) / (n.choose k : ℚ) =
      (bernsteinIntegerWeight n i k : ℚ) / (n.factorial : ℚ) := by
  have hfac : (n.choose k : ℚ) * k.factorial * (n-k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hc : (n.choose k : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold bernsteinIntegerWeight
  push_cast
  apply (div_eq_div_iff hc hf).2
  rw [← hfac]
  ring

theorem bernsteinCoefficients_nonneg_of_integer (n : ℕ)
    (a : Fin (n+1) → ℚ) (aa : Fin (n+1) → ℤ) (d : ℤ) (hd : 0 < d)
    (ha : ∀ k, a k = (aa k : ℚ) / d)
    (h : ∀ i : Fin (n+1), 0 ≤ ∑ k : Fin (n+1),
      aa k * bernsteinIntegerWeight n i.val k.val) :
    ∀ i, 0 ≤ bernsteinCoefficients (Polynomial.ofFn (n+1) a) n i := by
  intro i
  rw [bernsteinCoefficients_ofFn]
  have hw (k : Fin (n+1)) := bernsteinIntegerWeight_exact n i.val k.val (by omega)
  simp_rw [ha, hw]
  simp only [div_mul_div_comm, ← Finset.sum_div]
  apply div_nonneg
  · exact_mod_cast h i
  · positivity

end SingularValueBounds.KL.Certificates


open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
open NumericalCertificateConditions
open SingularValueBounds.KL.LowerCertificates

/-- Equality at enough distinct integers determines a bounded-degree polynomial. -/
theorem polynomial_eq_of_integer_grid (p q : ℚ[X]) (n : ℕ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ i : Fin (n+1), p.eval (i.val : ℚ) = q.eval (i.val : ℚ)) : p = q := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p-q)
    (f := fun i : Fin (n+1) => (i.val : ℚ))
  · intro i j hij
    dsimp only at hij
    exact Fin.ext (by exact_mod_cast hij)
  · intro i
    simpa only [Polynomial.eval_sub, sub_eq_zero] using h i
  · have hd := Polynomial.natDegree_sub_le_of_le hp hq
    simpa only [max_self, Fintype.card_fin] using Nat.lt_succ_of_le hd

theorem polynomialExpTaylor_degree (N d : ℕ) (p : ℚ[X]) (hp : p.natDegree ≤ d) :
    (polynomialExpTaylor N p).natDegree ≤ N*d := by
  unfold polynomialExpTaylor
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkn : k ≤ N := by have := Finset.mem_range.mp hk; omega
  have hdeg := Polynomial.natDegree_mul_le_of_le (show (C ((k.factorial : ℚ)⁻¹)).natDegree ≤ 0 by simp)
    (Polynomial.natDegree_pow_le_of_le k hp)
  exact hdeg.trans (by simpa using Nat.mul_le_mul_right d hkn)

theorem polynomialExpTaylor_eval_rat (N : ℕ) (p : ℚ[X]) (x : ℚ) :
    (polynomialExpTaylor N p).eval x = expTaylorQ N (p.eval x) := by
  simp [polynomialExpTaylor, expTaylorQ, Polynomial.eval_finset_sum, div_eq_mul_inv, mul_comm]

theorem ofFn_eval_of_integer (n : ℕ) (a : Fin (n+1) → ℚ) (aa : Fin (n+1) → ℤ)
    (d : ℤ) (ha : ∀ k, a k = (aa k : ℚ)/d) (x : ℤ) :
    (Polynomial.ofFn (n+1) a).eval (x : ℚ) =
      ((∑ k : Fin (n+1), aa k * x^k.val : ℤ) : ℚ) / d := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial, ha,
    Int.cast_sum, Int.cast_mul, Int.cast_pow, Finset.sum_div, div_mul_eq_mul_div]

theorem plateauCostMargin_degree (i : Fin 2) : (plateauCostMargin i).natDegree ≤ 100 := by
  have hD : (plateauCostD i).natDegree ≤ 4 := by
    unfold plateauCostD plateauCostA
    split_ifs <;> compute_degree!
  have hE : (-C 2*plateauCostE i).natDegree ≤ 4 := by
    unfold plateauCostE plateauCostV plateauCostA
    split_ifs <;> compute_degree!
  unfold plateauCostMargin
  have hexp := polynomialExpTaylor_degree 24 4 _ hE
  exact (Polynomial.natDegree_sub_le_of_le
    (Polynomial.natDegree_mul_le_of_le hD hexp) (show (C _ : ℚ[X]).natDegree ≤ 0 by simp)).trans (by norm_num)

theorem ofFn_eval_nat_of_integer (n : ℕ) (a : Fin (n+1) → ℚ) (aa : Fin (n+1) → ℤ)
    (d : ℤ) (ha : ∀ k, a k = (aa k : ℚ)/d) (x : ℕ) :
    (Polynomial.ofFn (n+1) a).eval (x : ℚ) =
      ((∑ k : Fin (n+1), aa k * (x : ℤ)^k.val : ℤ) : ℚ) / d := by
  simpa only [Int.cast_natCast] using ofFn_eval_of_integer n a aa d ha (x : ℤ)

theorem plateauScalarNumerator_degree (u A v w c : ℚ) :
    (plateauD u A c * polynomialExpTaylor 24 (plateauPsi u v w) - 1).natDegree ≤ 99 := by
  have hD : (plateauD u A c).natDegree ≤ 3 := by unfold plateauD; compute_degree!
  have hP : (plateauPsi u v w).natDegree ≤ 4 := by unfold plateauPsi; compute_degree!
  exact (Polynomial.natDegree_sub_le_of_le
    (Polynomial.natDegree_mul_le_of_le hD (polynomialExpTaylor_degree 24 4 _ hP))
    (show (1 : ℚ[X]).natDegree ≤ 0 by simp)).trans (by norm_num)

end SingularValueBounds.KL.Certificates
