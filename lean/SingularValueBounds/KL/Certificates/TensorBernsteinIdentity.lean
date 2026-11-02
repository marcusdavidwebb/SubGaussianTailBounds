import SingularValueBounds.KL.Certificates.BernsteinIdentity

/-! Exact tensor Bernstein inversion with kernel-checked degree hypotheses. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 2000000
lemma tensor_eq_of_eval {p q : Polynomial (Polynomial ℚ)}
    (h : ∀ a b : ℚ, p.eval₂ (Polynomial.evalRingHom a) b =
      q.eval₂ (Polynomial.evalRingHom a) b) : p = q := by
  apply Polynomial.ext
  intro l
  apply Polynomial.funext
  intro a
  have hm : p.map (Polynomial.evalRingHom a) = q.map (Polynomial.evalRingHom a) := by
    apply Polynomial.funext
    intro b
    simpa only [Polynomial.eval_map] using h a b
  simpa only [Polynomial.coeff_map, Polynomial.coe_evalRingHom] using
    congrArg (fun f : ℚ[X] => f.coeff l) hm

lemma eval_bernstein_monomial (n k : ℕ) (hk : k ≤ n) (a : ℚ) :
    a^k = ∑ i : Fin (n+1), ((i.val.choose k:ℚ)/n.choose k)*
      (bernsteinPolynomial ℚ n i).eval a := by
  have h := congrArg (Polynomial.eval a) (monomial_bernstein_identity n k hk)
  simpa [bernsteinExpansion, Polynomial.eval_finset_sum] using h

theorem tensor_bernstein_identity (p : Polynomial (Polynomial ℚ)) (n m : ℕ)
    (hp : p.natDegree ≤ m) (hc : ∀ l, (p.coeff l).natDegree ≤ n) :
    p = tensorExpansion n m (tensorCoefficients p n m) := by
  apply tensor_eq_of_eval
  intro a b
  have hbern (j : ℕ) :
      (bernsteinPolynomial (Polynomial ℚ) m j).eval₂ (Polynomial.evalRingHom a) b =
      (bernsteinPolynomial ℚ m j).eval b := by
    simp [bernsteinPolynomial, Polynomial.eval₂_pow, Polynomial.eval₂_sub]
  have hp_eval : p.eval₂ (Polynomial.evalRingHom a) b =
      ∑ l ∈ Finset.range (m+1), ∑ k ∈ Finset.range (n+1), (p.coeff l).coeff k*a^k*b^l := by
    rw [Polynomial.eval₂_eq_sum_range' _ (by omega : p.natDegree < m+1)]
    apply Finset.sum_congr rfl
    intro l _
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_eq_sum_range' (by have := hc l; omega : (p.coeff l).natDegree < n+1)]
    exact Finset.sum_mul _ _ _
  rw [hp_eval]
  simp only [tensorExpansion, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
    hbern, tensorCoefficients]
  simp_rw [Finset.sum_mul]
  have hexpand : (∑ l ∈ Finset.range (m+1), ∑ k ∈ Finset.range (n+1), (p.coeff l).coeff k*a^k*b^l) =
      ∑ l ∈ Finset.range (m+1), ∑ k ∈ Finset.range (n+1),
        ∑ i : Fin (n+1), ∑ j : Fin (m+1),
          (p.coeff l).coeff k * ((i.val.choose k:ℚ)/n.choose k) *
            ((j.val.choose l:ℚ)/m.choose l) *
              (bernsteinPolynomial ℚ n i).eval a * (bernsteinPolynomial ℚ m j).eval b := by
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    rw [eval_bernstein_monomial n k (by have := Finset.mem_range.mp hk; omega) a,
      eval_bernstein_monomial m l (by have := Finset.mem_range.mp hl; omega) b]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

lemma tensorAffine_eval (p : Polynomial (Polynomial ℚ)) (a w c h x y : ℚ) :
    (tensorAffine p a w c h).eval₂ (Polynomial.evalRingHom x) y =
      p.eval₂ (Polynomial.evalRingHom (a+w*x)) (c+h*y) := by
  have he : (Polynomial.evalRingHom x).comp (Polynomial.compRingHom (affine a w)) =
      Polynomial.evalRingHom (a+w*x) := by
    ext q <;>
    simp [Polynomial.coe_evalRingHom, Polynomial.coe_compRingHom, RingHom.comp_apply,
      affine]
  simp only [tensorAffine, Polynomial.eval₂_comp, Polynomial.eval₂_add,
    Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_map]
  rw [he]
  simp [Polynomial.coe_evalRingHom]

noncomputable def tensorOfFn (n m : ℕ) (a : Fin (n+1) → Fin (m+1) → ℚ) : Polynomial (Polynomial ℚ) :=
  Polynomial.ofFn (m+1) (fun l => Polynomial.ofFn (n+1) (fun k => a k l))

theorem tensorCoefficients_ofFn (n m : ℕ) (a : Fin (n+1) → Fin (m+1) → ℚ)
    (i : Fin (n+1)) (j : Fin (m+1)) :
    tensorCoefficients (tensorOfFn n m a) n m i j =
      ∑ k : Fin (n+1), ∑ l : Fin (m+1),
        a k l * ((i.val.choose k.val : ℚ)/n.choose k.val) *
          ((j.val.choose l.val : ℚ)/m.choose l.val) := by
  unfold tensorCoefficients tensorOfFn
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.ofFn_coeff_eq_val_of_lt _ l.isLt,
    Polynomial.ofFn_coeff_eq_val_of_lt _ k.isLt]

theorem tensorOfFn_bernstein_identity (n m : ℕ) (a : Fin (n+1) → Fin (m+1) → ℚ) :
    tensorOfFn n m a = tensorExpansion n m (tensorCoefficients (tensorOfFn n m a) n m) := by
  apply tensor_bernstein_identity
  · exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
  · intro l
    by_cases hl : l < m+1
    · rw [tensorOfFn, Polynomial.ofFn_coeff_eq_val_of_lt _ hl]
      exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
    · rw [tensorOfFn, Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      simp

end SingularValueBounds.KL.Certificates
