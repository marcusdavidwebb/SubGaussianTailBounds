import SingularValueBounds.KL.Upper.CertificateData
import SingularValueBounds.KL.Upper.TailExtension
import SingularValueBounds.KL.Upper.Determinants

/-! # Interpretation of all fixed rate and determinant certificate families

Only `RateCertificateConditions` and `MajorantCertificateConditions`, which
are finite rational facts, remain assumptions. The real-variable conclusions
are proved throughout their stated intervals/rectangles. -/
open Polynomial Set
open scoped Polynomial BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1000000

theorem ratePolynomial_eval (v correction : ℚ) (y : ℝ) :
    realEval (ratePolynomial v correction) y = upperRateNumerator v correction y := by
  let e : ℚ[X] →+* ℝ := Polynomial.eval₂RingHom (Rat.castHom ℝ) y
  have hC (a : ℚ) : e (C a) = (a : ℝ) := by simp [e,Polynomial.coe_eval₂RingHom]
  have hX : e X = y := by simp [e,Polynomial.coe_eval₂RingHom]
  have hcoeff (j : ℕ) : (((1/(2*(j:ℚ)+1)):ℚ):ℝ) = 1/(2*(j:ℝ)+1) := by
    push_cast
    rfl
  change e (ratePolynomial v correction) = _
  dsimp only [ratePolynomial, upperRateNumerator]
  simp only [map_sub, map_mul, map_add, map_pow, map_sum, map_ofNat, map_one,
    hC, hX, hcoeff]
  simp only [add_sub_assoc, div_eq_mul_inv]
  have hsum : (∑ j ∈ Finset.range 6,
      (1/(2*(j:ℝ)+1))*((v:ℝ)*y)^(2*j+1)*
        (2*y^2+v*y+(2*v-2))^(10-2*j)*
          ((2*y^2+v*y+(2*v-2))^2-((v:ℝ)*y)^2)) =
      ∑ j ∈ Finset.range 6,
      ((v:ℝ)*y)^(2*j+1)*(2*y^2+v*y+(2*v-2))^(10-2*j)*
        ((2*y^2+v*y+(2*v-2))^2-((v:ℝ)*y)^2)/(2*(j:ℝ)+1) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [div_eq_mul_inv, one_mul]
    ac_rfl
  simp only [div_eq_mul_inv] at hsum
  rw [hsum]
  -- Preserve the factored degree-27 expression: only the last scalar moves.
  simp only [Rat.cast_inv, Rat.cast_ofNat, one_mul]
  rw [mul_comm (13 : ℝ)⁻¹ (((v : ℝ) * y)^13)]

theorem upper_rate_of_certificates (h : RateCertificateConditions) (i : Fin 15)
    {theta : ℝ} (ht : theta ∈ Icc (1 : ℝ) (rateRows i).1) :
    upperRateF (rateRows i).1 theta ≤ (rateRows i).2 := by
  have hrows : ∀ i : Fin 15, (1 : ℚ) < (rateRows i).1 := by decide +kernel
  have hv : (1 : ℝ) < (rateRows i).1 := by exact_mod_cast hrows i
  apply upperRateF_le_of_numerator hv ht.1
  rw [← ratePolynomial_eval]
  apply rate_polynomial_nonneg h i
  constructor <;> linarith [ht.1,ht.2]

theorem majorantBQ_eval (i : Fin 6) (a : ℝ) :
    realEval (majorantBQ i) a = upperMajorantB i a := by
  fin_cases i <;> norm_num [realEval, majorantBQ, upperMajorantB,
    Polynomial.eval₂_pow, Polynomial.eval₂_sub]

theorem majorantAQ_eval (i : Fin 6) (a : ℝ) :
    realEval (majorantAQ i) a = upperMajorantA i a := by
  fin_cases i <;> norm_num [realEval, majorantAQ, upperMajorantA,
    Polynomial.eval₂_pow, Polynomial.eval₂_sub]

theorem majorantCleared_eval (i : Fin 6) (a x : ℝ) :
    realEval₂ (majorantCleared i) a x =
      upperMajorantH i a x * upperPadeD (upperComparisonZ a x) -
        upperPadeN (upperComparisonZ a x) := by
  simp only [realEval₂, majorantCleared, majorantHQ, padeDQ, padeNQ, comparisonZQ,
    Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow,
    Polynomial.eval₂_one, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  norm_num only [Polynomial.eval₂_ofNat, map_div₀, map_ofNat]
  rw [show (Polynomial.eval₂ (Rat.castHom ℝ) a (majorantBQ i)) =
    upperMajorantB i a from majorantBQ_eval i a,
    show (Polynomial.eval₂ (Rat.castHom ℝ) a (majorantAQ i)) =
    upperMajorantA i a from majorantAQ_eval i a]
  norm_num [upperMajorantH, upperPadeD, upperPadeN, upperComparisonZ]

theorem upper_scalar_majorant_of_certificates (h : MajorantCertificateConditions) (i : Fin 6)
    {a x : ℝ} (hax : (majorantBoxes i).contains a x)
    (hz : upperComparisonZ a x < 1) :
    -Real.log (1-upperComparisonZ a x) ≤ upperMajorantH i a x := by
  apply upper_scalar_majorant_of_polynomial i hz
  rw [← majorantCleared_eval]
  exact majorant_cleared_nonneg h i hax

theorem majorant_domain_bounds (i : Fin 6) {a x : ℝ}
    (hax : (majorantBoxes i).contains a x) : a ≤ 5/6 ∧ 0 ≤ x ∧ x ≤ 1 := by
  have hboxes : ∀ i : Fin 6,
      (majorantBoxes i).right ≤ (5/6 : ℚ) ∧
      (0 : ℚ) ≤ (majorantBoxes i).bottom ∧ (majorantBoxes i).top ≤ (1 : ℚ) := by
    decide +kernel
  have hb : ((majorantBoxes i).right : ℝ) ≤ 5/6 ∧
      (0 : ℝ) ≤ (majorantBoxes i).bottom ∧ ((majorantBoxes i).top : ℝ) ≤ 1 := by
    refine ⟨?_, ?_, ?_⟩
    · have hr : ((majorantBoxes i).right : ℝ) ≤ ((5/6 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (hboxes i).1
      norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
      exact hr
    · exact_mod_cast (hboxes i).2.1
    · exact_mod_cast (hboxes i).2.2
  exact ⟨hax.1.2.trans hb.1, hb.2.1.trans hax.2.1, hax.2.2.trans hb.2.2⟩

theorem upper_scalar_majorant_on_domain (h : MajorantCertificateConditions) (i : Fin 6)
    {a x : ℝ} (hax : (majorantBoxes i).contains a x) :
    -Real.log (1-upperComparisonZ a x) ≤ upperMajorantH i a x := by
  obtain ⟨ha,hx,_⟩ := majorant_domain_bounds i hax
  exact upper_scalar_majorant_of_certificates h i hax (upperComparisonZ_lt_one ha hx)

theorem sum_bound_with_one_retained {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) (k : ι) (retained : ℝ)
    (hother : ∀ j, j ≠ k → f j ≤ g j) (hk : f k ≤ retained) :
    (∑ j,f j) ≤ (∑ j,g j)-g k+retained := by
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase k)
    (fun j hj => hother j (Finset.mem_erase.mp hj).1)
  have hf := Finset.sum_erase_add (Finset.univ : Finset ι) f (Finset.mem_univ k)
  have hg := Finset.sum_erase_add (Finset.univ : Finset ι) g (Finset.mem_univ k)
  linarith

theorem upper_six_logdet_majorants {ι : Type*} [Fintype ι]
    (h : MajorantCertificateConditions) (i : Fin 6) (x : ι → ℝ)
    (hnorm : ∑ j,x j^2 = 1)
    (hdomain : ∀ j, (majorantBoxes i).contains (∑ k,x k^3) (x j)) :
    (∑ j,-Real.log (1-upperComparisonZ (∑ k,x k^3) (x j)))-2*(∑ j,x j) ≤
      upperMajorantB i (∑ k,x k^3) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => upper_scalar_majorant_on_domain h i (hdomain j))
  rw [upperMajorantH_sum i x hnorm] at hs
  linarith

/-- Retains the entire Padé contribution of the chosen eigenvalue. Choosing
a largest coordinate gives exactly supplementary equation `eq:k1-joint-J`. -/
theorem upper_joint_logdet_majorants {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : MajorantCertificateConditions) (i : Fin 6) (x : ι → ℝ) (top : ι)
    (hnorm : ∑ j,x j^2 = 1)
    (hdomain : ∀ j, (majorantBoxes i).contains (∑ k,x k^3) (x j)) :
    (∑ j,-Real.log (1-upperComparisonZ (∑ k,x k^3) (x j)))-2*(∑ j,x j) ≤
      upperMajorantB i (∑ k,x k^3)-upperMajorantH i (∑ k,x k^3) (x top)+
        upperPadeN (upperComparisonZ (∑ k,x k^3) (x top)) /
          upperPadeD (upperComparisonZ (∑ k,x k^3) (x top)) := by
  have hb := majorant_domain_bounds i (hdomain top)
  have hs := sum_bound_with_one_retained
    (fun j => -Real.log (1-upperComparisonZ (∑ k,x k^3) (x j)))
    (fun j => upperMajorantH i (∑ k,x k^3) (x j)) top
    (upperPadeN (upperComparisonZ (∑ k,x k^3) (x top)) /
      upperPadeD (upperComparisonZ (∑ k,x k^3) (x top)))
    (fun j _ => upper_scalar_majorant_on_domain h i (hdomain j))
    (neg_log_one_sub_le_upperPade (upperComparisonZ_lt_one hb.1 hb.2.1))
  rw [upperMajorantH_sum i x hnorm] at hs
  linarith

end
end SingularValueBounds.KL
