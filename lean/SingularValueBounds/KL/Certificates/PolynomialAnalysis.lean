import SingularValueBounds.KL.Certificates.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-! Calculus consequences of finite polynomial certificates.
The monotonicity and unique-root rules use derivatives and the intermediate
value theorem; the algebraic certificate rules remain in `Polynomial`. -/
open scoped BigOperators Polynomial
open Polynomial Set
namespace SingularValueBounds.KL.Certificates
noncomputable section

theorem polynomial_monotone {p : ℝ[X]} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, 0 ≤ p.derivative.eval x) : MonotoneOn p.eval (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) p.continuous.continuousOn
    (fun _ _ => p.differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  simpa only [p.deriv] using hd x ⟨hx.1.le, hx.2.le⟩

theorem polynomial_strictMono {p : ℝ[X]} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, 0 < p.derivative.eval x) : StrictMonoOn p.eval (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) p.continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  simpa only [p.deriv] using hd x ⟨hx.1.le, hx.2.le⟩

/-- The root-finding implication uses IVT and a proved derivative sign;
no numerical root finder is trusted as an analytic assertion. -/
theorem polynomial_unique_root {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (ha : p.eval a ≤ 0) (hb : 0 ≤ p.eval b)
    (hd : ∀ x ∈ Icc a b, 0 < p.derivative.eval x) :
    ∃! r, r ∈ Icc a b ∧ p.eval r = 0 := by
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hab p.continuous.continuousOn ⟨ha, hb⟩
  refine ⟨r, ⟨hr, he⟩, ?_⟩
  intro s hs
  exact (polynomial_strictMono hd).injOn hs.1 hr (hs.2.trans he.symm)

theorem rational_polynomial_unique_root {p : ℚ[X]} {a width ε : ℚ}
    {n : ℕ} {b : Fin (n + 1) → ℚ} (hw : 0 < width) (hε : 0 < ε)
    (hid : p.derivative.comp (affine a width) = bernsteinExpansion n b)
    (hb : ∀ i, ε ≤ b i ∧ b i ≤ b 0 + ∑ j, |b j|)
    (ha : p.eval a ≤ 0) (hc : 0 ≤ p.eval (a + width)) :
    ∃! r, r ∈ Icc (a : ℝ) ((a : ℝ) + width) ∧ realEval p r = 0 := by
  have hwidth : (0 : ℝ) < width := by exact_mod_cast hw
  have hr := polynomial_unique_root (p := p.map (Rat.castHom ℝ))
    (a := (a : ℝ)) (b := (a : ℝ) + width)
    (le_add_of_nonneg_right hwidth.le)
  have he (x : ℝ) : (p.map (Rat.castHom ℝ)).eval x = realEval p x := by
    simp [realEval, Polynomial.eval_map]
  simp_rw [← he]
  apply hr
  · rw [he, realEval_rat]
    exact_mod_cast ha
  · rw [he, ← Rat.cast_add, realEval_rat]
    exact_mod_cast hc
  · intro x hx
    have h := (polynomial_bounds_interval hid hb hw hx).1
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have he' : (p.map (Rat.castHom ℝ)).derivative.eval x = realEval p.derivative x := by
      simp [realEval, Polynomial.derivative_map, Polynomial.eval_map]
    rw [he']
    exact hε'.trans_le h

end
end SingularValueBounds.KL.Certificates
