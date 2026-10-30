import SingularValueBounds.KL.Upper.EntropyQuadrature
import SingularValueBounds.KL.Upper.JointTail
import Mathlib.Analysis.Convex.Mul

/-! # Separate convexity of the endpoint entropy sum (supplementary S1.6.3)

The joint prefactor is the full logarithmic series, not a finite Taylor
approximation. Its positive coefficients prove separate convexity throughout
each spectral rectangle and justify the four-corner certificates.
-/

open MeasureTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

/-- Positive-series expansion of the spectral part of the joint cost. -/
theorem upperJointCost_hasSum {q k a : ℝ} (hq : 0 ≤ q) (hk : 0 < k)
    (hgap : q*k^2 < 1) :
    HasSum (fun n : ℕ => a*q^(n+2)*k^(2*n+1)/(n+2 : ℝ))
      (upperJointCost q k a-q) := by
  have habs : |q*k^2| < 1 := by rwa [abs_of_nonneg (mul_nonneg hq (sq_nonneg k))]
  have h := (hasSum_nat_add_iff' 1).2 (Real.hasSum_pow_div_log_of_abs_lt_one habs)
  norm_num [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] at h
  have hh := h.mul_left (a/k^3)
  convert! hh using 1
  · ext n
    have hn : (n+2 : ℝ) ≠ 0 := by positivity
    have hp : k^(2*n+1)*k^3=k^(2*(n+2)) := by rw [← pow_add]; congr 1 <;> omega
    apply mul_right_cancel₀ (pow_ne_zero 3 hk.ne')
    calc
      _ = a*q^(n+2)*(k^(2*n+1)*k^3)/(n+2 : ℝ) := by ring
      _ = a*q^(n+2)*k^(2*(n+2))/(n+2 : ℝ) := by rw [hp]
      _ = _ := by
        simp only [mul_pow, ← pow_mul]
        field_simp [hk.ne',hn]
        <;> ring
  · dsimp [upperJointCost]
    ring

theorem upperJointCost_convex_shape {q a kl kh : ℝ}
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hkl : 0 < kl) (hgap : q*kh^2 < 1) :
    ConvexOn ℝ (Icc kl kh) (fun k => upperJointCost q k a) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy s t hs ht hst
  have hxy := (convex_Icc kl kh) hx hy hs ht hst
  have hdomain {z : ℝ} (hz : z ∈ Icc kl kh) : q*z^2 < 1 := by
    have hz0 : 0 ≤ z := (hkl.trans_le hz.1).le
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz.2 2) hq).trans_lt hgap
  have hX := upperJointCost_hasSum (a := a) hq (hkl.trans_le hx.1) (hdomain hx)
  have hY := upperJointCost_hasSum (a := a) hq (hkl.trans_le hy.1) (hdomain hy)
  have hZ := upperJointCost_hasSum (a := a) hq (hkl.trans_le hxy.1) (hdomain hxy)
  have h := hasSum_le (fun n => ?_) hZ ((hX.mul_left s).add (hY.mul_left t))
  · simp only [smul_eq_mul] at hxy h ⊢
    have hqst : s*q+t*q=q := by
      calc
        _ = (s+t)*q := by ring
        _ = q := by rw [hst,one_mul]
    nlinarith
  have hc := (convexOn_pow (𝕜 := ℝ) (2*n+1)).2
    (show x ∈ Ici 0 by exact (hkl.trans_le hx.1).le)
    (show y ∈ Ici 0 by exact (hkl.trans_le hy.1).le) hs ht hst
  have hscale : 0 ≤ a*q^(n+2)/(n+2 : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hc hscale
  simp only [smul_eq_mul] at hh ⊢
  convert! hh using 1 <;> ring

def upperJointPrefactor (q a k : ℝ) : ℝ := Real.exp (upperJointCost q k a/2)

theorem upperJointPrefactor_convex_shape {q a kl kh : ℝ}
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hkl : 0 < kl) (hgap : q*kh^2 < 1) :
    ConvexOn ℝ (Icc kl kh) (fun k => upperJointPrefactor q a k) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy s t hs ht hst
  have hc := (upperJointCost_convex_shape hq ha hkl hgap).2 hx hy hs ht hst
  simp only [smul_eq_mul] at hc ⊢
  dsimp [upperJointPrefactor]
  have he := convexOn_exp.2 (mem_univ (upperJointCost q x a/2))
    (mem_univ (upperJointCost q y a/2)) hs ht hst
  simp only [smul_eq_mul] at he
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

theorem upperJointPrefactor_convex_third (q k al ah : ℝ) :
    ConvexOn ℝ (Icc al ah) (fun a => upperJointPrefactor q a k) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy s t hs ht hst
  simp only [smul_eq_mul]
  have hid : upperJointCost q k (s*x+t*y)/2 =
      s*(upperJointCost q k x/2)+t*(upperJointCost q k y/2) := by
    dsimp [upperJointCost]
    linear_combination -(q/2)*hst
  dsimp [upperJointPrefactor]
  rw [hid]
  exact convexOn_exp.2 (mem_univ _) (mem_univ _) hs ht hst

/-- Any finite endpoint entropy sum inherits separate convexity from its
joint prefactors. Its coefficients include the Riemann weight and decay. -/
theorem entropy_sum_separately_convex {n : ℕ} {q d : Fin n → ℝ}
    {al ah kl kh c : ℝ} (hd : ∀ i, 0 ≤ d i)
    (hq : ∀ i, 0 ≤ q i) (ha : 0 ≤ al) (hk : 0 < kl)
    (hgap : ∀ i, q i*kh^2 < 1) :
    (∀ k ∈ Icc kl kh, ConvexOn ℝ (Icc al ah)
      (fun a => c+∑ i, d i*upperJointPrefactor (q i) a k)) ∧
    (∀ a ∈ Icc al ah, ConvexOn ℝ (Icc kl kh)
      (fun k => c+∑ i, d i*upperJointPrefactor (q i) a k)) := by
  have hsum {l h : ℝ} (f : Fin n → ℝ → ℝ)
      (hc : ∀ i, ConvexOn ℝ (Icc l h) (f i)) :
      ConvexOn ℝ (Icc l h) (fun z => c+∑ i, d i*f i z) := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy s t hs ht hst
    simp only [smul_eq_mul]
    have hh : (∑ i, d i*f i (s*x+t*y)) ≤
        ∑ i, (s*(d i*f i x)+t*(d i*f i y)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := mul_le_mul_of_nonneg_left ((hc i).2 hx hy hs ht hst) (hd i)
      simp only [smul_eq_mul] at hh
      convert! hh using 1 <;> ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hh
    have hcst : s*c+t*c=c := by
      calc
        _ = (s+t)*c := by ring
        _ = c := by rw [hst,one_mul]
    nlinarith
  constructor
  · intro k hk'
    exact hsum (fun i a => upperJointPrefactor (q i) a k)
      (fun i => upperJointPrefactor_convex_third (q i) k al ah)
  · intro a ha'
    exact hsum (fun i k => upperJointPrefactor (q i) a k)
      (fun i => upperJointPrefactor_convex_shape (hq i) (ha.trans ha'.1) hk (hgap i))

end
end SingularValueBounds.KL
