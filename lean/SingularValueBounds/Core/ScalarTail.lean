import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Moment bounds from an exponential tail -/

open MeasureTheory Set
open scoped ENNReal

namespace SingularValueBounds

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A nonnegative random variable with an exponential tail has all positive
integer moments, with the usual factorial bound. -/
theorem exponential_tail_moment {Y : Ω → ℝ} {C r : ℝ}
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hC : 0 ≤ C) (hr : 0 < r)
    (htail : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < Y ω} ≤ C * Real.exp (-(r * x)))
    (n : ℕ) :
    Integrable (fun ω => Y ω ^ (n + 1)) μ ∧
      (∫ ω, Y ω ^ (n + 1) ∂μ) ≤ C * ((n + 1).factorial : ℝ) / r ^ (n + 1) := by
  let g : ℝ → ℝ := fun x => x ^ n * Real.exp (-(r * x))
  have hg : IntegrableOn g (Ioi 0) := by
    have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (n : ℝ)) (p := 1) (b := r)
      (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (by norm_num) hr
    simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using hi
  have hg0 : ∀ᵐ x ∂volume.restrict (Ioi 0), 0 ≤ g x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    dsimp [g]
    positivity
  have hgi : (∫ x in Ioi 0, g x) = (1 / r) ^ (n + 1) * (n.factorial : ℝ) := by
    have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (n : ℝ) + 1) (by positivity) hr
    simp only [add_sub_cancel_right, Real.rpow_natCast,
      Real.Gamma_nat_eq_factorial] at hi
    have hncast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
    rw [hncast, Real.rpow_natCast] at hi
    exact hi
  have hpow0 : 0 ≤ᵐ[μ] fun ω => Y ω ^ (n + 1) :=
    Filter.Eventually.of_forall (fun ω => pow_nonneg (hY0 ω) _)
  have hpowm : AEStronglyMeasurable (fun ω => Y ω ^ (n + 1)) μ :=
    (hY.pow_const _).aestronglyMeasurable
  have hlayer : (∫⁻ ω, ENNReal.ofReal (Y ω ^ (n + 1)) ∂μ) =
      ENNReal.ofReal (n + 1 : ℝ) *
        ∫⁻ x in Ioi 0, μ {ω | x < Y ω} * ENNReal.ofReal (x ^ n) := by
    have hi := lintegral_rpow_eq_lintegral_meas_lt_mul μ
      (Filter.Eventually.of_forall hY0) hY (p := (n : ℝ) + 1) (by positivity)
    simp only [add_sub_cancel_right, Real.rpow_natCast] at hi
    have hncast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
    rw [hncast] at hi
    simp_rw [Real.rpow_natCast] at hi
    simpa only [Nat.cast_add, Nat.cast_one] using hi
  have hlbound : (∫⁻ ω, ENNReal.ofReal (Y ω ^ (n + 1)) ∂μ) ≤
      ENNReal.ofReal (C * ((n + 1).factorial : ℝ) / r ^ (n + 1)) := by
    rw [hlayer]
    calc
      ENNReal.ofReal (n + 1 : ℝ) *
          (∫⁻ x in Ioi 0, μ {ω | x < Y ω} * ENNReal.ofReal (x ^ n)) ≤
          ENNReal.ofReal (n + 1 : ℝ) *
          (∫⁻ x in Ioi 0, ENNReal.ofReal (C * g x)) := by
        apply mul_le_mul_right
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have ht := ENNReal.ofReal_le_ofReal (htail x hx.le)
        rw [ofReal_measureReal] at ht
        calc
          μ {ω | x < Y ω} * ENNReal.ofReal (x ^ n) ≤
              ENNReal.ofReal (C * Real.exp (-(r * x))) * ENNReal.ofReal (x ^ n) :=
            mul_le_mul_left ht _
          _ = ENNReal.ofReal (C * g x) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            dsimp [g]
            ring
      _ = ENNReal.ofReal (n + 1 : ℝ) *
          ENNReal.ofReal (C * ((1 / r) ^ (n + 1) * (n.factorial : ℝ))) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hg.const_mul C)
          (hg0.mono fun x hx => mul_nonneg hC hx), integral_const_mul, hgi]
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_pow]
        ring
  have hint : Integrable (fun ω => Y ω ^ (n + 1)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hpowm hpow0).1
      (ne_of_lt (lt_of_le_of_lt hlbound ENNReal.ofReal_lt_top))
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hpow0] at hlbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlbound

/-- Tail integration after truncating at an arbitrary nonnegative level. -/
theorem exponential_tail_positive_part_moment {Y : Ω → ℝ} {C r t : ℝ}
    (hY : AEMeasurable Y μ) (hC : 0 ≤ C) (hr : 0 < r) (ht : 0 ≤ t)
    (htail : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < Y ω} ≤ C * Real.exp (-(r * x)))
    (n : ℕ) :
    Integrable (fun ω => max (Y ω - t) 0 ^ (n + 1)) μ ∧
      (∫ ω, max (Y ω - t) 0 ^ (n + 1) ∂μ) ≤
        (C * Real.exp (-(r * t))) * ((n + 1).factorial : ℝ) / r ^ (n + 1) := by
  apply exponential_tail_moment ((hY.sub_const t).max aemeasurable_const)
    (fun ω => le_max_right _ _) (by positivity) hr _ n
  intro x hx
  have hs : {ω | x < max (Y ω - t) 0} = {ω | x + t < Y ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [lt_max_iff]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      exact Or.inl (by linarith)
  rw [hs]
  calc
    μ.real {ω | x + t < Y ω} ≤ C * Real.exp (-(r * (x + t))) :=
      htail (x + t) (add_nonneg hx ht)
    _ = (C * Real.exp (-(r * t))) * Real.exp (-(r * x)) := by
      rw [show -(r * (x + t)) = -(r * t) + -(r * x) by ring, Real.exp_add]
      ring

end SingularValueBounds
