import SingularValueBounds.Scalar.TailSecond

/-! # Scalar tools for the upper exponential estimate

Convex secants, tail integration and the rational exponential majorant used
in the scalar exponential lemma.
-/

open MeasureTheory Set
open scoped ENNReal

namespace SingularValueBounds

noncomputable section

set_option maxHeartbeats 600000

/-- A rational majorant for the exponential, used after truncating the tail. -/
theorem exp_le_pade {t : ℝ} (ht : 0 ≤ t) (ht2 : t < 2) :
    Real.exp t ≤ (2 + t) / (2 - t) := by
  have hm : Monotone (fun x : ℝ => (2 + x) - (2 - x) * Real.exp x) := by
    apply monotone_of_hasDerivAt_nonneg
      (f' := fun x : ℝ => 1 + (x - 1) * Real.exp x)
    · intro x
      convert ((hasDerivAt_const x 2).add (hasDerivAt_id x)).sub
        (((hasDerivAt_const x 2).sub (hasDerivAt_id x)).mul (Real.hasDerivAt_exp x)) using 1 <;>
        simp only [id_eq] <;> ring
    · intro x
      have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
      have hid : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
      rw [hid] at he
      change (0 : ℝ) ≤ 1 + (x - 1) * Real.exp x
      nlinarith
  have hh := hm ht
  norm_num at hh
  apply (le_div_iff₀ (by linarith : 0 < 2 - t)).2
  nlinarith

/-- A convex secant bound with an exact shifted exponential remainder. -/
theorem exp_truncation_majorant {y v ℓ : ℝ} (hy : 0 ≤ y) (hv : 0 < v) :
    Real.exp (ℓ * y) ≤
      1 + ((Real.exp (ℓ * v) - 1) / v) * y +
      (Real.exp (ℓ * v) * (Real.exp (ℓ * max (y - v) 0) - 1) -
        ((Real.exp (ℓ * v) - 1) / v) * max (y - v) 0) := by
  by_cases hyv : y ≤ v
  · rw [max_eq_right (sub_nonpos.mpr hyv)]
    simp only [mul_zero, Real.exp_zero, sub_self, mul_zero, add_zero]
    have ha : 0 ≤ 1 - y / v := by apply sub_nonneg.mpr; exact (div_le_one hv).2 hyv
    have hb : 0 ≤ y / v := div_nonneg hy hv.le
    have hc := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (ℓ * v))
      ha hb (by ring : 1 - y / v + y / v = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    convert hc using 1 <;> field_simp <;> ring
  · rw [max_eq_left (by linarith : 0 ≤ y - v)]
    have he : Real.exp (ℓ * y) = Real.exp (ℓ * v) * Real.exp (ℓ * (y - v)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    apply le_of_eq
    field_simp
    ring

/-- The rational arithmetic behind the sharp upper Bernstein denominator. -/
theorem truncated_exp_rational_bound {t a B : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (ha : 0 ≤ a) (hat : a ≤ t / 2)
    (hB : 0 ≤ B) (hB1 : B ≤ 1 / 2) :
    (Real.exp t - 1) + B * (t * Real.exp t / (1 - a) - Real.exp t + 1) ≤
      t + t ^ 2 / (1 - t) := by
  have ha1 : 0 < 1 - a := by linarith
  have ht2 : 0 < 2 - t := by linarith
  have ht1' : 0 < 1 - t := by linarith
  have htden : 0 < 1 - t / 2 := by linarith
  have htan : Real.exp t - 1 ≤ t * Real.exp t := by
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_nonneg t)
    have hi : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    rw [hi] at hh
    nlinarith
  have hd : t * Real.exp t ≤ t * Real.exp t / (1 - a) := by
    apply (le_div_iff₀ ha1).2
    nlinarith [mul_nonneg (mul_nonneg ht (Real.exp_nonneg t)) ha]
  have hH : 0 ≤ t * Real.exp t / (1 - a) - Real.exp t + 1 := by linarith
  have hdiv : t * Real.exp t / (1 - a) ≤ t * Real.exp t / (1 - t / 2) :=
    div_le_div_of_nonneg_left (mul_nonneg ht (Real.exp_nonneg t)) htden (by linarith)
  have hp := exp_le_pade ht (by linarith : t < 2)
  calc
    _ ≤ (Real.exp t - 1) + (1 / 2 : ℝ) *
        (t * Real.exp t / (1 - a) - Real.exp t + 1) := by gcongr
    _ ≤ (Real.exp t - 1) + (1 / 2 : ℝ) *
        (t * Real.exp t / (1 - t / 2) - Real.exp t + 1) := by linarith
    _ = (1 / 2 : ℝ) * (Real.exp t * ((2 + t) / (2 - t)) - 1) := by
      field_simp
      ring
    _ ≤ (1 / 2 : ℝ) * (((2 + t) / (2 - t)) ^ 2 - 1) := by
      have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ (2 + t) / (2 - t) by positivity)
      nlinarith
    _ ≤ t + t ^ 2 / (1 - t) := by
      apply (mul_le_mul_right ht1').mp
      have he : (t + t ^ 2 / (1 - t)) * (1 - t) = t := by field_simp; ring
      rw [he]
      apply (mul_le_mul_right (sq_pos_of_pos ht2)).mp
      have he' : ((1 / 2 : ℝ) * (((2 + t) / (2 - t)) ^ 2 - 1) * (1 - t)) *
          (2 - t) ^ 2 = 4 * t * (1 - t) := by field_simp; ring
      rw [he']
      nlinarith [mul_nonneg ht (sq_nonneg t)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Integrating a shifted exponential remainder directly by the tail formula.
This packages the power-series truncation argument without an infinite sum. -/
theorem exponential_tail_remainder [IsFiniteMeasure μ] {U : Ω → ℝ} {D r ℓ E b : ℝ}
    (hU : AEMeasurable U μ) (hU0 : ∀ ω, 0 ≤ U ω)
    (hD : 0 ≤ D) (hr : 0 < r) (hℓ : 0 ≤ ℓ) (hℓr : ℓ < r)
    (hE : 0 ≤ E) (hb : b ≤ E * ℓ)
    (htail : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < U ω} ≤ D * Real.exp (-(r * x))) :
    Integrable (fun ω => E * (Real.exp (ℓ * U ω) - 1) - b * U ω) μ ∧
      (∫ ω, E * (Real.exp (ℓ * U ω) - 1) - b * U ω ∂μ) ≤
        D * (E * ℓ / (r - ℓ) - b / r) := by
  let g : ℝ → ℝ := fun x => E * ℓ * Real.exp (ℓ * x) - b
  let F : ℝ → ℝ := fun x => E * (Real.exp (ℓ * x) - 1) - b * x
  let H : ℝ → ℝ := fun x => E * ℓ * Real.exp (-(r - ℓ) * x) - b * Real.exp (-r * x)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hg0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ g x := by
    intro x hx
    have he : 1 ≤ Real.exp (ℓ * x) := Real.one_le_exp_iff.mpr (mul_nonneg hℓ hx)
    have hm := mul_le_mul_of_nonneg_left he (mul_nonneg hE hℓ)
    dsimp [g]
    linarith
  have hFderiv : ∀ x : ℝ, HasDerivAt F (g x) x := by
    intro x
    convert ((((hasDerivAt_id x).const_mul ℓ).exp.sub_const 1).const_mul E).sub
      ((hasDerivAt_id x).const_mul b) using 1 <;> simp only [id_eq] <;> dsimp [F, g] <;> ring
  have hFi : ∀ x : ℝ, (∫ t in (0 : ℝ)..x, g t) = F x := by
    intro x
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hFderiv t) (hg.intervalIntegrable 0 x)
    simpa [F] using hi
  have hF0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x := by
    intro x hx
    rw [← hFi]
    exact intervalIntegral.integral_nonneg hx (fun t ht => hg0 t ht.1)
  have hHi : IntegrableOn H (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (by linarith : -(r - ℓ) < 0) 0).const_mul (E * ℓ)).sub
      ((integrableOn_exp_mul_Ioi (by linarith : -r < 0) 0).const_mul b)
  have hH : ∀ x, H x = Real.exp (-(r * x)) * g x := by
    intro x
    dsimp [H, g]
    have he : Real.exp (-(r - ℓ) * x) = Real.exp (-(r * x)) * Real.exp (ℓ * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have hH0 : ∀ᵐ x ∂volume.restrict (Ioi 0), 0 ≤ H x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [hH]
    exact mul_nonneg (Real.exp_nonneg _) (hg0 x hx.le)
  have hHint : (∫ x in Ioi 0, H x) = E * ℓ / (r - ℓ) - b / r := by
    dsimp [H]
    rw [integral_sub
      ((integrableOn_exp_mul_Ioi (by linarith : -(r - ℓ) < 0) 0).const_mul (E * ℓ))
      ((integrableOn_exp_mul_Ioi (by linarith : -r < 0) 0).const_mul b),
      integral_const_mul, integral_const_mul,
      integral_exp_mul_Ioi (by linarith : -(r - ℓ) < 0) 0,
      integral_exp_mul_Ioi (by linarith : -r < 0) 0]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
    ring
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall hU0) hU (fun t _ => hg.intervalIntegrable 0 t)
    (show ∀ᵐ x ∂volume.restrict (Ioi 0), 0 ≤ g x from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hg0 x hx.le)
  simp_rw [hFi] at hlayer
  have hbound : (∫⁻ ω, ENNReal.ofReal (F (U ω)) ∂μ) ≤
      ENNReal.ofReal (D * (E * ℓ / (r - ℓ) - b / r)) := by
    rw [hlayer]
    calc
      (∫⁻ x in Ioi 0, μ {ω | x < U ω} * ENNReal.ofReal (g x)) ≤
          ∫⁻ x in Ioi 0, ENNReal.ofReal (D * H x) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have ht := ENNReal.ofReal_le_ofReal (htail x hx.le)
        rw [ofReal_measureReal] at ht
        calc
          _ ≤ ENNReal.ofReal (D * Real.exp (-(r * x))) * ENNReal.ofReal (g x) :=
            mul_le_mul_right' ht _
          _ = ENNReal.ofReal (D * H x) := by
            rw [← ENNReal.ofReal_mul (by positivity), hH]
            congr 1
            ring
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hHi.const_mul D)
          (hH0.mono fun x hx => mul_nonneg hD hx), integral_const_mul, hHint]
  have hFm : AEStronglyMeasurable (fun ω => F (U ω)) μ := by
    dsimp [F]
    exact (((hU.const_mul ℓ).exp.sub_const 1).const_mul E |>.sub (hU.const_mul b)).aestronglyMeasurable
  have hFn : 0 ≤ᵐ[μ] fun ω => F (U ω) := Filter.Eventually.of_forall (fun ω => hF0 _ (hU0 ω))
  have hInt := (lintegral_ofReal_ne_top_iff_integrable hFm hFn).1
    (ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top))
  refine ⟨hInt, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hFn] at hbound
  apply (ENNReal.ofReal_le_ofReal_iff ?_).1 hbound
  rw [← hHint]
  exact mul_nonneg hD (integral_nonneg_of_ae hH0)

/-- The upper exponential estimate from a mean and an exponential tail. -/
theorem upper_mgf_of_mean_tail [IsProbabilityMeasure μ] {Y : Ω → ℝ} {C r v ℓ : ℝ}
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hC : 0 ≤ C) (hr : 0 < r) (hv : 0 < v) (hrv : 2 ≤ r * v)
    (hsmall : C * Real.exp (-(r * v)) / r ≤ 1 / 2)
    (hℓ : 0 ≤ ℓ) (hℓv : ℓ * v < 1)
    (htail : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < Y ω} ≤
      C * Real.exp (-(r * x)))
    (hmean : (∫ ω, Y ω ∂μ) ≤ 1) :
    Integrable (fun ω => Real.exp (ℓ * Y ω)) μ ∧
      (∫ ω, Real.exp (ℓ * Y ω) ∂μ) ≤ Real.exp (ℓ / (1 - v * ℓ)) := by
  have hℓr : ℓ < r := by nlinarith
  have hYint : Integrable Y μ := by
    simpa only [Nat.zero_add, pow_one] using
      (exponential_tail_moment hY hY0 hC hr htail 0).1
  let U : Ω → ℝ := fun ω => max (Y ω - v) 0
  let E : ℝ := Real.exp (ℓ * v)
  let b : ℝ := (E - 1) / v
  let D : ℝ := C * Real.exp (-(r * v))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb0 : 0 ≤ b := by
    apply div_nonneg _ hv.le
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hℓ hv.le))
  have hb : b ≤ E * ℓ := by
    apply (div_le_iff₀ hv).2
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(ℓ * v)))
      (Real.exp_nonneg (ℓ * v))
    have hi : Real.exp (-(ℓ * v)) * Real.exp (ℓ * v) = 1 := by
      rw [← Real.exp_add]; simp
    rw [hi] at he
    dsimp [E]
    nlinarith
  have htU : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < U ω} ≤
      D * Real.exp (-(r * x)) := by
    intro x hx
    have hs : {ω | x < U ω} = {ω | x + v < Y ω} := by
      ext ω
      dsimp [U]
      rw [lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        exact Or.inl (by linarith)
    rw [hs]
    calc
      _ ≤ C * Real.exp (-(r * (x + v))) := htail _ (by linarith)
      _ = _ := by
        dsimp [D]
        rw [show -(r * (x + v)) = -(r * v) + -(r * x) by ring, Real.exp_add]
        ring
  have hR := exponential_tail_remainder ((hY.sub_const v).max aemeasurable_const)
    (fun ω => le_max_right _ _) hD hr hℓ hℓr
    (show 0 ≤ E from Real.exp_nonneg _) hb htU
  let R : Ω → ℝ := fun ω => E * (Real.exp (ℓ * U ω) - 1) - b * U ω
  have hRint : Integrable R μ := hR.1
  have hpoly : Integrable (fun ω => 1 + b * Y ω + R ω) μ :=
    ((integrable_const 1).add (hYint.const_mul b)).add hRint
  have hpoint : ∀ ω, Real.exp (ℓ * Y ω) ≤ 1 + b * Y ω + R ω := by
    intro ω
    exact exp_truncation_majorant (hY0 ω) hv
  have heint : Integrable (fun ω => Real.exp (ℓ * Y ω)) μ := by
    apply hpoly.mono' ((hY.const_mul ℓ).exp.aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpoint ω
  have hpolyint : (∫ ω, 1 + b * Y ω + R ω ∂μ) =
      1 + b * (∫ ω, Y ω ∂μ) + (∫ ω, R ω ∂μ) := by
    rw [integral_add (f := fun ω => 1 + b * Y ω) (g := R)
      ((integrable_const 1).add (hYint.const_mul b)) hRint,
      integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => b * Y ω)
        (integrable_const 1) (hYint.const_mul b), integral_const_mul]
    simp
  have hexp : (∫ ω, Real.exp (ℓ * Y ω) ∂μ) ≤
      1 + b + D * (E * ℓ / (r - ℓ) - b / r) := by
    have hm := mul_le_mul_of_nonneg_left hmean hb0
    have hi := integral_mono_ae heint hpoly (Filter.Eventually.of_forall hpoint)
    rw [hpolyint] at hi
    have hRi : (∫ ω, R ω ∂μ) ≤ D * (E * ℓ / (r - ℓ) - b / r) := hR.2
    nlinarith
  have hrat := truncated_exp_rational_bound (mul_nonneg hℓ hv.le) hℓv
    (div_nonneg hℓ hr.le) (show ℓ / r ≤ ℓ * v / 2 by
      apply (div_le_iff₀ hr).2
      nlinarith [mul_nonneg hℓ (sub_nonneg.mpr hrv)])
    (div_nonneg hD hr.le) hsmall
  have hscalar : b + D * (E * ℓ / (r - ℓ) - b / r) ≤
      ℓ + v * ℓ ^ 2 / (1 - v * ℓ) := by
    apply (mul_le_mul_right hv).mp
    have hi₁ : (b + D * (E * ℓ / (r - ℓ) - b / r)) * v =
        (Real.exp (ℓ * v) - 1) + D / r *
          ((ℓ * v) * Real.exp (ℓ * v) / (1 - ℓ / r) - Real.exp (ℓ * v) + 1) := by
      dsimp [b, E]
      field_simp [hv.ne', hr.ne', sub_ne_zero.mpr hℓr.ne]
      ring
    have hi₂ : (ℓ + v * ℓ ^ 2 / (1 - v * ℓ)) * v =
        ℓ * v + (ℓ * v) ^ 2 / (1 - ℓ * v) := by
      rw [mul_comm v ℓ]
      ring
    rw [hi₁, hi₂]
    exact hrat
  have hun : (∫ ω, Real.exp (ℓ * Y ω) ∂μ) ≤
      1 + ℓ + v * ℓ ^ 2 / (1 - v * ℓ) := by linarith
  refine ⟨heint, hun.trans ?_⟩
  have hid : ℓ + v * ℓ ^ 2 / (1 - v * ℓ) = ℓ / (1 - v * ℓ) := by
    have hd : 1 - v * ℓ ≠ 0 := by nlinarith
    field_simp [hd]
    ring
  rw [add_assoc, hid]
  simpa only [add_comm] using Real.add_one_le_exp (ℓ / (1 - v * ℓ))

end
end SingularValueBounds
