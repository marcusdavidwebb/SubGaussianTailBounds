import SingularValueBounds.Shifts.BasicMoments
import SingularValueBounds.Scalar.Exponential

/-! # The current lower-shift moment argument
Both estimates use ratio Cauchy--Schwarz. The second estimate factors the
squared denominator exactly as in the paper, rather than using a tangent
majorant. The second estimate uses the strictly positive coefficient and
residual floor that occur in the lower shift.
-/
open MeasureTheory
namespace SingularValueBounds
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The lower-shift mean bound, directly from ratio Cauchy--Schwarz. -/
theorem current_shift_mean_lower {q e : Ω → ℝ} {a η M b : ℝ}
    (hq : Integrable q μ) (hq2 : Integrable (fun ω => q ω ^ 2) μ)
    (hqe : Integrable (fun ω => q ω * e ω) μ) (he : AEMeasurable e μ)
    (hq0 : ∀ ω, 0 ≤ q ω) (he0 : ∀ ω, 0 ≤ e ω)
    (ha : 0 < a) (hη : 0 ≤ η) (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hmean : (∫ ω, q ω ∂μ) = 1) (hsecond : (∫ ω, q ω ^ 2 ∂μ) ≤ M)
    (hexcess : (∫ ω, q ω * e ω ∂μ) ≤ b) :
    1 / (a + b + η * M) ≤ ∫ ω, q ω / (a + e ω + η * q ω) ∂μ := by
  let D := fun ω => a + e ω + η * q ω
  have hD : ∀ ω, 0 < D ω := fun ω => by
    dsimp [D]; have := hq0 ω; have := he0 ω; positivity
  have hdiv := (shift_integrable hq hq2 he hq0 he0 ha hη).1
  have hmul : Integrable (fun ω => q ω * D ω) μ := by
    convert! ((hq.const_mul a).add hqe).add (hq2.const_mul η) using 1
    funext ω; dsimp [D]; ring
  have hc := integral_ratio_cauchy hq0 hD hdiv hmul
  rw [hmean, one_pow] at hc
  have hmul_bound : (∫ ω, q ω * D ω ∂μ) ≤ a + b + η * M := by
    calc
      _ = ∫ ω, a * q ω + q ω * e ω + η * q ω ^ 2 ∂μ := by
        congr 1; funext ω; dsimp [D]; ring
      _ = a + (∫ ω, q ω * e ω ∂μ) + η * (∫ ω, q ω ^ 2 ∂μ) := by
        rw [integral_add (f := fun ω => a * q ω + q ω * e ω)
          ((hq.const_mul a).add hqe) (hq2.const_mul η),
          integral_add (hq.const_mul a) hqe]
        simp only [integral_const_mul, hmean, mul_one]
      _ ≤ _ := add_le_add (add_le_add_right hexcess a)
        (mul_le_mul_of_nonneg_left hsecond hη)
  have hnon : 0 ≤ ∫ ω, q ω / D ω ∂μ :=
    integral_nonneg (fun ω => div_nonneg (hq0 ω) (hD ω).le)
  exact (div_le_iff₀ (by positivity : 0 < a + b + η * M)).2
    (hc.trans (mul_le_mul_of_nonneg_left hmul_bound hnon))

/-- The lower-shift second moment, from the manuscript's denominator identity. -/
theorem current_shift_second_moment_upper {q e : Ω → ℝ} {a η M : ℝ}
    (hq : Integrable q μ) (hq2 : Integrable (fun ω => q ω ^ 2) μ)
    (he : AEMeasurable e μ) (hq0 : ∀ ω, 0 ≤ q ω) (he0 : ∀ ω, 0 ≤ e ω)
    (ha : 0 < a) (hη : 0 < η) (hM : 0 ≤ M) (hMa : η * M < a)
    (hmean : (∫ ω, q ω ∂μ) = 1) (hsecond : (∫ ω, q ω ^ 2 ∂μ) ≤ M) :
    (∫ ω, (q ω / (a + e ω + η * q ω)) ^ 2 ∂μ) ≤ M / (a + η * M) ^ 2 := by
  have hd := (shift_integrable hq hq2 he hq0 he0 ha hη.le).2
  have ha0 : 0 < a - η * M := sub_pos.mpr hMa
  let D := fun ω => (a - η * M) + (2 * η) * q ω
  let B := a + η * M
  have hD : ∀ ω, 0 < D ω := fun ω => by
    dsimp [D]; have := hq0 ω; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hqdiv : Integrable (fun ω => q ω / D ω) μ := by
    simpa only [add_zero] using
      (shift_integrable hq hq2 (aemeasurable_const : AEMeasurable (fun _ : Ω => (0 : ℝ)) μ)
        hq0 (fun _ => le_rfl) ha0 (show 0 ≤ 2 * η by positivity)).1
  have hq2div : Integrable (fun ω => q ω ^ 2 / D ω) μ := by
    apply (hq2.div_const (a - η * M)).mono'
      ((hq.aemeasurable.pow_const 2).div
        (aemeasurable_const.add (hq.aemeasurable.const_mul (2 * η)))).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖q ω ^ 2 / D ω‖ ≤ q ω ^ 2 / (a - η * M)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hD ω).le)]
    apply div_le_div_of_nonneg_left (sq_nonneg _) ha0
    dsimp [D]
    have := mul_nonneg (show 0 ≤ 2 * η by positivity) (hq0 ω)
    linarith
  have hratio : 1 / B ≤ ∫ ω, q ω / D ω ∂μ := by
    have h := current_shift_mean_lower (q := q) (e := fun _ => 0)
      (a := a - η * M) (η := 2 * η) (M := M) (b := 0)
      hq hq2 (by simpa using (integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) μ))
      aemeasurable_const hq0 (fun _ => le_rfl) ha0 (by positivity) hM le_rfl hmean hsecond
      (by simp)
    have hid : a - η * M + 2 * η * M = B := by dsimp [B]; ring
    simp only [add_zero] at h
    rw [hid] at h
    exact h
  have hidentity : (∫ ω, q ω ^ 2 / D ω ∂μ) =
      (1 - (a - η * M) * (∫ ω, q ω / D ω ∂μ)) / (2 * η) := by
    calc
      _ = ∫ ω, (q ω - (a - η * M) * (q ω / D ω)) / (2 * η) ∂μ := by
        congr 1; funext ω
        field_simp [(hD ω).ne', hη.ne']
        dsimp [D]; ring
      _ = _ := by
        rw [integral_div, integral_sub hq (hqdiv.const_mul (a - η * M)),
          integral_const_mul, hmean]
  have hq2bound : (∫ ω, q ω ^ 2 / D ω ∂μ) ≤ M / B := by
    rw [hidentity]
    calc
      _ ≤ (1 - (a - η * M) * (1 / B)) / (2 * η) :=
        div_le_div_of_nonneg_right
          (sub_le_sub_left (mul_le_mul_of_nonneg_left hratio ha0.le) 1) (by positivity)
      _ = M / B := by
        field_simp [hη.ne', hB.ne']
        dsimp [B]; ring
  have hmajor : (∫ ω, (q ω / (a + e ω + η * q ω)) ^ 2 ∂μ) ≤
      (∫ ω, q ω ^ 2 / D ω ∂μ) / B := by
    have hi := integral_mono hd (hq2div.div_const B) (fun ω => by
      apply (shift_sq_le (q ω) (e ω) a η (hq0 ω) (he0 ω) ha hη.le).trans
      rw [div_div]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (hD ω) hB)
      have hid : (a + η * q ω) ^ 2 - D ω * B = η ^ 2 * (q ω - M) ^ 2 := by
        dsimp [D, B]; ring
      nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg (q ω - M))])
    simpa only [integral_div] using hi
  calc
    _ ≤ (∫ ω, q ω ^ 2 / D ω ∂μ) / B := hmajor
    _ ≤ (M / B) / B := div_le_div_of_nonneg_right hq2bound hB.le
    _ = M / (a + η * M) ^ 2 := by simp only [div_div, B, pow_two]
end SingularValueBounds
