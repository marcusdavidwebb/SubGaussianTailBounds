import SingularValueBounds.Scalar.CauchySchwarz
import SingularValueBounds.Scalar.UpperExponentialTools

/-! # Scalar exponential bounds (current paper, Lemma 4.1)
The lower bound uses ratio Cauchy--Schwarz; the upper bound uses the
convex-secant and integrated-tail calculation.
-/
open MeasureTheory Set
namespace SingularValueBounds
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cauchy--Schwarz in ratio form. -/
theorem integral_ratio_cauchy {q D : Ω → ℝ}
    (hq0 : ∀ ω, 0 ≤ q ω) (hD0 : ∀ ω, 0 < D ω)
    (hdiv : Integrable (fun ω => q ω / D ω) μ)
    (hmul : Integrable (fun ω => q ω * D ω) μ) :
    (∫ ω, q ω ∂μ) ^ 2 ≤
      (∫ ω, q ω / D ω ∂μ) * (∫ ω, q ω * D ω ∂μ) := by
  have hs₁ : ∀ ω, (Real.sqrt (q ω / D ω)) ^ 2 = q ω / D ω :=
    fun ω => Real.sq_sqrt (div_nonneg (hq0 ω) (hD0 ω).le)
  have hs₂ : ∀ ω, (Real.sqrt (q ω * D ω)) ^ 2 = q ω * D ω :=
    fun ω => Real.sq_sqrt (mul_nonneg (hq0 ω) (hD0 ω).le)
  have h₁ : MemLp (fun ω => Real.sqrt (q ω / D ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hdiv.aestronglyMeasurable)).2
    simpa only [hs₁] using hdiv
  have h₂ : MemLp (fun ω => Real.sqrt (q ω * D ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hmul.aestronglyMeasurable)).2
    simpa only [hs₂] using hmul
  have he : ∀ ω, Real.sqrt (q ω / D ω) * Real.sqrt (q ω * D ω) = q ω := by
    intro ω
    rw [← Real.sqrt_mul (div_nonneg (hq0 ω) (hD0 ω).le)]
    have hid : q ω / D ω * (q ω * D ω) = (q ω) ^ 2 := by
      field_simp [(hD0 ω).ne'] <;> ring
    rw [hid, Real.sqrt_sq (hq0 ω)]
  simpa only [he, hs₁, hs₂] using integral_mul_sq_le h₁ h₂

/-- Lemma 4.1(1), following the paper's Cauchy--Schwarz argument. -/
theorem scalar_lower_exponential [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {v ℓ : ℝ} (hY0 : ∀ ω, 0 ≤ Y ω)
    (hY : Integrable Y μ) (hY2 : Integrable (fun ω => Y ω ^ 2) μ)
    (hv : 0 < v) (hℓ : 0 ≤ ℓ)
    (hmean : 1 ≤ ∫ ω, Y ω ∂μ) (hsecond : (∫ ω, Y ω ^ 2 ∂μ) ≤ v) :
    Integrable (fun ω => Real.exp (-ℓ * Y ω)) μ ∧
      (∫ ω, Real.exp (-ℓ * Y ω) ∂μ) ≤ Real.exp (-ℓ / (1 + v * ℓ)) := by
  let D : Ω → ℝ := fun ω => 1 + ℓ * Y ω
  have hD : ∀ ω, 0 < D ω := fun ω => by
    dsimp [D]; have := hY0 ω; positivity
  have hD1 : ∀ ω, 1 ≤ D ω := fun ω => by
    dsimp [D]; have := mul_nonneg hℓ (hY0 ω); linarith
  have hdiv : Integrable (fun ω => Y ω / D ω) μ := by
    apply hY.mono' (hY.aemeasurable.div
      (aemeasurable_const.add (hY.aemeasurable.const_mul ℓ))).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖Y ω / D ω‖ ≤ Y ω
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hY0 ω) (hD ω).le)]
    exact div_le_self (hY0 ω) (hD1 ω)
  have hmul : Integrable (fun ω => Y ω * D ω) μ := by
    convert! hY.add (hY2.const_mul ℓ) using 1
    funext ω; dsimp [D]; ring
  have hc := integral_ratio_cauchy hY0 hD hdiv hmul
  have hmul_eq : (∫ ω, Y ω * D ω ∂μ) =
      (∫ ω, Y ω ∂μ) + ℓ * (∫ ω, Y ω ^ 2 ∂μ) := by
    calc
      _ = ∫ ω, Y ω + ℓ * Y ω ^ 2 ∂μ := by
        congr 1; funext ω; dsimp [D]; ring
      _ = _ := by rw [integral_add hY (hY2.const_mul ℓ), integral_const_mul]
  rw [hmul_eq] at hc
  have hd0 : 0 ≤ ∫ ω, Y ω / D ω ∂μ :=
    integral_nonneg (fun ω => div_nonneg (hY0 ω) (hD ω).le)
  have hmean0 : 0 ≤ ∫ ω, Y ω ∂μ := le_trans zero_le_one hmean
  have hden : 0 < (∫ ω, Y ω ∂μ) + ℓ * v := by positivity
  have hratio : 1 / (1 + ℓ * v) ≤ ∫ ω, Y ω / D ω ∂μ := by
    have hc' : (∫ ω, Y ω ∂μ) ^ 2 ≤
        (∫ ω, Y ω / D ω ∂μ) * ((∫ ω, Y ω ∂μ) + ℓ * v) := by
      exact hc.trans (mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left hsecond hℓ) _) hd0)
    have hr : 1 / (1 + ℓ * v) ≤
        (∫ ω, Y ω ∂μ) ^ 2 / ((∫ ω, Y ω ∂μ) + ℓ * v) := by
      apply (div_le_div_iff₀ (by positivity) hden).2
      nlinarith [mul_nonneg (mul_nonneg hℓ hv.le)
        (show 0 ≤ (∫ ω, Y ω ∂μ) ^ 2 - 1 by nlinarith)]
    exact hr.trans ((div_le_iff₀ hden).2 hc')
  have hexp : Integrable (fun ω => Real.exp (-ℓ * Y ω)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.continuous_exp.comp_aestronglyMeasurable
        (hY.aestronglyMeasurable.const_mul (-ℓ)))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hℓ) (hY0 ω))
  refine ⟨hexp, ?_⟩
  have hpoint : ∀ ω, Real.exp (-ℓ * Y ω) ≤ 1 - ℓ * (Y ω / D ω) := by
    intro ω
    have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (ℓ * Y ω))
      (Real.exp_nonneg (-ℓ * Y ω))
    have hi : Real.exp (ℓ * Y ω) * Real.exp (-ℓ * Y ω) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    rw [hi] at hm
    have hid : (1 - ℓ * (Y ω / D ω)) * D ω = 1 := by
      field_simp [(hD ω).ne']; dsimp [D]; ring
    apply (mul_le_mul_iff_left₀ (hD ω)).mp
    rw [hid]
    dsimp [D]
    nlinarith
  have hi := integral_mono hexp ((integrable_const 1).sub (hdiv.const_mul ℓ)) hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_const 1) (hdiv.const_mul ℓ), integral_const_mul] at hi
  simp only [integral_const] at hi
  simp only [probReal_univ, smul_eq_mul, one_mul] at hi
  calc
    _ ≤ 1 - ℓ * (∫ ω, Y ω / D ω ∂μ) := hi
    _ ≤ 1 - ℓ / (1 + v * ℓ) := by
      have := mul_le_mul_of_nonneg_left hratio hℓ
      rw [mul_comm ℓ v] at this
      simpa only [mul_one_div] using sub_le_sub_left this 1
    _ ≤ Real.exp (-ℓ / (1 + v * ℓ)) := by
      simpa [sub_eq_add_neg, add_comm, neg_div] using
        Real.add_one_le_exp (-ℓ / (1 + v * ℓ))

/-- Lemma 4.1(2), the upper exponential estimate without centring. -/
theorem scalar_upper_exponential [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {K ℓ : ℝ} (hK : 1 ≤ K)
    (hY : AEMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hℓ : 0 ≤ ℓ) (hℓv : ℓ * (8 * K ^ 2 * logParameter K) < 1)
    (htail : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x < Y ω} ≤
      Real.sqrt 3 * Real.exp (-(x / (3 * K ^ 2))))
    (hmean : (∫ ω, Y ω ∂μ) ≤ 1) :
    Integrable (fun ω => Real.exp (ℓ * Y ω)) μ ∧
      (∫ ω, Real.exp (ℓ * Y ω) ∂μ) ≤
        Real.exp (ℓ / (1 - (8 * K ^ 2 * logParameter K) * ℓ)) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL := one_le_logParameter hK
  apply upper_mgf_of_mean_tail hY hY0 (Real.sqrt_nonneg 3)
    (show 0 < 1 / (3 * K ^ 2) by positivity) (by positivity)
    (show 2 ≤ (1 / (3 * K ^ 2)) * (8 * K ^ 2 * logParameter K) from ?_)
    ((scalar_tail_coefficient hK).trans (by norm_num)) hℓ hℓv ?_ hmean
  · have hi : (1 / (3 * K ^ 2)) * (8 * K ^ 2 * logParameter K) =
        (8 / 3 : ℝ) * logParameter K := by field_simp [hK0.ne'] <;> ring
    rw [hi]
    linarith
  · intro x hx
    convert! htail x hx using 1
    congr 2
    ring
end
end SingularValueBounds
