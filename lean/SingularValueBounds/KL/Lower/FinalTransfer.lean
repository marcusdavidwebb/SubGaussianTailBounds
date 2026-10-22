import SingularValueBounds.KL.Transfer

/-! Final scalar normalizations of the mixed-profile transfer. These lemmas
retain the explicit process input; the public theorem supplies it from the
proved mixed correction rule. -/
open MeasureTheory ProbabilityTheory
namespace SingularValueBounds.KL
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m n : ℕ} [NeZero n]

theorem lower_tail_general_from_mixed_input
    (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ) {K H : ℝ}
    (hK : 1 ≤ K) (hH : 0 < H) (hHbound : H ≤ 96/25)
    (hprocess : ∀ b : ℝ, 0 < b →
      Nonempty (LowerTransferInput μ X
        (K^2*n+2*K^2*logParameter K*H*Real.sqrt n)
        ((499/100)*K^2*logParameter K) b))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | smallestSingularValue (rowMatrix X ω) ≤
      LowerThreshold generalConstants m n K t} ≤ Real.exp (-t^2/2) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL : 0 < logParameter K := lt_of_lt_of_le zero_lt_one (one_le_logParameter hK)
  let N := K^2*n+2*K^2*logParameter K*H*Real.sqrt n
  let q := Real.sqrt (499/200:ℝ)*K*Real.sqrt (logParameter K)
  have hN : 0 < N := by
    have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
    dsimp [N]
    positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hν : 2*q^2 = (499/100:ℝ)*K^2*logParameter K := by
    dsimp [q]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 499/200),
      Real.sq_sqrt hL.le]
    ring
  have h := lower_transfer X ((NeZero.pos n).trans_le hnm)
    (Real.sqrt_pos.mpr hN) (Real.sq_sqrt hN.le)
    (mixed_dimension_cost_lt (n := n) hK0 hL hH) hq
    (fun b hb => by rw [hν]; exact hprocess b hb) ht
  have hbeta : Real.sqrt (499/200:ℝ) ≤ (79/50:ℝ) := by
    exact Real.sqrt_le_iff.mpr (by norm_num)
  have hqbound : q*t ≤ (79/50:ℝ)*K*Real.sqrt (logParameter K)*t := by
    dsimp [q]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbeta hK0.le) (Real.sqrt_nonneg _)) ht
  have hDbound : K*logParameter K*H ≤ (96/25:ℝ)*K*logParameter K := by
    nlinarith [mul_le_mul_of_nonneg_left hHbound (mul_nonneg hK0.le hL.le)]
  apply le_trans (measureReal_mono ?_) h
  intro ω hω
  change smallestSingularValue (rowMatrix X ω) ≤ LowerThreshold generalConstants m n K t at hω
  change smallestSingularValue (rowMatrix X ω) ≤
    Real.sqrt m-(K*Real.sqrt n+K*logParameter K*H)-q*t
  dsimp [LowerThreshold, generalConstants] at hω
  linarith

theorem lower_tail_one_from_mixed_input
    (hnm : n ≤ m) (X : Fin m → Ω → Fin n → ℝ) {H : ℝ}
    (hH : 0 < H) (hHbound : H ≤ 33/25)
    (hprocess : ∀ b : ℝ, 0 < b →
      Nonempty (LowerTransferInput μ X (n+2*H*Real.sqrt n) (5/2) b))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | smallestSingularValue (rowMatrix X ω) ≤
      LowerThreshold oneConstants m n 1 t} ≤ Real.exp (-t^2/2) := by
  let N := (n:ℝ)+2*H*Real.sqrt n
  have hN : 0 < N := by
    have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
    dsimp [N]
    positivity
  have hq : 0 < Real.sqrt (5/4:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hν : 2*Real.sqrt (5/4:ℝ)^2 = (5/2:ℝ) := by
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5/4)]
    norm_num
  have hD : Real.sqrt N < Real.sqrt n+H := by
    simpa only [N, one_pow, one_mul, mul_one, div_one] using
      (constant_dimension_cost_lt (n := n) (K := 1) (by norm_num) hH)
  have h := lower_transfer X ((NeZero.pos n).trans_le hnm)
    (Real.sqrt_pos.mpr hN) (Real.sq_sqrt hN.le) hD hq
    (fun b hb => by rw [hν]; exact hprocess b hb) ht
  have hbeta : Real.sqrt (5/4:ℝ) ≤ (28/25:ℝ) := by
    exact Real.sqrt_le_iff.mpr (by norm_num)
  have hqbound := mul_le_mul_of_nonneg_right hbeta ht
  apply le_trans (measureReal_mono ?_) h
  intro ω hω
  change smallestSingularValue (rowMatrix X ω) ≤ LowerThreshold oneConstants m n 1 t at hω
  change smallestSingularValue (rowMatrix X ω) ≤
    Real.sqrt m-(Real.sqrt n+H)-Real.sqrt (5/4:ℝ)*t
  simp only [LowerThreshold, oneConstants, logParameter, Real.log_one, add_zero,
    Real.sqrt_one, mul_one, one_mul] at hω
  linarith

end
end SingularValueBounds.KL
