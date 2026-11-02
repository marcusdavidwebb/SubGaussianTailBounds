import SingularValueBounds.KL.Certificates.ConcreteLog

/-! Uniform coarse bounds for the actual rounded small-range prefactors. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates

private lemma logUnitZ2Upper_le_half {x : ℚ} (hx : 1 ≤ x) (h2 : x ≤ 2) :
    logUnitZ2Upper x ≤ 1/2 := by
  have hu := roundUpQ_lt_add (logUnitZ x)
  have hz := logUnitZ_le_third hx h2
  have h0 : 0 ≤ logUnitZUpper x := (logUnitZ_nonneg hx).trans (le_roundUpQ _)
  have hhalf : logUnitZUpper x ≤ 1/2 := by
    dsimp [logUnitZUpper, roundingScale] at *
    linarith
  have hsq : logUnitZUpper x ^ 2 ≤ 1/4 := by nlinarith
  have hr := roundUpQ_lt_add (logUnitZUpper x ^ 2)
  change roundUpQ (logUnitZUpper x ^ 2) ≤ 1/2
  dsimp [roundingScale] at hr
  linarith

private lemma logUnitPowerUpper_le_linear {x : ℚ} (hx : 1 ≤ x) (h2 : x ≤ 2)
    (j : ℕ) : logUnitPowerUpper x j ≤ logUnitZUpper x + j / roundingScale := by
  have hr : logUnitZ2Upper x ≤ 1 := (logUnitZ2Upper_le_half hx h2).trans (by norm_num)
  induction j with
  | zero =>
    change logUnitZUpper x ≤ logUnitZUpper x + (0 : ℚ) / roundingScale
    simp only [zero_div, add_zero, le_refl]
  | succ j ih =>
    have hp := logUnitPowerUpper_nonneg hx j
    have hm := mul_le_mul_of_nonneg_left hr hp
    have he := roundUpQ_lt_add (logUnitPowerUpper x j * logUnitZ2Upper x)
    change roundUpQ (logUnitPowerUpper x j * logUnitZ2Upper x) ≤ _
    push_cast
    simp only [add_div] at *
    simp only [mul_one] at hm
    linarith

/-- A deliberately loose bound for all inputs in the reduced logarithm interval.
It includes every rounding operation of the implemented upper enclosure. -/
theorem logUnitUpperQ_le_coarse {x : ℚ} (hx : 1 ≤ x) (h2 : x ≤ 2) :
    logUnitUpperQ x ≤ 40 * logUnitZ x + 1/1000000000 := by
  let P := logUnitZUpper x + 18 / roundingScale
  have hP : 0 ≤ P := by
    dsimp [P]
    exact add_nonneg ((logUnitZ_nonneg hx).trans (le_roundUpQ _)) (div_nonneg (by norm_num) roundingScale_pos.le)
  have hp (j : ℕ) (hj : j ≤ 18) : logUnitPowerUpper x j ≤ P := by
    apply (logUnitPowerUpper_le_linear hx h2 j).trans
    dsimp [P]
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (by exact_mod_cast hj) roundingScale_pos.le
  have hc (j : ℕ) (hj : j < 18) :
      logUnitCoeffUpper x j ≤ 2 * P + 1 / roundingScale := by
    have hden : (1 : ℚ) ≤ 2*j+1 := by have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j; linarith
    have hdiv : 2 * logUnitPowerUpper x j / (2*j+1) ≤ 2 * P := by
      rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2*j+1)]
      have hh := hp j (by omega)
      nlinarith
    exact (roundUpQ_lt_add _).le.trans (add_le_add_left hdiv _)
  have hs : (∑ j ∈ Finset.range 18, logUnitCoeffUpper x j) ≤
      18 * (2 * P + 1 / roundingScale) := by
    calc
      _ ≤ ∑ j ∈ Finset.range 18, (2 * P + 1 / roundingScale) :=
        Finset.sum_le_sum (fun j hj => hc j (Finset.mem_range.mp hj))
      _ = _ := by simp; ring
  have hden : (1 : ℚ) ≤ 37 * (1 - logUnitZ2Upper x) := by
    have hh := logUnitZ2Upper_le_half hx h2
    linarith
  have ht : 2 * logUnitPowerUpper x 18 / (37 * (1 - logUnitZ2Upper x)) ≤ 2 * P := by
    rw [div_le_iff₀ (by linarith : (0 : ℚ) < 37 * (1 - logUnitZ2Upper x))]
    have hh := hp 18 le_rfl
    nlinarith
  have htail := (roundUpQ_lt_add _).le.trans (add_le_add_left ht (1 / roundingScale))
  have hz0 := logUnitZ_nonneg hx
  have hz := roundUpQ_lt_add (logUnitZ x)
  unfold logUnitUpperQ
  dsimp [P, logUnitZUpper, roundingScale] at hs htail hz ⊢
  linarith

private lemma logRoundedQ_one_sub_lower {t : ℚ} (ht : 0 < t) (ht1 : t ≤ 1/8) :
    -(logRoundedQ (1-t)).1 = logUnitUpperQ (1/(1-t)) := by
  have hlt : 1-t < 1 := by linarith
  have htwo : ¬ 2 ≤ (1 : ℚ)/(1-t) := by
    apply not_le.mpr
    rw [div_lt_iff₀ (by linarith : (0 : ℚ) < 1-t)]
    linarith
  simp only [one_div] at htwo
  simp [logRoundedQ, hlt, logPositiveRoundedQ, logReductionQ, reduceLogPowTwo, htwo]

/-- The implemented rounded logarithm is small uniformly on the small-prefactor range. -/
theorem logRoundedQ_one_sub_lower_coarse {t : ℚ} (ht : 0 < t) (ht1 : t ≤ 1/8) :
    -(logRoundedQ (1-t)).1 ≤ 40*t + 1/1000000000 := by
  have hd : (0 : ℚ) < 1-t := by linarith
  have hx : (1 : ℚ) ≤ 1/(1-t) := (le_div_iff₀ hd).2 (by linarith)
  have h2 : (1 : ℚ)/(1-t) ≤ 2 := (div_le_iff₀ hd).2 (by linarith)
  have hz : logUnitZ (1/(1-t)) ≤ t := by
    have he : logUnitZ (1/(1-t)) = t/(2-t) := by
      unfold logUnitZ
      field_simp [ne_of_gt hd, show (2 : ℚ)-t ≠ 0 by linarith]
      ring
    rw [he, div_le_iff₀ (by linarith : (0 : ℚ) < 2-t)]
    nlinarith
  rw [logRoundedQ_one_sub_lower ht ht1]
  exact (logUnitUpperQ_le_coarse hx h2).trans (by linarith)

/-- A uniform domain bound replaces all small-prefactor grid evaluations. -/
theorem endpointSmallPrefactor_expDomain_uniform {k q : ℚ}
    (hk : 1/200 ≤ k) (hk1 : k ≤ 1/4) (hq : 0 < q) (hq2 : q ≤ 2) :
    roundUpQ (roundUpQ (-(logRoundedQ (1-q*k^2)).1/(2*k^2))) < 82 := by
  have hk0 : 0 < k := by linarith
  have hk2 : k^2 ≤ 1/16 := by nlinarith
  have hkl : 1/40000 ≤ k^2 := by nlinarith
  have ht : 0 < q*k^2 := mul_pos hq (pow_pos hk0 _)
  have ht1 : q*k^2 ≤ 1/8 := by
    have hh := mul_le_mul hq2 hk2 (sq_nonneg k) (by norm_num : (0 : ℚ) ≤ 2)
    norm_num at hh ⊢
    exact hh
  have hlog := logRoundedQ_one_sub_lower_coarse ht ht1
  have hb : -(logRoundedQ (1-q*k^2)).1/(2*k^2) ≤ 41 := by
    rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2*k^2)]
    have hh := mul_le_mul_of_nonneg_right hq2 (sq_nonneg k)
    nlinarith
  have hround := roundUpQ_lt_add (-(logRoundedQ (1-q*k^2)).1/(2*k^2))
  have hround2 := roundUpQ_lt_add (roundUpQ (-(logRoundedQ (1-q*k^2)).1/(2*k^2)))
  norm_num [roundingScale] at hround hround2
  linarith

end SingularValueBounds.KL.Certificates
