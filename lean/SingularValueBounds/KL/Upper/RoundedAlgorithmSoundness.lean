import SingularValueBounds.KL.Upper.RoundedAlgorithm

/-! The finite rational predicates connect the printed fixed-point algorithm to
the real exponential and logarithm. No analytic assertion is a certificate field. -/
namespace SingularValueBounds.KL.Certificates
noncomputable section

def RoundedExpConditions (x : ℚ) : Prop :=
  x ≤ roundUpQ x ∧
  if roundUpQ x < 0 then
    ExpLowerTranscript 80 (-roundUpQ x) (expLowerSumQ (-roundUpQ x))
      (expTermLowerQ (-roundUpQ x)) ∧
      0 < expLowerSumQ (-roundUpQ x) ∧
      1/expLowerSumQ (-roundUpQ x) ≤ roundUpQ (1/expLowerSumQ (-roundUpQ x))
  else ExpUpperTranscript 80 (roundUpQ x) (expPositiveUpperQ (roundUpQ x))
      (expTermUpperQ (roundUpQ x))

theorem RoundedExpConditions.sound {x : ℚ} (h : RoundedExpConditions x) :
    Real.exp (x : ℝ) ≤ (expUpperRoundedQ x : ℝ) := by
  have hxy : (x : ℝ) ≤ (roundUpQ x : ℝ) := by exact_mod_cast h.1
  apply (Real.exp_le_exp.mpr hxy).trans
  dsimp [expUpperRoundedQ]
  split_ifs with hy
  · have ht := (if_pos hy ▸ h.2)
    convert exp_neg_upper_of_lower_transcript ht.1 ht.2.1 ht.2.2 using 1 <;> simp
  · exact (if_neg hy ▸ h.2).sound

def UnitLogConditions (x : ℚ) : Prop :=
  0 < x ∧ LogTranscript 18 (logUnitZ x) (logUnitLowerQ x) (logUnitUpperQ x)
    (logUnitPowerLower x) (logUnitPowerUpper x)
    (logUnitCoeffLower x) (logUnitCoeffUpper x)

theorem UnitLogConditions.sound {x : ℚ} (h : UnitLogConditions x) :
    (logUnitLowerQ x : ℝ) ≤ Real.log (x : ℝ) ∧
    Real.log (x : ℝ) ≤ (logUnitUpperQ x : ℝ) := by
  have hx : (0 : ℝ) < x := by exact_mod_cast h.1
  have hi : (1+(logUnitZ x : ℝ))/(1-(logUnitZ x : ℝ)) = (x : ℝ) := by
    simp only [logUnitZ, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
    field_simp
    <;> ring
  simpa only [hi] using h.2.sound

def ScaledLogConditions (x : ℚ) : Prop :=
  let p := logReductionQ x
  x = (2 : ℚ)^p.1*p.2 ∧ UnitLogConditions p.2 ∧ UnitLogConditions 2

theorem ScaledLogConditions.sound {x : ℚ} (h : ScaledLogConditions x) :
    ((logPositiveRoundedQ x).1 : ℝ) ≤ Real.log (x : ℝ) ∧
    Real.log (x : ℝ) ≤ ((logPositiveRoundedQ x).2 : ℝ) := by
  rcases h with ⟨hscale, hu, htwo⟩
  have hs : (x : ℝ)=(2 : ℝ)^(logReductionQ x).1*((logReductionQ x).2 : ℝ) := by
    exact_mod_cast hscale
  have hup : (0 : ℝ)<(logReductionQ x).2 := by exact_mod_cast hu.1
  have hid : Real.log (x : ℝ) =
      ((logReductionQ x).1 : ℝ)*Real.log 2+Real.log ((logReductionQ x).2 : ℝ) := by
    rw [hs, Real.log_mul (by positivity) hup.ne', Real.log_pow]
  have hun := hu.sound
  have htn := htwo.sound
  norm_num only [Rat.cast_ofNat] at htn
  rw [hid]
  dsimp [logPositiveRoundedQ]
  push_cast
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left htn.1
      (show (0 : ℝ)≤(logReductionQ x).1 by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left htn.2
      (show (0 : ℝ)≤(logReductionQ x).1 by positivity)]

def RoundedLogConditions (x : ℚ) : Prop :=
  0 < x ∧ if x < 1 then ScaledLogConditions (1/x) else ScaledLogConditions x

theorem RoundedLogConditions.sound {x : ℚ} (h : RoundedLogConditions x) :
    ((logRoundedQ x).1 : ℝ) ≤ Real.log (x : ℝ) ∧
    Real.log (x : ℝ) ≤ ((logRoundedQ x).2 : ℝ) := by
  dsimp [logRoundedQ]
  split_ifs with hx
  · have hh := (if_pos hx ▸ h.2).sound
    have hid : Real.log ((1/x : ℚ) : ℝ) = -Real.log (x : ℝ) := by
      simp [Real.log_inv]
    simp only [Rat.cast_neg] 
    rw [hid] at hh
    constructor <;> linarith [hh.1, hh.2]
  · exact (if_neg hx ▸ h.2).sound

end
end SingularValueBounds.KL.Certificates
