import SingularValueBounds.KL.Certificates.IntegerFixedPoint

/-! Exact integer evaluation of every recursively rounded logarithm term. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def logZLowerInt (x : ℚ) : ℤ := ⌊logUnitZ x*roundingScale⌋
def logZUpperInt (x : ℚ) : ℤ := -⌊-(logUnitZ x*roundingScale)⌋
def logZ2LowerInt (x : ℚ) : ℤ := logZLowerInt x*logZLowerInt x/(fixedScaleNat:ℤ)
def logZ2UpperInt (x : ℚ) : ℤ := -(-(logZUpperInt x*logZUpperInt x)/(fixedScaleNat:ℤ))

def logPowerLowerInt (z z2 : ℤ) : ℕ → ℤ
  | 0 => z
  | j+1 => logPowerLowerInt z z2 j*z2/(fixedScaleNat:ℤ)
def logPowerUpperInt (z z2 : ℤ) : ℕ → ℤ
  | 0 => z
  | j+1 => -(-(logPowerUpperInt z z2 j*z2)/(fixedScaleNat:ℤ))

def logCoeffLowerInt (x : ℚ) (j : ℕ) : ℤ :=
  (2*logPowerLowerInt (logZLowerInt x) (logZ2LowerInt x) j)/((2*j+1:ℕ):ℤ)
def logCoeffUpperInt (x : ℚ) (j : ℕ) : ℤ :=
  -(-(2*logPowerUpperInt (logZUpperInt x) (logZ2UpperInt x) j)/((2*j+1:ℕ):ℤ))

theorem logUnitZLower_eq_int (x : ℚ) : logUnitZLower x = fixedQ (logZLowerInt x) := rfl

theorem logUnitZUpper_eq_int (x : ℚ) : logUnitZUpper x = fixedQ (logZUpperInt x) := by
  simp only [logUnitZUpper, roundUpQ, fixedQ, logZUpperInt, Int.cast_neg]

theorem logUnitZ2Lower_eq_int (x : ℚ) : logUnitZ2Lower x = fixedQ (logZ2LowerInt x) := by
  unfold logUnitZ2Lower
  rw [logUnitZLower_eq_int, pow_two]
  simpa [logZ2LowerInt] using roundDownQ_fixed_mul_div (logZLowerInt x) (logZLowerInt x) 1

theorem logUnitZ2Upper_eq_int (x : ℚ) : logUnitZ2Upper x = fixedQ (logZ2UpperInt x) := by
  unfold logUnitZ2Upper
  rw [logUnitZUpper_eq_int, pow_two]
  simpa [logZ2UpperInt] using roundUpQ_fixed_mul_div (logZUpperInt x) (logZUpperInt x) 1

theorem logPowerLowerQ_fixed (z z2 : ℤ) (j : ℕ) :
    logPowerLowerQ (fixedQ z) (fixedQ z2) j = fixedQ (logPowerLowerInt z z2 j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [logPowerLowerQ, ih]
    simpa [logPowerLowerInt] using roundDownQ_fixed_mul_div (logPowerLowerInt z z2 j) z2 1

theorem logPowerUpperQ_fixed (z z2 : ℤ) (j : ℕ) :
    logPowerUpperQ (fixedQ z) (fixedQ z2) j = fixedQ (logPowerUpperInt z z2 j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [logPowerUpperQ, ih]
    simpa [logPowerUpperInt] using roundUpQ_fixed_mul_div (logPowerUpperInt z z2 j) z2 1

theorem logUnitPowerLower_eq_int (x : ℚ) (j : ℕ) :
    logUnitPowerLower x j = fixedQ (logPowerLowerInt (logZLowerInt x) (logZ2LowerInt x) j) := by
  unfold logUnitPowerLower
  rw [logUnitZLower_eq_int, logUnitZ2Lower_eq_int, logPowerLowerQ_fixed]

theorem logUnitPowerUpper_eq_int (x : ℚ) (j : ℕ) :
    logUnitPowerUpper x j = fixedQ (logPowerUpperInt (logZUpperInt x) (logZ2UpperInt x) j) := by
  unfold logUnitPowerUpper
  rw [logUnitZUpper_eq_int, logUnitZ2Upper_eq_int, logPowerUpperQ_fixed]

theorem logUnitCoeffLower_eq_int (x : ℚ) (j : ℕ) :
    logUnitCoeffLower x j = fixedQ (logCoeffLowerInt x j) := by
  unfold logUnitCoeffLower
  rw [logUnitPowerLower_eq_int]
  have he (n : ℤ) : 2*fixedQ n/(2*(j:ℚ)+1) = fixedQ (2*n)/((2*j+1:ℕ):ℚ) := by
    simp [fixedQ]
    ring
  rw [he, roundDownQ_fixed_div]
  rfl

theorem logUnitCoeffUpper_eq_int (x : ℚ) (j : ℕ) :
    logUnitCoeffUpper x j = fixedQ (logCoeffUpperInt x j) := by
  unfold logUnitCoeffUpper
  rw [logUnitPowerUpper_eq_int]
  have he (n : ℤ) : 2*fixedQ n/(2*(j:ℚ)+1) = fixedQ (2*n)/((2*j+1:ℕ):ℚ) := by
    simp [fixedQ]
    ring
  rw [he, roundUpQ_fixed_div]
  rfl

theorem logUnitLowerQ_eq_int (x : ℚ) :
    logUnitLowerQ x = fixedQ (∑ j ∈ Finset.range 18, logCoeffLowerInt x j) := by
  unfold logUnitLowerQ
  simp_rw [logUnitCoeffLower_eq_int]
  simp [fixedQ, Finset.sum_div]

theorem logUnitUpperQ_eq_int (x : ℚ) :
    logUnitUpperQ x = fixedQ (∑ j ∈ Finset.range 18, logCoeffUpperInt x j)+
      roundUpQ (2*fixedQ (logPowerUpperInt (logZUpperInt x) (logZ2UpperInt x) 18)/
        (37*(1-fixedQ (logZ2UpperInt x)))) := by
  unfold logUnitUpperQ
  simp_rw [logUnitCoeffUpper_eq_int]
  rw [logUnitPowerUpper_eq_int, logUnitZ2Upper_eq_int]
  simp [fixedQ, Finset.sum_div]

end SingularValueBounds.KL.Certificates
