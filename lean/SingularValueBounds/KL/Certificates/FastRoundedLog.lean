import SingularValueBounds.KL.Upper.RoundedAlgorithm

/-! Tail-recursive evaluation of the existing rounded logarithm sums.
The equations are proved in Lean; they only change how exact rational arithmetic is reduced. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0

def logLowerAcc (z2 : ℚ) : ℕ → ℕ → ℚ → ℚ → ℚ
  | 0, _, _, total => total
  | count+1, j, power, total =>
      logLowerAcc z2 count (j+1) (roundDownQ (power*z2))
        (total+roundDownQ (2*power/(2*(j:ℚ)+1)))

def logUpperAcc (z2 : ℚ) : ℕ → ℕ → ℚ → ℚ → ℚ
  | 0, _, _, total => total
  | count+1, j, power, total =>
      logUpperAcc z2 count (j+1) (roundUpQ (power*z2))
        (total+roundUpQ (2*power/(2*(j:ℚ)+1)))

theorem logLowerAcc_correct (z z2 : ℚ) (count j : ℕ) :
    logLowerAcc z2 count j (logPowerLowerQ z z2 j)
      (∑ i ∈ Finset.range j, roundDownQ (2*logPowerLowerQ z z2 i/(2*(i:ℚ)+1))) =
    ∑ i ∈ Finset.range (j+count), roundDownQ (2*logPowerLowerQ z z2 i/(2*(i:ℚ)+1)) := by
  induction count generalizing j with
  | zero => simp [logLowerAcc]
  | succ count ih =>
    simp only [logLowerAcc]
    rw [← logPowerLowerQ]
    rw [← Finset.sum_range_succ]
    rw [ih]
    rw [show j+1+count = j+(count+1) by omega]

theorem logUpperAcc_correct (z z2 : ℚ) (count j : ℕ) :
    logUpperAcc z2 count j (logPowerUpperQ z z2 j)
      (∑ i ∈ Finset.range j, roundUpQ (2*logPowerUpperQ z z2 i/(2*(i:ℚ)+1))) =
    ∑ i ∈ Finset.range (j+count), roundUpQ (2*logPowerUpperQ z z2 i/(2*(i:ℚ)+1)) := by
  induction count generalizing j with
  | zero => simp [logUpperAcc]
  | succ count ih =>
    simp only [logUpperAcc]
    rw [← logPowerUpperQ]
    rw [← Finset.sum_range_succ]
    rw [ih]
    rw [show j+1+count = j+(count+1) by omega]

theorem logUnitLowerQ_eq_fast (x : ℚ) :
    logUnitLowerQ x = logLowerAcc (logUnitZ2Lower x) 18 0 (logUnitZLower x) 0 := by
  symm
  simpa [logUnitLowerQ, logUnitCoeffLower, logUnitPowerLower, logPowerLowerQ] using
    logLowerAcc_correct (logUnitZLower x) (logUnitZ2Lower x) 18 0

theorem logUnitUpperQ_eq_fast (x : ℚ) :
    logUnitUpperQ x =
      logUpperAcc (logUnitZ2Upper x) 18 0 (logUnitZUpper x) 0+
        roundUpQ (2*logUnitPowerUpper x 18/(37*(1-logUnitZ2Upper x))) := by
  unfold logUnitUpperQ
  congr 1
  symm
  simpa [logUnitCoeffUpper, logUnitPowerUpper, logPowerUpperQ] using
    logUpperAcc_correct (logUnitZUpper x) (logUnitZ2Upper x) 18 0

end SingularValueBounds.KL.Certificates
