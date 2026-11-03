import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log

/-! # Rational fixed-point algorithms for the entropy certificates
These rational functions define the rounded calculations used by the analytic
soundness lemmas. The finite obligations used in the results are proved in Lean. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates

def roundingScale : ℚ := 1000000000000000

def roundDownQ (x : ℚ) : ℚ := (⌊x*roundingScale⌋ : ℚ)/roundingScale
def roundUpQ (x : ℚ) : ℚ := -(⌊-(x*roundingScale)⌋ : ℚ)/roundingScale

def expTermLowerQ (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | j+1 => roundDownQ (expTermLowerQ x j*x/(j+1 : ℚ))

def expTermUpperQ (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | j+1 => roundUpQ (expTermUpperQ x j*x/(j+1 : ℚ))

def logPowerLowerQ (z z2 : ℚ) : ℕ → ℚ
  | 0 => z
  | j+1 => roundDownQ (logPowerLowerQ z z2 j*z2)

def logPowerUpperQ (z z2 : ℚ) : ℕ → ℚ
  | 0 => z
  | j+1 => roundUpQ (logPowerUpperQ z z2 j*z2)

def logUnitZ (x : ℚ) : ℚ := (x-1)/(x+1)
def logUnitZLower (x : ℚ) : ℚ := roundDownQ (logUnitZ x)
def logUnitZUpper (x : ℚ) : ℚ := roundUpQ (logUnitZ x)
def logUnitZ2Lower (x : ℚ) : ℚ := roundDownQ (logUnitZLower x ^ 2)
def logUnitZ2Upper (x : ℚ) : ℚ := roundUpQ (logUnitZUpper x ^ 2)

def logUnitPowerLower (x : ℚ) : ℕ → ℚ :=
  logPowerLowerQ (logUnitZLower x) (logUnitZ2Lower x)
def logUnitPowerUpper (x : ℚ) : ℕ → ℚ :=
  logPowerUpperQ (logUnitZUpper x) (logUnitZ2Upper x)

def logUnitCoeffLower (x : ℚ) (j : ℕ) : ℚ :=
  roundDownQ (2*logUnitPowerLower x j/(2*(j : ℚ)+1))
def logUnitCoeffUpper (x : ℚ) (j : ℕ) : ℚ :=
  roundUpQ (2*logUnitPowerUpper x j/(2*(j : ℚ)+1))

def logUnitLowerQ (x : ℚ) : ℚ := ∑ j ∈ Finset.range 18, logUnitCoeffLower x j
def logUnitUpperQ (x : ℚ) : ℚ :=
  (∑ j ∈ Finset.range 18, logUnitCoeffUpper x j)+
    roundUpQ (2*logUnitPowerUpper x 18/(37*(1-logUnitZ2Upper x)))

def reduceLogPowTwo : ℕ → ℚ → ℕ × ℚ
  | 0, x => (0,x)
  | fuel+1, x =>
      if 2 ≤ x then
        let pair := reduceLogPowTwo fuel (x/2)
        (pair.1+1,pair.2)
      else (0,x)

def logReductionQ (x : ℚ) : ℕ × ℚ :=
  reduceLogPowTwo (Nat.log 2 x.num.natAbs+1) x

def logPositiveRoundedQ (x : ℚ) : ℚ × ℚ :=
  let pair := logReductionQ x
  (logUnitLowerQ pair.2+(pair.1 : ℚ)*logUnitLowerQ 2,
    logUnitUpperQ pair.2+(pair.1 : ℚ)*logUnitUpperQ 2)

def logRoundedQ (x : ℚ) : ℚ × ℚ :=
  if x < 1 then
    let pair := logPositiveRoundedQ (1/x)
    (-pair.2,-pair.1)
  else logPositiveRoundedQ x

end SingularValueBounds.KL.Certificates

