import SingularValueBounds.KL.Upper.RoundedAlgorithm
import Mathlib.Data.Rat.Floor

/-! Integer representations of the existing fixed-point rational rounding operations. -/
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0

def fixedScaleNat : ℕ := 1000000000000000
def fixedQ (n : ℤ) : ℚ := (n : ℚ)/roundingScale

theorem fixedQ_add (n m : ℤ) : fixedQ (n+m) = fixedQ n+fixedQ m := by
  simp [fixedQ, add_div]

theorem fixedQ_mul_int (n m : ℤ) : fixedQ (n*m) = (n:ℚ)*fixedQ m := by
  simp [fixedQ]
  ring

theorem roundDownQ_fixed_mul_div (n m : ℤ) (j : ℕ) :
    roundDownQ (fixedQ n*fixedQ m/(j:ℚ)) =
      fixedQ (n*m/((fixedScaleNat*j : ℕ):ℤ)) := by
  unfold roundDownQ fixedQ
  congr 1
  have he : (((n:ℚ)/roundingScale)*((m:ℚ)/roundingScale)/(j:ℚ))*roundingScale =
      ((n*m:ℤ):ℚ)/((fixedScaleNat*j:ℕ):ℚ) := by
    simp only [roundingScale, fixedScaleNat, Nat.cast_mul, Int.cast_mul]
    ring
  rw [he, Rat.floor_intCast_div_natCast]

theorem roundUpQ_fixed_mul_div (n m : ℤ) (j : ℕ) :
    roundUpQ (fixedQ n*fixedQ m/(j:ℚ)) =
      fixedQ (-((- (n*m))/((fixedScaleNat*j : ℕ):ℤ))) := by
  unfold roundUpQ fixedQ
  have he : -((((n:ℚ)/roundingScale)*((m:ℚ)/roundingScale)/(j:ℚ))*roundingScale) =
      ((-(n*m):ℤ):ℚ)/((fixedScaleNat*j:ℕ):ℚ) := by
    simp only [roundingScale, fixedScaleNat, Nat.cast_mul, Int.cast_mul, Int.cast_neg]
    ring
  rw [he, Rat.floor_intCast_div_natCast]
  simp only [Int.cast_neg]

theorem roundDownQ_fixed_div (n : ℤ) (j : ℕ) :
    roundDownQ (fixedQ n/(j:ℚ)) = fixedQ (n/(j:ℤ)) := by
  unfold roundDownQ fixedQ
  congr 1
  have he : ((n:ℚ)/roundingScale/(j:ℚ))*roundingScale = (n:ℚ)/(j:ℚ) := by
    simp only [roundingScale]
    ring
  rw [he, Rat.floor_intCast_div_natCast]

theorem roundUpQ_fixed_div (n : ℤ) (j : ℕ) :
    roundUpQ (fixedQ n/(j:ℚ)) = fixedQ (-((-n)/(j:ℤ))) := by
  unfold roundUpQ fixedQ
  have he : -(((n:ℚ)/roundingScale/(j:ℚ))*roundingScale) = ((-n:ℤ):ℚ)/(j:ℚ) := by
    simp only [roundingScale, Int.cast_neg]
    ring
  rw [he, Rat.floor_intCast_div_natCast]
  simp only [Int.cast_neg]

/-- Natural ceiling division agrees with signed integer ceiling division. -/
theorem natCeil_cast_eq_neg_ediv (n d : ℕ) (hd : 0 < d) :
    (match n with | 0 => (0 : ℤ) | k+1 => ((k/d+1 : ℕ) : ℤ)) =
      -(-(n : ℤ)/(d : ℤ)) := by
  cases n with
  | zero => simp
  | succ n =>
    have he : -((n+1 : ℕ) : ℤ) = Int.negSucc n := by rfl
    rw [he, Int.negSucc_ediv n (by exact_mod_cast hd)]
    simp
    rfl

end SingularValueBounds.KL.Certificates
