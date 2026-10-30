import SingularValueBounds.KL.Certificates.ExactMomentEvaluation

/-! Exact moment sums evaluated with a shared integer denominator.

Each fold carries the current power or term, the partial sum, and their common
positive denominator. Its recurrence uses only integer multiplication and addition;
conversion to a rational happens after the fold. The bridges below prove equality
to the existing rational specifications, retaining every truncation and remainder.
-/
namespace SingularValueBounds.KL.Certificates.NumericalCertificateConditions

def expTaylorIntegerFold (a : ℤ) (b : ℕ) :
    ℕ → ℕ → ℤ → ℤ → ℕ → ℤ × ℤ × ℕ
  | 0, _, power, total, denominator => (power, total, denominator)
  | count+1, j, power, total, denominator =>
    let step := b*(j+1)
    let next := power*a
    expTaylorIntegerFold a b count (j+1) next (total*step+next) (denominator*step)

private theorem expTaylorFold_eq_integer (a : ℤ) (b : ℕ) (hb : 0 < b)
    (count j : ℕ) (power total : ℤ) (denominator : ℕ) (hd : 0 < denominator) :
    expTaylorFold ((a : ℚ)/b) count j ((power : ℚ)/denominator) ((total : ℚ)/denominator) =
      let p := expTaylorIntegerFold a b count j power total denominator
      ((p.1 : ℚ)/p.2.2, (p.2.1 : ℚ)/p.2.2) := by
  induction count generalizing j power total denominator with
  | zero => rfl
  | succ count ih =>
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hdq : (denominator : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hjq : ((j+1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hterm : (power : ℚ)/denominator * ((a : ℚ)/b) / (j+1 : ℕ) =
        ((power*a : ℤ) : ℚ)/(denominator*(b*(j+1)) : ℕ) := by
      push_cast
      field_simp [hbq, hdq, hjq]
      all_goals ring_nf <;> simp
    have htotal : (total : ℚ)/denominator + ((power*a : ℤ) : ℚ)/(denominator*(b*(j+1)) : ℕ) =
        ((total*(b*(j+1) : ℕ)+power*a : ℤ) : ℚ)/(denominator*(b*(j+1)) : ℕ) := by
      push_cast
      field_simp [hbq, hdq, hjq]
      all_goals ring
    simp only [expTaylorFold, expTaylorIntegerFold]
    rw [hterm, htotal]
    exact ih (j+1) (power*a) (total*(b*(j+1) : ℕ)+power*a) (denominator*(b*(j+1)))
      (Nat.mul_pos hd (Nat.mul_pos hb (by omega)))

def integerExpTaylor (N : ℕ) (x : ℚ) : ℚ :=
  let p := expTaylorIntegerFold x.num x.den N 0 1 1 1
  (p.2.1 : ℚ)/p.2.2

def integerExpTaylorUpper (N : ℕ) (x : ℚ) : ℚ :=
  let p := expTaylorIntegerFold x.num x.den N 0 1 1 1
  (p.2.1 : ℚ)/p.2.2 + (((p.1 : ℚ)/p.2.2)*x/(N+1 : ℕ))/(1-x/(N+2 : ℕ))

theorem expTaylorQ_eq_integer (N : ℕ) (x : ℚ) :
    expTaylorQ N x = integerExpTaylor N x := by
  have h := expTaylorFold_eq_integer x.num x.den x.den_pos N 0 1 1 1 (by decide)
  simp only [Int.cast_one, Nat.cast_one, div_one, Rat.num_div_den] at h
  rw [expTaylorQ_eq_fold, h]
  rfl

theorem expTaylorUpperQ_eq_integer (N : ℕ) (x : ℚ) :
    expTaylorUpperQ N x = integerExpTaylorUpper N x := by
  have h := expTaylorFold_eq_integer x.num x.den x.den_pos N 0 1 1 1 (by decide)
  simp only [Int.cast_one, Nat.cast_one, div_one, Rat.num_div_den] at h
  rw [expTaylorUpperQ_eq_fold, h]
  rfl



def logTaylorIntegerFold (a : ℤ) (b : ℕ) :
    ℕ → ℕ → ℤ → ℤ → ℕ → ℤ × ℤ × ℕ
  | 0, _, power, total, denominator => (power, total, denominator)
  | count+1, j, power, total, denominator =>
    let step := 2*j+1
    logTaylorIntegerFold a b count (j+1) (power*a^2*step)
      ((total*step+2*power)*b^2) (denominator*(b^2*step))

private theorem logTaylorFold_eq_integer (a : ℤ) (b : ℕ) (hb : 0 < b)
    (count j : ℕ) (power total : ℤ) (denominator : ℕ) (hd : 0 < denominator) :
    logTaylorFold ((a : ℚ)/b) count j ((power : ℚ)/denominator) ((total : ℚ)/denominator) =
      let p := logTaylorIntegerFold a b count j power total denominator
      ((p.1 : ℚ)/p.2.2, (p.2.1 : ℚ)/p.2.2) := by
  induction count generalizing j power total denominator with
  | zero => rfl
  | succ count ih =>
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hdq : (denominator : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hjq : (2*(j : ℚ)+1) ≠ 0 := by positivity
    have hpower : ((power : ℚ)/denominator) * ((a : ℚ)/b)^2 =
        ((power*a^2*(2*j+1 : ℕ) : ℤ) : ℚ)/(denominator*(b^2*(2*j+1)) : ℕ) := by
      push_cast
      field_simp [hbq, hdq, hjq]
      all_goals ring
    have htotal : (total : ℚ)/denominator + 2*((power : ℚ)/denominator)/(2*(j:ℚ)+1) =
        (((total*(2*j+1 : ℕ)+2*power)*b^2 : ℤ) : ℚ)/(denominator*(b^2*(2*j+1)) : ℕ) := by
      push_cast
      field_simp [hbq, hdq, hjq]
      all_goals ring
    simp only [logTaylorFold, logTaylorIntegerFold]
    rw [hpower, htotal]
    exact ih (j+1) (power*a^2*(2*j+1 : ℕ)) ((total*(2*j+1 : ℕ)+2*power)*b^2)
      (denominator*(b^2*(2*j+1))) (Nat.mul_pos hd (Nat.mul_pos (pow_pos hb _) (by omega)))

def integerLogTaylor (N : ℕ) (x : ℚ) : ℚ :=
  let p := logTaylorIntegerFold x.num x.den N 0 x.num 0 x.den
  (p.2.1 : ℚ)/p.2.2

def integerLogTaylorUpper (N : ℕ) (x : ℚ) : ℚ :=
  let p := logTaylorIntegerFold x.num x.den N 0 x.num 0 x.den
  (p.2.1 : ℚ)/p.2.2 + 2*((p.1 : ℚ)/p.2.2)/((2*(N:ℚ)+1)*(1-x^2))

theorem logTaylorQ_eq_integer (N : ℕ) (x : ℚ) :
    logTaylorQ N x = integerLogTaylor N x := by
  have h := logTaylorFold_eq_integer x.num x.den x.den_pos N 0 x.num 0 x.den x.den_pos
  simp only [Int.cast_zero, zero_div, Rat.num_div_den] at h
  rw [logTaylorQ_eq_fold, h]
  rfl

theorem logTaylorUpperQ_eq_integer (N : ℕ) (x : ℚ) :
    logTaylorUpperQ N x = integerLogTaylorUpper N x := by
  have h := logTaylorFold_eq_integer x.num x.den x.den_pos N 0 x.num 0 x.den x.den_pos
  simp only [Int.cast_zero, zero_div, Rat.num_div_den] at h
  rw [logTaylorUpperQ_eq_fold, h]
  rfl

end SingularValueBounds.KL.Certificates.NumericalCertificateConditions

namespace SingularValueBounds.KL.LowerCertificates

def lowerMPartialIntegerFold (a : ℤ) (b : ℕ) :
    ℕ → ℕ → ℤ → ℤ → ℕ → ℤ × ℤ × ℕ
  | 0, _, power, total, denominator => (power, total, denominator)
  | count+1, j, power, total, denominator =>
    let step := (j+2)*(j+3)
    lowerMPartialIntegerFold a b count (j+1) (power*a*step)
      ((total*step+2*power)*b) (denominator*(b*step))

private theorem lowerMPartialFold_eq_integer (a : ℤ) (b : ℕ) (hb : 0 < b)
    (count j : ℕ) (power total : ℤ) (denominator : ℕ) (hd : 0 < denominator) :
    lowerMPartialFold ((a : ℚ)/b) count j ((power : ℚ)/denominator) ((total : ℚ)/denominator) =
      let p := lowerMPartialIntegerFold a b count j power total denominator
      (p.2.1 : ℚ)/p.2.2 := by
  induction count generalizing j power total denominator with
  | zero => rfl
  | succ count ih =>
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hdq : (denominator : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hj2 : ((j : ℚ)+2) ≠ 0 := by positivity
    have hj3 : ((j : ℚ)+3) ≠ 0 := by positivity
    have hpower : ((power : ℚ)/denominator) * ((a : ℚ)/b) =
        ((power*a*((j+2)*(j+3) : ℕ) : ℤ) : ℚ)/(denominator*(b*((j+2)*(j+3))) : ℕ) := by
      push_cast
      field_simp [hbq, hdq, hj2, hj3]
      all_goals ring
    have htotal : (total : ℚ)/denominator + 2*((power : ℚ)/denominator)/((j+2)*(j+3)) =
        (((total*((j+2)*(j+3) : ℕ)+2*power)*b : ℤ) : ℚ)/(denominator*(b*((j+2)*(j+3))) : ℕ) := by
      push_cast
      field_simp [hbq, hdq, hj2, hj3]
      all_goals ring
    simp only [lowerMPartialFold, lowerMPartialIntegerFold]
    rw [hpower, htotal]
    exact ih (j+1) (power*a*((j+2)*(j+3) : ℕ)) ((total*((j+2)*(j+3) : ℕ)+2*power)*b)
      (denominator*(b*((j+2)*(j+3))))
      (Nat.mul_pos hd (Nat.mul_pos hb (Nat.mul_pos (by omega) (by omega))))

def integerLowerMPartial (N : ℕ) (x : ℚ) : ℚ :=
  let p := lowerMPartialIntegerFold x.num x.den N 0 (x.num^2) 0 (x.den^2)
  (p.2.1 : ℚ)/p.2.2

theorem lowerMPartialQ_eq_integer (N : ℕ) (x : ℚ) :
    lowerMPartialQ N x = integerLowerMPartial N x := by
  have h := lowerMPartialFold_eq_integer x.num x.den x.den_pos N 0 (x.num^2) 0 (x.den^2)
    (pow_pos x.den_pos _)
  simp only [Int.cast_zero, zero_div, Int.cast_pow, Nat.cast_pow, ← div_pow, Rat.num_div_den] at h
  rw [lowerMPartialQ_eq_fold, h]
  rfl

end SingularValueBounds.KL.LowerCertificates
