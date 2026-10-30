import SingularValueBounds.KL.Lower.CellData

/-! Single-pass evaluation of the exact finite sums in the moment certificates.

The identities below preserve the original rational sums, including their
truncation orders and remainders. They merely carry each term into the next
step instead of recomputing powers and factorials for every summand.
-/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates.NumericalCertificateConditions

def expTaylorFold (x : ℚ) : ℕ → ℕ → ℚ → ℚ → ℚ × ℚ
  | 0, _, term, total => (term, total)
  | count+1, j, term, total =>
    let next := term*x/(j+1 : ℕ)
    expTaylorFold x count (j+1) next (total+next)

private theorem expTaylorTerm_step (x : ℚ) (j : ℕ) :
    (x^j/(j.factorial : ℚ))*x/(j+1 : ℕ) = x^(j+1)/((j+1).factorial : ℚ) := by
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
  ring

private theorem expTaylorFold_correct (x : ℚ) (count j : ℕ) :
    expTaylorFold x count j (x^j/(j.factorial : ℚ))
      (∑ i ∈ Finset.range (j+1), x^i/(i.factorial : ℚ)) =
      (x^(j+count)/((j+count).factorial : ℚ),
        ∑ i ∈ Finset.range (j+count+1), x^i/(i.factorial : ℚ)) := by
  induction count generalizing j with
  | zero => simp [expTaylorFold]
  | succ count ih =>
    simp only [expTaylorFold, expTaylorTerm_step]
    rw [← Finset.sum_range_succ, ih]
    rw [show j+1+count = j+(count+1) by omega]

theorem expTaylorQ_eq_fold (N : ℕ) (x : ℚ) :
    expTaylorQ N x = (expTaylorFold x N 0 1 1).2 := by
  have h := congrArg Prod.snd (expTaylorFold_correct x N 0)
  simpa [expTaylorQ] using h.symm

theorem expTaylorUpperQ_eq_fold (N : ℕ) (x : ℚ) :
    expTaylorUpperQ N x =
      let p := expTaylorFold x N 0 1 1
      p.2 + (p.1*x/(N+1 : ℕ))/(1-x/(N+2 : ℕ)) := by
  have h := expTaylorFold_correct x N 0
  simp only [Nat.zero_add, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Finset.sum_range_one] at h
  rw [h]
  dsimp only
  rw [expTaylorTerm_step]
  simp [expTaylorUpperQ, expTaylorQ]

def logTaylorFold (z : ℚ) : ℕ → ℕ → ℚ → ℚ → ℚ × ℚ
  | 0, _, power, total => (power, total)
  | count+1, j, power, total =>
    logTaylorFold z count (j+1) (power*z^2) (total+2*power/(2*(j:ℚ)+1))

private theorem logTaylorFold_correct (z : ℚ) (count j : ℕ) :
    logTaylorFold z count j (z^(2*j+1))
      (∑ i ∈ Finset.range j, 2*z^(2*i+1)/(2*(i:ℚ)+1)) =
      (z^(2*(j+count)+1),
        ∑ i ∈ Finset.range (j+count), 2*z^(2*i+1)/(2*(i:ℚ)+1)) := by
  induction count generalizing j with
  | zero => simp [logTaylorFold]
  | succ count ih =>
    simp only [logTaylorFold]
    rw [← pow_add, show 2*j+1+2 = 2*(j+1)+1 by omega]
    rw [← Finset.sum_range_succ, ih]
    rw [show j+1+count = j+(count+1) by omega]

theorem logTaylorQ_eq_fold (N : ℕ) (z : ℚ) :
    logTaylorQ N z = (logTaylorFold z N 0 z 0).2 := by
  have h := congrArg Prod.snd (logTaylorFold_correct z N 0)
  simp only [Nat.zero_add, Nat.mul_zero, zero_add, pow_one,
    Finset.sum_range_zero, Prod.snd] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem logTaylorUpperQ_eq_fold (N : ℕ) (z : ℚ) :
    logTaylorUpperQ N z =
      let p := logTaylorFold z N 0 z 0
      p.2 + 2*p.1/((2*(N:ℚ)+1)*(1-z^2)) := by
  have h := logTaylorFold_correct z N 0
  simp only [Nat.zero_add, Nat.mul_zero, zero_add, pow_one,
    Finset.sum_range_zero] at h
  rw [h]
  unfold logTaylorUpperQ logTaylorQ
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SingularValueBounds.KL.Certificates.NumericalCertificateConditions

namespace SingularValueBounds.KL.LowerCertificates

def lowerMPartialFold (q : ℚ) : ℕ → ℕ → ℚ → ℚ → ℚ
  | 0, _, _, total => total
  | count+1, j, power, total =>
    lowerMPartialFold q count (j+1) (power*q)
      (total+2*power/((j+2:ℚ)*(j+3:ℚ)))

private theorem lowerMPartialFold_correct (q : ℚ) (count j : ℕ) :
    lowerMPartialFold q count j (q^(j+2))
      (∑ i ∈ Finset.range j, 2*q^(i+2)/((i+2:ℚ)*(i+3:ℚ))) =
      ∑ i ∈ Finset.range (j+count), 2*q^(i+2)/((i+2:ℚ)*(i+3:ℚ)) := by
  induction count generalizing j with
  | zero => simp [lowerMPartialFold]
  | succ count ih =>
    simp only [lowerMPartialFold]
    rw [← pow_succ, show j+2+1 = j+1+2 by omega]
    rw [← Finset.sum_range_succ, ih]
    rw [show j+1+count = j+(count+1) by omega]

theorem lowerMPartialQ_eq_fold (N : ℕ) (q : ℚ) :
    lowerMPartialQ N q = lowerMPartialFold q N 0 (q^2) 0 := by
  simpa [lowerMPartialQ] using (lowerMPartialFold_correct q N 0).symm

end SingularValueBounds.KL.LowerCertificates
