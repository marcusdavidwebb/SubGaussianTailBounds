import Mathlib

/-! # Optimizing the potential parameter for the current spectral proof

The exact choices φ₋ = D/[A(s₋−D)] and φ₊ = D/[A(s₊+D)] convert
the initial spectral cost and one-row drift into `(s₋−D)²` and `(s₊+D)²`.
These are the choices in §2.2; no recursively accumulated barriers enter.
-/

namespace SingularValueBounds
noncomputable section

/-- Exact normalization for an upper barrier at the optimal potential. -/
theorem spectral_upper_optimal_normalization {A D s : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hs : 0 < s) :
    1 - A * (D / (A * (s + D))) = s / (s + D) := by
  have hsum : 0 < s + D := add_pos hs hD
  field_simp
  ring

/-- The optimized upper estimate is the square of `s + D`. -/
theorem spectral_upper_optimal_cost {A N D s : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hs : 0 < s) (hD2 : D ^ 2 = A * N) :
    N / (D / (A * (s + D))) + s ^ 2 / (1 - A * (D / (A * (s + D)))) =
      (s + D) ^ 2 := by
  rw [spectral_upper_optimal_normalization hA hD hs]
  have hsum : 0 < s + D := add_pos hs hD
  field_simp
  nlinarith [hD2]

/-- Exact normalization for a lower barrier; the admissible case is `s > D`. -/
theorem spectral_lower_optimal_normalization {A D s : ℝ}
    (hA : 0 < A) (_hD : 0 < D) (hs : D < s) :
    1 + A * (D / (A * (s - D))) = s / (s - D) := by
  have hdiff : 0 < s - D := sub_pos.mpr hs
  field_simp
  ring

/-- The optimized lower estimate is the square of `s - D`. -/
theorem spectral_lower_optimal_cost {A N D s : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hs : D < s) (hD2 : D ^ 2 = A * N) :
    s ^ 2 / (1 + A * (D / (A * (s - D)))) - N / (D / (A * (s - D))) =
      (s - D) ^ 2 := by
  rw [spectral_lower_optimal_normalization hA hD hs]
  have hdiff : 0 < s - D := sub_pos.mpr hs
  have hs0 : 0 < s := hD.trans hs
  field_simp
  nlinarith [hD2]

end
end SingularValueBounds
