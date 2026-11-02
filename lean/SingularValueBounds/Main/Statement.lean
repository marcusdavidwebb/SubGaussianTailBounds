import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Probability.Independence.Basic
import SingularValueBounds.Core.Assumptions
import SingularValueBounds.Core.Constants

/-!
# Internal matrix notation

Singular values are defined from the actual Gram matrix, including zeros.
The canonical adapters relate these internal extrema to NLA-lib's ordered
singular values in the immutable root statement.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace SingularValueBounds

noncomputable section

/-- The `n` singular values, including zeros, indexed by a spectral basis of
the Gram matrix `Sᵀ S`. Their order is irrelevant to the minimum and maximum. -/
def singularValues {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self S).eigenvalues j)

def smallestSingularValue {m n : ℕ} [NeZero n]
    (S : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (singularValues S)

def largestSingularValue {m n : ℕ} [NeZero n]
    (S : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (singularValues S)

theorem singularValues_nonneg {m n : ℕ}
    (S : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : 0 ≤ singularValues S j :=
  Real.sqrt_nonneg _

theorem smallestSingularValue_nonneg {m n : ℕ} [NeZero n]
    (S : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ smallestSingularValue S := by
  unfold smallestSingularValue
  apply Finset.le_inf'
  intro j _
  exact singularValues_nonneg S j

/-- The random matrix whose rows are the `X i`. -/
def rowMatrix {Ω : Type*} {m n : ℕ} (X : Fin m → Ω → Fin n → ℝ)
    (ω : Ω) : Matrix (Fin m) (Fin n) ℝ := fun i j => X i ω j

end
end SingularValueBounds
