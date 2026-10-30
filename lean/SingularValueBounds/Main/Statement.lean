import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Probability.Independence.Basic
import SingularValueBounds.Core.Assumptions
import SingularValueBounds.Core.Constants

/-!
# Theorem 1.1: statement and notation

This file fixes the exact statement to be proved, including the endpoint
constants, the non-strict tail events, and zero singular values. Singular
values are defined from the actual Gram matrix, not abstract substitutes.

`Theorem11` below is the quantified proposition. Its proof is
`SingularValueBounds.theorem11` in `Main/Theorem11.lean`; keeping the statement in
this file avoids circular dependencies between notation and the proof.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace SingularValueBounds

noncomputable section

/-- The common dimension coefficient α = γ in Theorem 1.1. -/
def dimensionCoefficient (K : ℝ) : ℝ :=
  if K = 1 then 3 else 5 * K * (logParameter K) ^ (2 / 3 : ℝ)

/-- The common coefficient β = δ of the confidence parameter. -/
def confidenceCoefficient (K : ℝ) : ℝ := 2 * K * Real.sqrt (logParameter K)

@[simp] theorem dimensionCoefficient_one : dimensionCoefficient 1 = 3 := by
  simp [dimensionCoefficient]

@[simp] theorem confidenceCoefficient_one : confidenceCoefficient 1 = 2 := by
  simp [confidenceCoefficient, logParameter]

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

/-- The two conclusions of Theorem 1.1 at a fixed confidence parameter. -/
def SingularValueTails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m n : ℕ} [NeZero n]
    (X : Fin m → Ω → Fin n → ℝ) (K t : ℝ) : Prop :=
  μ.real {ω | smallestSingularValue (rowMatrix X ω) ≤
      Real.sqrt m - K * Real.sqrt n -
        dimensionCoefficient K * (n : ℝ) ^ (1 / 6 : ℝ) -
        confidenceCoefficient K * t} ≤ Real.exp (-t ^ 2 / 2) ∧
  μ.real {ω | Real.sqrt m + K * Real.sqrt n +
      dimensionCoefficient K * (n : ℝ) ^ (1 / 6 : ℝ) +
        confidenceCoefficient K * t ≤ largestSingularValue (rowMatrix X ω)} ≤
    Real.exp (-t ^ 2 / 2)

/-- Exact quantified target for Theorem 1.1, with no barrier or quadratic-form
estimates added to the hypotheses. The measure is assumed to be a probability
measure when proving this proposition. -/
def Theorem11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  ∀ (m n : ℕ) [NeZero n], n ≤ m →
    ∀ (X : Fin m → Ω → Fin n → ℝ) (K : ℝ), 1 ≤ K →
      iIndepFun X μ →
      (∀ i, CentredIsotropic μ (X i)) →
      (∀ i, SubGaussianMGF μ (X i) K) →
      ∀ t : ℝ, 0 ≤ t → SingularValueTails μ X K t

end
end SingularValueBounds
