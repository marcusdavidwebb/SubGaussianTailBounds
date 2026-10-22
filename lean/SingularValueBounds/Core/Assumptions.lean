import Mathlib

/-! # The original row hypotheses of Theorem 1.1 -/

open MeasureTheory
open scoped Matrix

namespace SingularValueBounds

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- A measurable centred isotropic real random vector, stated directionally.
The integrability fields give the usual (finite) meaning to the expectations.
The last identity is `E[(uᵀX)²] = uᵀu`, equivalent in finite dimensions to
`E[XXᵀ] = I`. -/
structure CentredIsotropic (μ : Measure Ω) (X : Ω → ι → ℝ) : Prop where
  measurable : Measurable X
  integrable : ∀ u : ι → ℝ, Integrable (fun ω => u ⬝ᵥ X ω) μ
  mean_zero : ∀ u : ι → ℝ, (∫ ω, u ⬝ᵥ X ω ∂μ) = 0
  square_integrable : ∀ u : ι → ℝ, Integrable (fun ω => (u ⬝ᵥ X ω) ^ 2) μ
  second_moment : ∀ u : ι → ℝ, (∫ ω, (u ⬝ᵥ X ω) ^ 2 ∂μ) = u ⬝ᵥ u

/-- The paper's directional MGF sub-Gaussian condition with bound `K`.
Using arbitrary vectors instead of only unit vectors introduces the factor
`uᵀu` in the exponent. Finiteness of each MGF is stated explicitly. -/
structure SubGaussianMGF (μ : Measure Ω) (X : Ω → ι → ℝ) (K : ℝ) : Prop where
  integrable_exp : ∀ (u : ι → ℝ) (t : ℝ),
    Integrable (fun ω => Real.exp (t * (u ⬝ᵥ X ω))) μ
  mgf_bound : ∀ (u : ι → ℝ) (t : ℝ),
    (∫ ω, Real.exp (t * (u ⬝ᵥ X ω)) ∂μ) ≤
      Real.exp (t ^ 2 * K ^ 2 * (u ⬝ᵥ u) / 2)


end
end SingularValueBounds
