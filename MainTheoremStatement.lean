import NLAlib.Probability.SubGaussianVector.Basic
import NLAlib.Matrix.Spectral.SingularValues

open MeasureTheory ProbabilityTheory

namespace SubGaussian
universe u

def GaussianSingularValueTails {Ω : Type u} {m n : ℕ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (lower upper t : ℝ) : Prop :=
    (μ {ω | NLAlib.singularValues (A ω) (n-1) ≤ lower}).toReal ≤ Real.exp(-(t^2)/2))
      ∧ (μ {ω | NLAlib.singularValues (A ω) 0 ≥ upper}).toReal ≤ Real.exp(-(t^2)/2))

def TailBoundAt (K α β γ δ : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m n : ℕ) (A : Ω → Matrix (Fin m) (Fin n) ℝ),
    1 ≤ n → n ≤ m →
    (∀ i, Measurable (fun ω => A ω i)) →
    iIndepFun (fun i ω => A ω i) μ →
    (∀ i, NLAlib.IsIsotropic (fun ω => A ω i) μ) →
    (∀ i, NLAlib.IsSubgaussianVector (fun ω => A ω i) ⟨K ^ 2, sq_nonneg K⟩ μ) →
    ∀ t : ℝ, 0 ≤ t →
    let L := Real.log (Real.exp 1 * K)
    GaussianSingularValueTails μ A (√m - K * √n - α * K * L - β * K * √L * t)
      (√m + K * √n + γ * K * L + δ * K * √L * t) t

def GeneralSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧ ∀ K : ℝ, 1 ≤ K → TailBoundAt.{u} K α β γ δ

def UnitSingularValueTailBound (α β γ δ : ℝ) : Prop :=
  (0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ) ∧ TailBoundAt.{u} 1 α β γ δ

end SubGaussian
