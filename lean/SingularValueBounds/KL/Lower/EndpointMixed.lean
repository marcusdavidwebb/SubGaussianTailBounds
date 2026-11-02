import SingularValueBounds.KL.Lower.EndpointSpectrum

/-! # Endpoint spectral mixed costs

The ordinary covariance and Young bounds in supplementary S1.5, with
the scalar majorant `g` kept in its printed form.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ}

def diagonalQuadratic (b : ι → ℝ) (X : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, b i * X ω i ^ 2

omit [MeasurableSpace Ω] in
lemma quadraticForm_diagonal_eq (b : ι → ℝ) :
    quadraticForm (Matrix.diagonal b) X = diagonalQuadratic b X := by
  ext ω
  simp only [quadraticForm, diagonalQuadratic, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma frobenius_diagonal_eq (b : ι → ℝ) :
    frobenius (Matrix.diagonal b) = Real.sqrt (∑ i, b i ^ 2) := by
  have hh := Matrix.isHermitian_diagonal b
  rw [frobenius_eq_sqrt_trace_square hh]
  simp only [pow_two, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

def endpointOrdinaryCost (r : ι → ℝ) (A c : ℝ) : ℝ :=
  A+(1-c)*spectralMoment r 3+A*spectralMoment r 4-c*spectralMoment r 5 +
    Real.sqrt (spectralMoment r 4)*Real.sqrt (∑ i, endpointComparisonEigen A c (r i)^2)

theorem endpoint_diagonal_mixed_cost (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (r : ι → ℝ) (A c : ℝ)
    (h2 : spectralMoment r 2 = 1)
    (hf : ∀ i, 0 ≤ endpointComparisonEigen A c (r i)) :
    (∫ ω, diagonalQuadratic (fun i => r i ^ 2) X ω *
      diagonalQuadratic (fun i => endpointComparisonEigen A c (r i)) X ω ∂μ) -
      (∑ i, r i) ≤ endpointOrdinaryCost r A c := by
  have he := endpoint_covariance_le hsg hiso
    (Matrix.diagonal (fun i => r i^2))
    (Matrix.diagonal (fun i => endpointComparisonEigen A c (r i)))
    (Matrix.posSemidef_diagonal_iff.mpr (fun i => sq_nonneg _))
    (Matrix.posSemidef_diagonal_iff.mpr hf)
  rw [quadraticCovariance_eq_mixed hsg hiso] at he
  simp only [Matrix.trace_diagonal, Matrix.diagonal_mul_diagonal,
    frobenius_diagonal_eq, ← pow_mul, show 2*2=4 from rfl,
    quadraticForm_diagonal_eq] at he
  change (∫ ω, diagonalQuadratic (fun i => r i^2) X ω *
      diagonalQuadratic (fun i => endpointComparisonEigen A c (r i)) X ω ∂μ) -
      spectralMoment r 2 * (∑ i, endpointComparisonEigen A c (r i)) ≤
      Real.sqrt (spectralMoment r 4)*Real.sqrt (∑ i, endpointComparisonEigen A c (r i)^2) +
        (∑ i, r i^2 * endpointComparisonEigen A c (r i)) at he
  rw [h2, one_mul] at he
  have hid : (∑ i, endpointComparisonEigen A c (r i)) +
      (∑ i, r i^2*endpointComparisonEigen A c (r i)) - (∑ i, r i) =
      A+(1-c)*spectralMoment r 3+A*spectralMoment r 4-c*spectralMoment r 5 := by
    have hp (x : ℝ) : endpointComparisonEigen A c x+x^2*endpointComparisonEigen A c x-x =
        A*x^2+(1-c)*x^3+A*x^4-c*x^5 := by dsimp [endpointComparisonEigen]; ring
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    simp_rw [hp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change A*spectralMoment r 2+(1-c)*spectralMoment r 3+A*spectralMoment r 4-c*spectralMoment r 5 = _
    rw [h2, mul_one]
  dsimp [endpointOrdinaryCost]
  linarith

def endpointG (A c ξ x : ℝ) : ℝ :=
  (A/ξ+1-c)*x + (A+ξ/2+(A^2-2*c)/(2*ξ))*x^2 -
    (c+A*c/ξ)*x^3+c^2/(2*ξ)*x^4

omit [DecidableEq ι] in
theorem endpoint_ordinary_cost_young (r : ι → ℝ) (A c : ℝ)
    (h2 : spectralMoment r 2 = 1) {ξ : ℝ} (hξ : 0 < ξ) :
    endpointOrdinaryCost r A c ≤ A+1/(2*ξ)+(∑ i, r i^2*endpointG A c ξ (r i)) := by
  have hs4 : 0 ≤ spectralMoment r 4 := Finset.sum_nonneg fun _ _ => by positivity
  have hB : 0 ≤ ∑ i, endpointComparisonEigen A c (r i)^2 := Finset.sum_nonneg fun _ _ => by positivity
  have hy : Real.sqrt (spectralMoment r 4)*Real.sqrt (∑ i, endpointComparisonEigen A c (r i)^2) ≤
      ξ/2*spectralMoment r 4+(∑ i, endpointComparisonEigen A c (r i)^2)/(2*ξ) := by
    apply (mul_le_mul_iff_left₀ (show 0 < 2*ξ by positivity)).mp
    have hs := sq_nonneg (Real.sqrt (∑ i, endpointComparisonEigen A c (r i)^2) -
      ξ*Real.sqrt (spectralMoment r 4))
    have hex : (Real.sqrt (∑ i, endpointComparisonEigen A c (r i)^2)-
        ξ*Real.sqrt (spectralMoment r 4))^2 =
        (∑ i, endpointComparisonEigen A c (r i)^2)+ξ^2*spectralMoment r 4-
        2*ξ*Real.sqrt (spectralMoment r 4)*Real.sqrt (∑ i, endpointComparisonEigen A c (r i)^2) := by
      rw [sub_sq, mul_pow, Real.sq_sqrt hs4, Real.sq_sqrt hB]
      ring
    rw [hex] at hs
    have heq : (ξ/2*spectralMoment r 4+(∑ i, endpointComparisonEigen A c (r i)^2)/(2*ξ))*(2*ξ) =
        ξ^2*spectralMoment r 4+(∑ i, endpointComparisonEigen A c (r i)^2) := by
      field_simp [hξ.ne']
    rw [heq]
    nlinarith only [hs]
  have hp (x : ℝ) : x^2*endpointG A c ξ x =
      (A/ξ+1-c)*x^3+(A+ξ/2+(A^2-2*c)/(2*ξ))*x^4 -
      (c+A*c/ξ)*x^5+c^2/(2*ξ)*x^6 := by dsimp [endpointG]; ring
  have he : A+1/(2*ξ)+(∑ i, r i^2*endpointG A c ξ (r i)) =
      A+(1-c)*spectralMoment r 3+A*spectralMoment r 4-c*spectralMoment r 5 +
      ξ/2*spectralMoment r 4+(∑ i, endpointComparisonEigen A c (r i)^2)/(2*ξ) := by
    simp_rw [hp]
    rw [endpointComparisonEigen_sq_sum, h2]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change A+1/(2*ξ)+((A/ξ+1-c)*spectralMoment r 3+
      (A+ξ/2+(A^2-2*c)/(2*ξ))*spectralMoment r 4-
      (c+A*c/ξ)*spectralMoment r 5+c^2/(2*ξ)*spectralMoment r 6) = _
    field_simp [hξ.ne']
    ring
  rw [he]
  dsimp [endpointOrdinaryCost]
  linarith

end
end SingularValueBounds.KL
