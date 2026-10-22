import Mathlib
import SingularValueBounds.Core.Constants

/-!
# Quadratic-form estimates and normalization

`QuadraticFormEstimates` packages the moment conclusions of Lemma 4.2 and
isotropy. `QuadraticForms/Bounds.lean` derives its fields from the original
isotropy and directional sub-Gaussian moment-generating-function condition.
The fields are square integrability, the isotropic mean, the quadratic second
moment and the variance bound at `K = 1`.

`QuadraticFormEstimates.normalize` gives the moments of the quadratic forms
used by both exponential shift bounds. The positive-part estimate is supplied
separately by `Shifts/QuadraticInput.lean` at its actual threshold.
-/

open MeasureTheory
open scoped Matrix BigOperators ENNReal

namespace SingularValueBounds

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- The real quadratic form evaluated at the random vector `X`. -/
def quadraticForm (B : Matrix ι ι ℝ) (X : Ω → ι → ℝ) : Ω → ℝ :=
  fun ω => X ω ⬝ᵥ (B *ᵥ X ω)

/-- The normalized quadratic form `Q₂` used by the shift estimates. -/
def normalizedQuadraticForm (R : Matrix ι ι ℝ) (X : Ω → ι → ℝ) : Ω → ℝ :=
  fun ω => quadraticForm (R ^ 2) X ω / Matrix.trace (R ^ 2)

/-- The quadratic-form moment and isotropy estimates used by both shifts. -/
structure QuadraticFormEstimates (μ : Measure Ω) (X : Ω → ι → ℝ) (K : ℝ) : Prop where
  memLp : ∀ B : Matrix ι ι ℝ, B.PosSemidef → MemLp (quadraticForm B X) 2 μ
  mean : ∀ B : Matrix ι ι ℝ, B.PosSemidef →
    (∫ ω, quadraticForm B X ω ∂μ) = Matrix.trace B
  second_moment : ∀ B : Matrix ι ι ℝ, B.PosSemidef →
    (∫ ω, quadraticForm B X ω ^ 2 ∂μ) ≤
      fourthMomentConstant K * Matrix.trace B ^ 2
  endpoint_variance : K = 1 → ∀ B : Matrix ι ι ℝ, B.PosSemidef →
    (∫ ω, (quadraticForm B X ω - Matrix.trace B) ^ 2 ∂μ) ≤
      2 * Matrix.trace (B ^ 2)

omit [MeasurableSpace Ω] [DecidableEq ι] in
theorem quadraticForm_nonneg {B : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (X : Ω → ι → ℝ) (ω : Ω) : 0 ≤ quadraticForm B X ω := by
  simpa only [quadraticForm, star_trivial] using hB.2 (X ω)

/-- Positive definiteness in a nonzero dimension makes the normalizing trace
strictly positive. -/
theorem trace_square_pos [Nonempty ι] {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    0 < Matrix.trace (R ^ 2) := by
  have hsym : ∀ i j, R j i = R i j := by
    intro i j
    have ht : Rᵀ = R := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian
    exact congrFun (congrFun ht i) j
  have hdiag : ∀ i, 0 < R i i := by
    intro i
    have hne : (Pi.single i (1 : ℝ) : ι → ℝ) ≠ 0 := by
      intro hz
      have hz' := congrFun hz i
      simp at hz'
    simpa only [star_trivial, Matrix.mulVec_single_one, single_dotProduct, one_mul]
      using hR.2 (Pi.single i (1 : ℝ)) hne
  have htrace : Matrix.trace (R ^ 2) = ∑ i, ∑ j, R i j ^ 2 := by
    simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym i j]
  rw [htrace]
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  exact lt_of_lt_of_le (sq_pos_of_pos (hdiag i))
    (Finset.single_le_sum (fun j _ => sq_nonneg (R i j)) (Finset.mem_univ i))

/-- The normalized moment facts used by the exponential shifts. Every field is
proved by `QuadraticFormEstimates.normalize`; none is an extra input. -/
structure NormalizedQuadraticFormEstimates
    (μ : Measure Ω) (X : Ω → ι → ℝ) (R : Matrix ι ι ℝ) (K : ℝ) : Prop where
  q2_nonneg : ∀ ω, 0 ≤ normalizedQuadraticForm R X ω
  q2_memLp : MemLp (normalizedQuadraticForm R X) 2 μ
  q2_mean : (∫ ω, normalizedQuadraticForm R X ω ∂μ) = 1
  q2_second : (∫ ω, normalizedQuadraticForm R X ω ^ 2 ∂μ) ≤ fourthMomentConstant K
  centered_memLp : MemLp (fun ω => quadraticForm R X ω - Matrix.trace R) 2 μ
  centered_mean : (∫ ω, quadraticForm R X ω - Matrix.trace R ∂μ) = 0
  endpoint_centered_second : K = 1 →
    (∫ ω, (quadraticForm R X ω - Matrix.trace R) ^ 2 ∂μ) ≤
      2 * Matrix.trace (R ^ 2)

/-- Normalize the quadratic form of `R²` and center that of `R`. -/
theorem QuadraticFormEstimates.normalize {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Nonempty ι] {X : Ω → ι → ℝ} {R : Matrix ι ι ℝ} {K : ℝ}
    (h : QuadraticFormEstimates μ X K) (hR : R.PosDef) :
    NormalizedQuadraticFormEstimates μ X R K := by
  have hR0 := hR.posSemidef
  have hR2 := hR0.pow 2
  have hS := trace_square_pos hR
  have hq1 := h.memLp R hR0
  have hq2 := h.memLp (R ^ 2) hR2
  refine ⟨?_, ?_, ?_, ?_,
    hq1.sub (memLp_const _), ?_, fun hK => h.endpoint_variance hK R hR0⟩
  · intro ω
    exact div_nonneg (quadraticForm_nonneg hR2 X ω) hS.le
  · change MemLp (fun ω => quadraticForm (R ^ 2) X ω / Matrix.trace (R ^ 2)) 2 μ
    convert hq2.const_mul (Matrix.trace (R ^ 2))⁻¹ using 1
    funext ω
    rw [div_eq_mul_inv, mul_comm]
  · simp only [normalizedQuadraticForm, integral_div, h.mean (R ^ 2) hR2]
    exact div_self hS.ne'
  · simp only [normalizedQuadraticForm, div_pow, integral_div]
    calc
      (∫ ω, quadraticForm (R ^ 2) X ω ^ 2 ∂μ) / Matrix.trace (R ^ 2) ^ 2 ≤
          (fourthMomentConstant K * Matrix.trace (R ^ 2) ^ 2) /
            Matrix.trace (R ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right (h.second_moment (R ^ 2) hR2) (sq_nonneg _)
      _ = fourthMomentConstant K := by field_simp [hS.ne']
  · rw [integral_sub (hq1.integrable (by norm_num)) (integrable_const _), h.mean R hR0]
    simp

end
end SingularValueBounds
