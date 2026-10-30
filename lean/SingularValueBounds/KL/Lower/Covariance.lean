import SingularValueBounds.KL.Statement

/-! # Endpoint quadratic covariances

Supplementary S1.5, `eq:app-K-one-covariance` and
`eq:app-K-one-rankone-covariance`. The centered products below are defined
directly by integrals, so their integrability is explicit throughout.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace SingularValueBounds.KL
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ}

def centeredQuadratic (A : Matrix ι ι ℝ) (X : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  quadraticForm A X ω - Matrix.trace A

def quadraticCovariance (μ : Measure Ω) (X : Ω → ι → ℝ)
    (A B : Matrix ι ι ℝ) : ℝ :=
  ∫ ω, centeredQuadratic A X ω * centeredQuadratic B X ω ∂μ

theorem centeredQuadratic_memLp (hsg : SubGaussianMGF μ X 1)
    (A : Matrix ι ι ℝ) : MemLp (centeredQuadratic A X) 2 μ :=
  (hsg.quadratic_memLp_two A).sub (memLp_const _)

theorem quadraticCovariance_comm (A B : Matrix ι ι ℝ) :
    quadraticCovariance μ X A B = quadraticCovariance μ X B A := by
  simp only [quadraticCovariance, mul_comm]

theorem quadraticCovariance_self_nonneg (A : Matrix ι ι ℝ) :
    0 ≤ quadraticCovariance μ X A A := by
  exact integral_nonneg fun ω => mul_self_nonneg _

lemma centeredQuadratic_add_smul (A B : Matrix ι ι ℝ) (s t : ℝ) (ω : Ω) :
    centeredQuadratic (s • A + t • B) X ω =
      s * centeredQuadratic A X ω + t * centeredQuadratic B X ω := by
  simp only [centeredQuadratic, quadraticForm, Matrix.add_mulVec,
    Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

theorem quadraticCovariance_add_smul (hsg : SubGaussianMGF μ X 1)
    (A B : Matrix ι ι ℝ) (s t : ℝ) :
    quadraticCovariance μ X (s • A + t • B) (s • A + t • B) =
      s ^ 2 * quadraticCovariance μ X A A +
      2 * s * t * quadraticCovariance μ X A B +
      t ^ 2 * quadraticCovariance μ X B B := by
  have ha := centeredQuadratic_memLp hsg A
  have hb := centeredQuadratic_memLp hsg B
  have he (ω : Ω) : centeredQuadratic (s • A + t • B) X ω *
      centeredQuadratic (s • A + t • B) X ω =
      s ^ 2 * (centeredQuadratic A X ω * centeredQuadratic A X ω) +
      (2 * s * t) * (centeredQuadratic A X ω * centeredQuadratic B X ω) +
      t ^ 2 * (centeredQuadratic B X ω * centeredQuadratic B X ω) := by
    rw [centeredQuadratic_add_smul]
    ring
  unfold quadraticCovariance
  simp_rw [he]
  rw [integral_add (f := fun ω => s ^ 2 * (centeredQuadratic A X ω * centeredQuadratic A X ω) +
      (2 * s * t) * (centeredQuadratic A X ω * centeredQuadratic B X ω))
      (g := fun ω => t ^ 2 * (centeredQuadratic B X ω * centeredQuadratic B X ω))
      (((ha.integrable_mul ha).const_mul (s ^ 2)).add ((ha.integrable_mul hb).const_mul (2*s*t)))
      ((hb.integrable_mul hb).const_mul (t ^ 2)),
    integral_add (f := fun ω => s ^ 2 * (centeredQuadratic A X ω * centeredQuadratic A X ω))
      (g := fun ω => (2 * s * t) * (centeredQuadratic A X ω * centeredQuadratic B X ω))
      ((ha.integrable_mul ha).const_mul (s ^ 2)) ((ha.integrable_mul hb).const_mul (2*s*t))]
  simp only [integral_const_mul]

/-- The centered definition agrees with the usual mixed moment minus means. -/
theorem quadraticCovariance_eq_mixed (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (A B : Matrix ι ι ℝ) :
    quadraticCovariance μ X A B =
      (∫ ω, quadraticForm A X ω * quadraticForm B X ω ∂μ) -
        Matrix.trace A * Matrix.trace B := by
  have ha := hiso.quadratic_integrable A
  have hb := hiso.quadratic_integrable B
  have hab := (hsg.quadratic_memLp_two A).integrable_mul (hsg.quadratic_memLp_two B)
  have he (ω : Ω) : centeredQuadratic A X ω * centeredQuadratic B X ω =
      quadraticForm A X ω * quadraticForm B X ω -
        Matrix.trace B * quadraticForm A X ω -
        Matrix.trace A * quadraticForm B X ω + Matrix.trace A * Matrix.trace B := by
    dsimp [centeredQuadratic]
    ring
  unfold quadraticCovariance
  simp_rw [he]
  rw [integral_add (f := fun ω => quadraticForm A X ω * quadraticForm B X ω -
      Matrix.trace B * quadraticForm A X ω - Matrix.trace A * quadraticForm B X ω)
      (g := fun _ => Matrix.trace A * Matrix.trace B)
      ((hab.sub (ha.const_mul _)).sub (hb.const_mul _)) (integrable_const _),
    integral_sub (f := fun ω => quadraticForm A X ω * quadraticForm B X ω -
      Matrix.trace B * quadraticForm A X ω)
      (g := fun ω => Matrix.trace A * quadraticForm B X ω)
      (hab.sub (ha.const_mul _)) (hb.const_mul _),
    integral_sub (f := fun ω => quadraticForm A X ω * quadraticForm B X ω)
      (g := fun ω => Matrix.trace B * quadraticForm A X ω) hab (ha.const_mul _)]
  simp only [integral_const_mul, integral_const, probReal_univ,
    smul_eq_mul, one_mul, hiso.quadratic_mean]
  ring

theorem quadraticCovariance_self_le (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    quadraticCovariance μ X A A ≤ 2 * Matrix.trace (A ^ 2) := by
  simpa only [quadraticCovariance, centeredQuadratic, ← pow_two] using
    quadratic_endpoint_variance hsg hiso A hA

lemma endpoint_psd_smul (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 ≤ s) : (s • A).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · change (s • A)ᴴ = s • A
    simp only [Matrix.conjTranspose_smul, star_trivial, hA.isHermitian.eq]
  ·
    intro x
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg hs (hA.dotProduct_mulVec_nonneg x)

lemma trace_square_add_smul (A B : Matrix ι ι ℝ) (s t : ℝ) :
    Matrix.trace ((s • A + t • B) ^ 2) = s ^ 2 * Matrix.trace (A ^ 2) +
      2 * s * t * Matrix.trace (A * B) + t ^ 2 * Matrix.trace (B ^ 2) := by
  simp only [pow_two, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [Matrix.trace_mul_comm B A]
  ring

/-- Variance positivity and the endpoint variance estimate, before optimizing
the two nonnegative scales. No commutation hypothesis is used. -/
theorem endpoint_covariance_scaled (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (A B : Matrix ι ι ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    4 * s * t * quadraticCovariance μ X A B ≤
      2 * s ^ 2 * Matrix.trace (A ^ 2) +
      4 * s * t * Matrix.trace (A * B) +
      2 * t ^ 2 * Matrix.trace (B ^ 2) := by
  have hn := quadraticCovariance_self_nonneg (μ := μ) (X := X) (s • A + (-t) • B)
  rw [quadraticCovariance_add_smul hsg] at hn
  have hu := quadraticCovariance_self_le hsg hiso (s • A + t • B)
    ((endpoint_psd_smul A hA hs).add (endpoint_psd_smul B hB ht))
  rw [quadraticCovariance_add_smul hsg, trace_square_add_smul] at hu
  nlinarith

lemma frobenius_eq_zero_iff (A : Matrix ι ι ℝ) : frobenius A = 0 ↔ A = 0 := by
  constructor
  · intro ha
    have hs := frobenius_sq A
    rw [ha] at hs
    have hz : ∀ i j, A i j = 0 := by
      intro i j
      have hi := Finset.single_le_sum (s := Finset.univ)
        (f := fun k => ∑ l, A k l ^ 2)
        (fun k (_ : k ∈ Finset.univ) =>
          Finset.sum_nonneg (fun l _ => sq_nonneg (A k l))) (Finset.mem_univ i)
      have hj := Finset.single_le_sum (s := Finset.univ)
        (fun l (_ : l ∈ Finset.univ) => sq_nonneg (A i l)) (Finset.mem_univ j)
      nlinarith [sq_nonneg (A i j)]
    ext i j
    exact hz i j
  · rintro rfl
    simp [frobenius]

/-- Supplementary `eq:app-K-one-covariance`, for arbitrary PSD matrices.
In particular the matrices need not commute or share eigenvectors. -/
theorem endpoint_covariance_le (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (A B : Matrix ι ι ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    quadraticCovariance μ X A B ≤
      frobenius A * frobenius B + Matrix.trace (A * B) := by
  by_cases haz : frobenius A = 0
  · rw [(frobenius_eq_zero_iff A).mp haz]
    simp [quadraticCovariance, centeredQuadratic, quadraticForm, frobenius]
  by_cases hbz : frobenius B = 0
  · rw [(frobenius_eq_zero_iff B).mp hbz]
    simp [quadraticCovariance, centeredQuadratic, quadraticForm, frobenius]
  have ha : 0 < frobenius A := lt_of_le_of_ne (frobenius_nonneg A) (Ne.symm haz)
  have hb : 0 < frobenius B := lt_of_le_of_ne (frobenius_nonneg B) (Ne.symm hbz)
  have h := endpoint_covariance_scaled hsg hiso A B hA hB hb.le ha.le
  have hfa : Matrix.trace (A ^ 2) = frobenius A ^ 2 := by
    rw [trace_square_eq_sum_sq hA.isHermitian, frobenius_sq]
  have hfb : Matrix.trace (B ^ 2) = frobenius B ^ 2 := by
    rw [trace_square_eq_sum_sq hB.isHermitian, frobenius_sq]
  rw [hfa, hfb] at h
  have hp : 0 < 4 * frobenius B * frobenius A := by positivity
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith only [h]

end
end SingularValueBounds.KL
