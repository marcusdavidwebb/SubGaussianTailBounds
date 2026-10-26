import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Function.L2Space
import SingularValueBounds.Core.Assumptions
import SingularValueBounds.Core.Matrix
import SingularValueBounds.QuadraticForms.Estimates

/-!
# Integrability and isotropic means of quadratic forms

These are direct consequences of the original directional hypotheses. This
file does not assume any quadratic-form moment or concentration estimate.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators ENNReal NNReal

namespace SingularValueBounds

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {μ : Measure Ω} {X : Ω → ι → ℝ} {K : ℝ}

/-- The directional hypothesis agrees with mathlib's scalar sub-Gaussian MGF
predicate, with variance proxy `K² * (uᵀu)`. -/
theorem SubGaussianMGF.directional (h : SubGaussianMGF μ X K) (u : ι → ℝ) :
    HasSubgaussianMGF (fun ω => u ⬝ᵥ X ω)
      ⟨K ^ 2 * (u ⬝ᵥ u), mul_nonneg (sq_nonneg K)
        (by simpa only [star_trivial] using dotProduct_star_self_nonneg u)⟩ μ := by
  refine ⟨h.integrable_exp u, ?_⟩
  intro t
  simpa only [mgf, NNReal.coe_mk, mul_comm, mul_left_comm, mul_assoc] using h.mgf_bound u t

/-- Every real directional projection has all finite absolute moments. -/
theorem SubGaussianMGF.directional_memLp (h : SubGaussianMGF μ X K)
    (u : ι → ℝ) (p : ℝ≥0) : MemLp (fun ω => u ⬝ᵥ X ω) p μ := by
  have hs : integrableExpSet (fun ω => u ⬝ᵥ X ω) μ = Set.univ := by
    ext t
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact h.integrable_exp u t
  apply memLp_of_mem_interior_integrableExpSet (p := p)
  rw [hs, interior_univ]
  trivial

theorem SubGaussianMGF.directional_integrable_pow (h : SubGaussianMGF μ X K)
    (u : ι → ℝ) (n : ℕ) : Integrable (fun ω => (u ⬝ᵥ X ω) ^ n) μ :=
  integrable_pow_of_integrable_exp_mul (by norm_num : (1 : ℝ) ≠ 0)
    (h.integrable_exp u 1) (h.integrable_exp u (-1)) n

theorem CentredIsotropic.directional_memLp_two (h : CentredIsotropic μ X)
    (u : ι → ℝ) : MemLp (fun ω => u ⬝ᵥ X ω) 2 μ :=
  (memLp_two_iff_integrable_sq (h.integrable u).aestronglyMeasurable).2
    (h.square_integrable u)

/-- Polarization of the directional isotropic second-moment identity. -/
theorem CentredIsotropic.directional_covariance (h : CentredIsotropic μ X)
    (u v : ι → ℝ) :
    (∫ ω, (u ⬝ᵥ X ω) * (v ⬝ᵥ X ω) ∂μ) = u ⬝ᵥ v := by
  have huv : Integrable (fun ω => (u ⬝ᵥ X ω) * (v ⬝ᵥ X ω)) μ :=
    (h.directional_memLp_two u).integrable_mul (h.directional_memLp_two v)
  have heq : (∫ ω, ((u + v) ⬝ᵥ X ω) ^ 2 ∂μ) =
      (∫ ω, (u ⬝ᵥ X ω) ^ 2 ∂μ) +
        2 * (∫ ω, (u ⬝ᵥ X ω) * (v ⬝ᵥ X ω) ∂μ) +
        (∫ ω, (v ⬝ᵥ X ω) ^ 2 ∂μ) := by
    calc
      _ = ∫ ω, (u ⬝ᵥ X ω) ^ 2 +
          2 * ((u ⬝ᵥ X ω) * (v ⬝ᵥ X ω)) + (v ⬝ᵥ X ω) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [add_dotProduct]
        ring
      _ = _ := by
        rw [integral_add (f := fun ω => (u ⬝ᵥ X ω) ^ 2 +
            2 * ((u ⬝ᵥ X ω) * (v ⬝ᵥ X ω)))
          ((h.square_integrable u).add (huv.const_mul 2)) (h.square_integrable v),
          integral_add (h.square_integrable u) (huv.const_mul 2), integral_const_mul]
  rw [h.second_moment, h.second_moment, h.second_moment] at heq
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm v u] at heq
  linarith

variable [DecidableEq ι]

theorem SubGaussianMGF.coordinate_memLp (h : SubGaussianMGF μ X K)
    (i : ι) (p : ℝ≥0) : MemLp (fun ω => X ω i) p μ := by
  simpa only [single_dotProduct, one_mul] using
    h.directional_memLp (Pi.single i (1 : ℝ)) p

theorem CentredIsotropic.coordinate_memLp_two (h : CentredIsotropic μ X)
    (i : ι) : MemLp (fun ω => X ω i) 2 μ := by
  simpa only [single_dotProduct, one_mul] using
    h.directional_memLp_two (Pi.single i (1 : ℝ))

theorem CentredIsotropic.coordinate_covariance (h : CentredIsotropic μ X)
    (i j : ι) : (∫ ω, X ω i * X ω j ∂μ) = if i = j then 1 else 0 := by
  simpa [single_dotProduct, Pi.single_apply, eq_comm] using
    h.directional_covariance (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))

omit [MeasurableSpace Ω] [DecidableEq ι] in
theorem quadraticForm_eq_sum (B : Matrix ι ι ℝ) (X : Ω → ι → ℝ) (ω : Ω) :
    quadraticForm B X ω = ∑ i, ∑ j, B i j * (X ω i * X ω j) := by
  simp only [quadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Isotropy alone gives integrability of every quadratic form. -/
theorem CentredIsotropic.quadratic_integrable (h : CentredIsotropic μ X)
    (B : Matrix ι ι ℝ) : Integrable (quadraticForm B X) μ := by
  have hi : ∀ i j, Integrable (fun ω => B i j * (X ω i * X ω j)) μ := by
    intro i j
    exact ((h.coordinate_memLp_two i).integrable_mul (h.coordinate_memLp_two j)).const_mul _
  have hs : Integrable (fun ω => ∑ i, ∑ j, B i j * (X ω i * X ω j)) μ :=
    integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))
  simpa only [← quadraticForm_eq_sum] using hs

/-- The isotropic quadratic-form identity, valid for every real matrix. -/
theorem CentredIsotropic.quadratic_mean (h : CentredIsotropic μ X)
    (B : Matrix ι ι ℝ) : (∫ ω, quadraticForm B X ω ∂μ) = Matrix.trace B := by
  have hi : ∀ i j, Integrable (fun ω => B i j * (X ω i * X ω j)) μ := by
    intro i j
    exact ((h.coordinate_memLp_two i).integrable_mul (h.coordinate_memLp_two j)).const_mul _
  simp_rw [quadraticForm_eq_sum]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j), integral_const_mul,
    h.coordinate_covariance]
  simp [Matrix.trace]

/-- Directional sub-Gaussianity supplies the square integrability needed in
the quadratic-form estimates, without a moment bound as a hypothesis. -/
theorem SubGaussianMGF.quadratic_memLp_two (h : SubGaussianMGF μ X K)
    (B : Matrix ι ι ℝ) : MemLp (quadraticForm B X) 2 μ := by
  haveI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := ⟨by
    have hn0 : (4 : ℝ≥0)⁻¹ + 4⁻¹ = 2⁻¹ := by
      apply NNReal.coe_injective
      norm_num
    have hn := congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) hn0
    simpa only [ENNReal.coe_add, ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
      ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using hn⟩
  have h4 : ∀ i, MemLp (fun ω => X ω i) (4 : ℝ≥0∞) μ := by
    intro i
    simpa only [ENNReal.coe_ofNat] using h.coordinate_memLp i 4
  have hi : ∀ i j, MemLp (fun ω => B i j * (X ω i * X ω j)) 2 μ := by
    intro i j
    exact ((h4 j).mul' (h4 i)).const_mul _
  have hs : MemLp (fun ω => ∑ i, ∑ j, B i j * (X ω i * X ω j)) 2 μ :=
    memLp_finset_sum _ (fun i _ => memLp_finset_sum _ (fun j _ => hi i j))
  simpa only [← quadraticForm_eq_sum] using hs

omit [MeasurableSpace Ω] in
theorem dot_unitary_star_mulVec (U : Matrix.unitaryGroup ι ℝ) (u x : ι → ℝ) :
    u ⬝ᵥ (star (U : Matrix ι ι ℝ) *ᵥ x) = ((U : Matrix ι ι ℝ) *ᵥ u) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec]
  have hv : u ᵥ* star (U : Matrix ι ι ℝ) = (U : Matrix ι ι ℝ) *ᵥ u := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Matrix.vecMul_transpose (U : Matrix ι ι ℝ) u
  rw [hv]

omit [MeasurableSpace Ω] in
theorem unitary_mulVec_dot (U : Matrix.unitaryGroup ι ℝ) (u v : ι → ℝ) :
    ((U : Matrix ι ι ℝ) *ᵥ u) ⬝ᵥ ((U : Matrix ι ι ℝ) *ᵥ v) = u ⬝ᵥ v := by
  rw [← dot_unitary_star_mulVec U, Matrix.mulVec_mulVec, U.2.1, Matrix.one_mulVec]

/-- Orthogonal coordinate changes preserve the directional MGF hypothesis. -/
theorem SubGaussianMGF.unitary (h : SubGaussianMGF μ X K)
    (U : Matrix.unitaryGroup ι ℝ) :
    SubGaussianMGF μ (fun ω => star (U : Matrix ι ι ℝ) *ᵥ X ω) K := by
  constructor
  · intro u t
    simpa only [dot_unitary_star_mulVec] using
      h.integrable_exp ((U : Matrix ι ι ℝ) *ᵥ u) t
  · intro u t
    simpa only [dot_unitary_star_mulVec, unitary_mulVec_dot] using
      h.mgf_bound ((U : Matrix ι ι ℝ) *ᵥ u) t

/-- Orthogonal coordinate changes also preserve centering and isotropy. -/
theorem CentredIsotropic.unitary (h : CentredIsotropic μ X)
    (U : Matrix.unitaryGroup ι ℝ) :
    CentredIsotropic μ (fun ω => star (U : Matrix ι ι ℝ) *ᵥ X ω) := by
  constructor
  · have hm := h.measurable
    change Measurable (fun ω i => ∑ j, (star (U : Matrix ι ι ℝ)) i j * X ω j)
    fun_prop
  · intro u
    simpa only [dot_unitary_star_mulVec] using
      h.integrable ((U : Matrix ι ι ℝ) *ᵥ u)
  · intro u
    simpa only [dot_unitary_star_mulVec] using
      h.mean_zero ((U : Matrix ι ι ℝ) *ᵥ u)
  · intro u
    simpa only [dot_unitary_star_mulVec] using
      h.square_integrable ((U : Matrix ι ι ℝ) *ᵥ u)
  · intro u
    simpa only [dot_unitary_star_mulVec, unitary_mulVec_dot] using
      h.second_moment ((U : Matrix ι ι ℝ) *ᵥ u)


end
end SingularValueBounds
