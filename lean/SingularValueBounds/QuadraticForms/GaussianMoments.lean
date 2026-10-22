import SingularValueBounds.QuadraticForms.GaussianComparison
import SingularValueBounds.QuadraticForms.ScalarMoments

/-!
# Exact Gaussian fourth moments

The Gaussian moments used to average directional estimates are obtained by
differentiating the already proved Gaussian MGF, then using finite-product
integration. No Gaussian moment identity is postulated.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators ENNReal NNReal

namespace SingularValueBounds

noncomputable section

theorem gaussian_mgf_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → ℝ} (v : ℝ)
    (hi : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) μ)
    (hm : ∀ t : ℝ, (∫ ω, Real.exp (t * Y ω) ∂μ) = Real.exp (v * t ^ 2 / 2)) :
    (∫ ω, Y ω ^ 2 ∂μ) = v ∧ (∫ ω, Y ω ^ 4 ∂μ) = 3 * v ^ 2 := by
  have hs : integrableExpSet Y μ = Set.univ := by
    ext t
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hi t
  have hz : 0 ∈ interior (integrableExpSet Y μ) := by rw [hs, interior_univ]; trivial
  let f : ℝ → ℝ := fun t => Real.exp (v * t ^ 2 / 2)
  have hmgf : mgf Y μ = f := funext hm
  have hd0 (t : ℝ) : HasDerivAt f (v * t * f t) t := by
    convert ((((hasDerivAt_id t).pow 2).const_mul v).div_const 2).exp using 1
    dsimp [f]
    ring
  have hd1 (t : ℝ) : HasDerivAt (fun t => v * t * f t)
      ((v + v ^ 2 * t ^ 2) * f t) t := by
    convert ((hasDerivAt_id t).const_mul v).mul (hd0 t) using 1
    dsimp only [id]
    ring
  have hd2 (t : ℝ) : HasDerivAt (fun t => (v + v ^ 2 * t ^ 2) * f t)
      ((3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f t) t := by
    convert ((hasDerivAt_const t v).add
      (((hasDerivAt_id t).pow 2).const_mul (v ^ 2))).mul (hd0 t) using 1
    dsimp only [id]
    ring
  have hd3 (t : ℝ) : HasDerivAt
      (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f t)
      ((3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * f t) t := by
    convert (((hasDerivAt_id t).const_mul (3 * v ^ 2)).add
      (((hasDerivAt_id t).pow 3).const_mul (v ^ 3))).mul (hd0 t) using 1
    dsimp only [id]
    ring
  have h1 : deriv f = fun t => v * t * f t := funext (fun t => (hd0 t).deriv)
  have h2 : deriv (fun t => v * t * f t) = fun t => (v + v ^ 2 * t ^ 2) * f t :=
    funext (fun t => (hd1 t).deriv)
  have h3 : deriv (fun t => (v + v ^ 2 * t ^ 2) * f t) =
      fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f t :=
    funext (fun t => (hd2 t).deriv)
  have h4 : deriv (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f t) =
      fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * f t :=
    funext (fun t => (hd3 t).deriv)
  constructor
  · have he := iteratedDeriv_mgf_zero hz 2
    simp only [Pi.pow_apply, hmgf] at he
    rw [← he]
    norm_num [iteratedDeriv_succ, h1, h2, f]
  · have he := iteratedDeriv_mgf_zero hz 4
    simp only [Pi.pow_apply, hmgf] at he
    rw [← he]
    norm_num [iteratedDeriv_succ, h1, h2, h3, h4, f]

theorem standardGaussian_linear_moments {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∫ g, (∑ i, a i * g i) ^ 2 ∂standardGaussian ι) = ∑ i, a i ^ 2 ∧
      (∫ g, (∑ i, a i * g i) ^ 4 ∂standardGaussian ι) =
        3 * (∑ i, a i ^ 2) ^ 2 := by
  apply gaussian_mgf_moments
  · intro t
    simpa only [Finset.mul_sum, mul_assoc] using
      standardGaussian_integrable_exp_sum (fun i => t * a i)
  · intro t
    calc
      _ = ∫ g, Real.exp (∑ i, (t * a i) * g i) ∂standardGaussian ι := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = Real.exp ((∑ i, (t * a i) ^ 2) / 2) := standardGaussian_integral_exp_sum _
      _ = _ := by
        congr 1
        simp only [mul_pow, ← Finset.mul_sum]
        ring

theorem standardGaussian_linear_pow_integrable {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (n : ℕ) :
    Integrable (fun g => (∑ i, a i * g i) ^ n) (standardGaussian ι) := by
  apply integrable_pow_of_integrable_exp_mul (t := 1) (by norm_num)
  · simpa only [one_mul] using standardGaussian_integrable_exp_sum a
  · simpa only [neg_mul, one_mul, Finset.sum_neg_distrib] using
      standardGaussian_integrable_exp_sum (fun i => -a i)

theorem standardGaussian_scalar_moments :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 ∧
      (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  simpa only [one_mul, one_pow, mul_one] using
    gaussian_mgf_moments (Y := id) 1 standardGaussian_integrable_exp
      (fun t => by simpa using standardGaussian_integral_exp t)

theorem standardGaussian_coordinate_sq_mul_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i j : ι) :
    (∫ g, (g i) ^ 2 * (g j) ^ 2 ∂standardGaussian ι) = if i = j then 3 else 1 := by
  let f : ι → ℝ → ℝ := fun k x =>
    (if k = i then x ^ 2 else 1) * (if k = j then x ^ 2 else 1)
  have hp (g : ι → ℝ) : (∏ k, f k (g k)) = (g i) ^ 2 * (g j) ^ 2 := by
    dsimp only [f]
    rw [Finset.prod_mul_distrib]
    simp
  have he := standardGaussian_integral_prod f
  simp_rw [hp] at he
  rw [he]
  by_cases hij : i = j
  · subst j
    have hv (k : ι) : (∫ x, f k x ∂gaussianReal 0 1) = if k = i then 3 else 1 := by
      by_cases hk : k = i
      · subst k
        simpa only [f, if_pos rfl, ite_true, ← pow_add, show 2 + 2 = 4 from rfl] using
          standardGaussian_scalar_moments.2
      · simp [f, hk]
    simp_rw [hv]
    simp
  · have hv (k : ι) : (∫ x, f k x ∂gaussianReal 0 1) = 1 := by
      by_cases hki : k = i
      · subst k
        simpa only [f, if_pos rfl, if_neg hij, mul_one] using
          standardGaussian_scalar_moments.1
      · by_cases hkj : k = j
        · subst k
          simpa only [f, if_neg hki, if_pos rfl, one_mul] using
            standardGaussian_scalar_moments.1
        · simp [f, hki, hkj]
    simp [hv, hij]

theorem standardGaussian_coordinate_sq_mul_sq_integrable {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i j : ι) :
    Integrable (fun g => (g i) ^ 2 * (g j) ^ 2) (standardGaussian ι) := by
  apply Integrable.of_integral_ne_zero
  rw [standardGaussian_coordinate_sq_mul_sq]
  split_ifs <;> norm_num

/-- The exact second moment of a diagonal Gaussian quadratic form. -/
theorem standardGaussian_quadratic_second {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    (∫ g, (∑ i, b i * (g i) ^ 2) ^ 2 ∂standardGaussian ι) =
      (∑ i, b i) ^ 2 + 2 * ∑ i, (b i) ^ 2 := by
  classical
  have hp (g : ι → ℝ) : (∑ i, b i * (g i) ^ 2) ^ 2 =
      ∑ i, ∑ j, (b i * b j) * ((g i) ^ 2 * (g j) ^ 2) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : ι) : Integrable
      (fun g => (b i * b j) * ((g i) ^ 2 * (g j) ^ 2)) (standardGaussian ι) :=
    (standardGaussian_coordinate_sq_mul_sq_integrable i j).const_mul _
  simp_rw [hp]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j), integral_const_mul,
    standardGaussian_coordinate_sq_mul_sq]
  have he (i j : ι) : (b i * b j) * (if i = j then 3 else 1) =
      b i * b j + (if j = i then 2 * (b i) ^ 2 else 0) := by
    by_cases hij : i = j
    · subst j; simp; ring
    · simp [hij, Ne.symm hij]
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

theorem standardGaussian_quadratic_sq_integrable {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    Integrable (fun g => (∑ i, b i * (g i) ^ 2) ^ 2) (standardGaussian ι) := by
  classical
  have hi : ∀ i j, Integrable
      (fun g => (b i * b j) * ((g i) ^ 2 * (g j) ^ 2)) (standardGaussian ι) :=
    fun i j => (standardGaussian_coordinate_sq_mul_sq_integrable i j).const_mul _
  convert integrable_finset_sum Finset.univ
    (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j)) using 1
  funext g
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end SingularValueBounds
