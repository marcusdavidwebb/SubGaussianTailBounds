import SingularValueBounds.KL.Upper.TailMoments
import SingularValueBounds.KL.Weighted.Gaussian
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Nat.Choose.Central

/-! # Coefficients of the explicit Gaussian majorant (supplementary S1.6.4)

These are moments of the auxiliary Gaussian variable. No coefficientwise
comparison with the original sub-Gaussian vector is inferred from an MGF
inequality.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

def gaussianSquareCoefficient : ℕ → ℝ
  | 0 => 1
  | p+1 => ((2*p+1 : ℝ)/(p+1))*gaussianSquareCoefficient p

theorem gaussianSquareCoefficient_nonneg (p : ℕ) : 0 ≤ gaussianSquareCoefficient p := by
  induction p with
  | zero => norm_num [gaussianSquareCoefficient]
  | succ p ih => simp only [gaussianSquareCoefficient]; positivity

theorem gaussianSquareCoefficient_pos (p : ℕ) : 0 < gaussianSquareCoefficient p := by
  induction p with
  | zero => norm_num [gaussianSquareCoefficient]
  | succ p ih => simp only [gaussianSquareCoefficient]; positivity

theorem gaussianSquareCoefficient_eq_centralBinom (p : ℕ) :
    gaussianSquareCoefficient p = (Nat.centralBinom p : ℝ)/2^p := by
  induction p with
  | zero => norm_num [gaussianSquareCoefficient]
  | succ p ih =>
    rw [gaussianSquareCoefficient,ih,pow_succ]
    have h : ((p : ℝ)+1)*(Nat.centralBinom (p+1) : ℝ) =
        2*(2*p+1)*(Nat.centralBinom p : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ p
    field_simp
    nlinarith [congrArg (fun z : ℝ => z*(2 : ℝ)^p) h]

theorem gaussianSquareCoefficient_step (p : ℕ) :
    gaussianSquareCoefficient (p+1) ≤ 2*gaussianSquareCoefficient p := by
  have hp : (0 : ℝ) < p+1 := by positivity
  have h : (2*p+1 : ℝ)/(p+1) ≤ 2 := (div_le_iff₀ hp).2 (by linarith)
  exact mul_le_mul_of_nonneg_right h (gaussianSquareCoefficient_nonneg p)

private def gaussianSquareDerivative (p : ℕ) (t : ℝ) : ℝ :=
  (p.factorial : ℝ)*gaussianSquareCoefficient p*(1-2*t)^(-(p : ℝ)-1/2 : ℝ)

private theorem gaussianSquareDerivative_hasDeriv (p : ℕ) {t : ℝ} (ht : t < 1/2) :
    HasDerivAt (gaussianSquareDerivative p) (gaussianSquareDerivative (p+1) t) t := by
  have hbase : 1-2*t ≠ 0 := ne_of_gt (by linarith)
  have hd := (((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul 2)).rpow_const
    (p := -(p : ℝ)-1/2) (Or.inl hbase)).const_mul
      ((p.factorial : ℝ)*gaussianSquareCoefficient p)
  convert! hd using 1
  simp only [gaussianSquareDerivative,gaussianSquareCoefficient,Nat.factorial_succ,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [show -((p : ℝ)+1)-1/2=-(p : ℝ)-1/2-1 by ring]
  simp only [id_eq, Pi.sub_apply, zero_sub, mul_one]
  field_simp
  <;> ring

private theorem gaussianSquare_iteratedDeriv (p : ℕ) {t : ℝ} (ht : t < 1/2) :
    iteratedDeriv p (fun x : ℝ => (1-2*x)^(-(1/2 : ℝ))) t =
      gaussianSquareDerivative p t := by
  induction p generalizing t with
  | zero => simp [gaussianSquareDerivative,gaussianSquareCoefficient]
  | succ p ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv p (fun x : ℝ => (1-2*x)^(-(1/2 : ℝ))) =ᶠ[nhds t]
        gaussianSquareDerivative p := by
      filter_upwards [Iio_mem_nhds ht] with x hx
      exact ih hx
    exact he.deriv_eq.trans (gaussianSquareDerivative_hasDeriv p ht).deriv

/-- Every coefficient of the auxiliary squared Gaussian's MGF is identified
by derivatives of its actual density-derived MGF. -/
theorem standardGaussian_square_moment (p : ℕ) :
    (∫ x : ℝ, (x^2)^p ∂gaussianReal 0 1)/(p.factorial : ℝ) =
      gaussianSquareCoefficient p := by
  let G : ℝ → ℝ := fun x => x^2
  have hi (t : ℝ) (ht : t < 1/2) : Integrable (fun x => Real.exp (t*G x)) (gaussianReal 0 1) := by
    apply Integrable.of_integral_ne_zero
    rw [show (fun x => Real.exp (t*G x))=(fun x => Real.exp (t*x^2)) by rfl,
      standardGaussian_integral_exp_sq t (by linarith)]
    exact inv_ne_zero (Real.sqrt_pos.mpr (by linarith)).ne'
  have hz : 0 ∈ interior (integrableExpSet G (gaussianReal 0 1)) := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))
    intro t ht
    exact hi t ht
  have he : mgf G (gaussianReal 0 1) =ᶠ[nhds (0 : ℝ)]
      (fun t => (1-2*t)^(-(1/2 : ℝ))) := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2)] with t ht
    have ht' : t < 1/2 := ht
    change (∫ x, Real.exp (t*x^2) ∂gaussianReal 0 1) = _
    rw [standardGaussian_integral_exp_sq t (by linarith), Real.rpow_neg (by linarith),
      Real.sqrt_eq_rpow]
  have hm := iteratedDeriv_mgf_zero hz p
  rw [he.iteratedDeriv_eq p,gaussianSquare_iteratedDeriv p (by norm_num)] at hm
  dsimp [gaussianSquareDerivative,G] at hm
  simp only [mul_zero,sub_zero,Real.one_rpow,mul_one] at hm
  rw [← hm]
  field_simp

/-- All the Gaussian majorant moments are integrable before any series
interchange. -/
theorem standardGaussian_square_moment_integrable (p : ℕ) :
    Integrable (fun x : ℝ => (x^2)^p) (gaussianReal 0 1) := by
  apply integrable_pow_of_integrable_exp_mul (t := 1/4) (by norm_num)
  · apply Integrable.of_integral_ne_zero
    rw [standardGaussian_integral_exp_sq (1/4) (by norm_num)]
    positivity

  · apply Integrable.of_integral_ne_zero
    rw [standardGaussian_integral_exp_sq (-(1/4)) (by norm_num)]
    positivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem standardGaussian_coordinate_even_integrable (i : ι) (p : ℕ) :
    Integrable (fun g : ι → ℝ => ((g i)^2)^p) (standardGaussian ι) := by
  have h := standardGaussian_linear_pow_integrable (Pi.single i (1 : ℝ)) (2*p)
  simpa only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,← pow_mul] using h

theorem standardGaussian_coordinate_even_moment (i : ι) (p : ℕ) :
    (∫ g : ι → ℝ, ((g i)^2)^p ∂standardGaussian ι) =
      (p.factorial : ℝ)*gaussianSquareCoefficient p := by
  let f : ι → ℝ → ℝ := fun j x => if j=i then (x^2)^p else 1
  have hprod (g : ι → ℝ) : (∏ j, f j (g j)) = ((g i)^2)^p := by
    simp [f]
  have hi := standardGaussian_integral_prod f
  simp_rw [hprod] at hi
  have hv (j : ι) : (∫ x, f j x ∂gaussianReal 0 1) =
      if j=i then (p.factorial : ℝ)*gaussianSquareCoefficient p else 1 := by
    by_cases hj : j=i
    · simp only [f,hj,if_true]
      exact (div_eq_iff (by positivity : (p.factorial : ℝ)≠0)).mp
        (standardGaussian_square_moment p) |>.trans (by ring)
    · simp [f,hj]
  rw [hi]
  simp only [hv,Finset.prod_ite_eq',Finset.mem_univ,if_true]

/-- Jensen bounds the moments of the explicitly constructed Gaussian
quadratic majorant, retaining its exact second coefficient separately. -/
theorem standardGaussian_quadratic_moment_le {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1) (p : ℕ) :
    Integrable (fun g : ι → ℝ => (∑ i, w i*(g i)^2)^p) (standardGaussian ι) ∧
      (∫ g : ι → ℝ, (∑ i, w i*(g i)^2)^p ∂standardGaussian ι)/(p.factorial : ℝ) ≤
        gaussianSquareCoefficient p := by
  have hpoint (g : ι → ℝ) : (∑ i, w i*(g i)^2)^p ≤
      ∑ i, w i*((g i)^2)^p := by
    simpa only [smul_eq_mul] using (convexOn_pow (𝕜 := ℝ) p).map_sum_le
      (t := Finset.univ) (w := w) (p := fun i => (g i)^2)
      (fun i hi => hw i) hsum (fun i hi => sq_nonneg (g i))
  have hupper : Integrable (fun g : ι → ℝ => ∑ i, w i*((g i)^2)^p)
      (standardGaussian ι) := integrable_finsetSum _
    (fun i hi => (standardGaussian_coordinate_even_integrable i p).const_mul (w i))
  have hInt : Integrable (fun g : ι → ℝ => (∑ i, w i*(g i)^2)^p) (standardGaussian ι) := by
    apply hupper.mono'
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · exact Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Finset.sum_nonneg
          (fun i hi => mul_nonneg (hw i) (sq_nonneg (g i)))) p)]
        exact hpoint g
  refine ⟨hInt, ?_⟩
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<p.factorial)).2
  have hi := integral_mono hInt hupper hpoint
  rw [integral_finsetSum _ (fun i hi =>
    (standardGaussian_coordinate_even_integrable i p).const_mul (w i))] at hi
  simp_rw [integral_const_mul,standardGaussian_coordinate_even_moment] at hi
  rw [← Finset.sum_mul,hsum,one_mul] at hi
  simpa only [mul_comm] using hi

/-- Exact shifted-exponential coefficients from the printed rare-event
majorant, including their factorial recurrence. -/
def shiftedExponentialCoefficient (p : ℕ) (A s : ℝ) : ℝ :=
  tailMomentSeries (p+1) A s

theorem shiftedExponentialCoefficient_succ {p : ℕ} (A s : ℝ) :
    shiftedExponentialCoefficient (p+1) A s =
      s*shiftedExponentialCoefficient p A s+A^(p+1)/((p+1).factorial : ℝ) := by
  exact tailMomentSeries_succ (by omega : 1 ≤ p+1) A s

theorem shiftedExponentialCoefficient_step (p : ℕ) {A s : ℝ}
    (hA : 0 ≤ A) (hs : 0 ≤ s) :
    shiftedExponentialCoefficient (p+1) A s ≤
      (s+A/(p+1))*shiftedExponentialCoefficient p A s :=
  by simpa only [shiftedExponentialCoefficient,Nat.cast_add,Nat.cast_one] using
    tailMomentSeries_succ_le (by omega : 1 ≤ p+1) hA hs

end
end SingularValueBounds.KL
