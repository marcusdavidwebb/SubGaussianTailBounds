import SingularValueBounds.KL.Upper.EndpointMatrix

/-! # The explicit auxiliary Gaussian majorant (supplementary S1.6.4)

The second coefficient retains the spectral square mass. Higher coefficient
bounds are Jensen estimates for this Gaussian variable alone.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def endpointGaussian (x : ι → ℝ) (g : ι → ℝ) : ℝ := ∑j,x j^2*(g j)^2

theorem spectralSquareMass_monotone :
    MonotoneOn (fun k : ℝ => k^4+(1-k^2)^2) (Icc (9/10 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · fun_prop
  · fun_prop
  · intro k hk
    have hk' : k∈Icc (9/10 : ℝ) 1 := interior_subset hk
    have hd : HasDerivAt (fun k : ℝ => k^4+(1-k^2)^2) (4*k*(2*k^2-1)) k := by
      convert! ((hasDerivAt_id k).pow 4).add
        (((hasDerivAt_const k 1).sub ((hasDerivAt_id k).pow 2)).pow 2) using 1 <;>
        simp only [Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring
    rw [hd.deriv]
    have hk0 : 0≤k := by linarith [hk'.1]
    have hh : 0≤2*k^2-1 := by nlinarith [hk'.1]
    positivity

theorem endpoint_spectral_fourth_mass (i : Fin 3) {x : ι → ℝ}
    (h2 : ∑j,x j^2=1) (top : ι)
    (hκ : x top∈Icc (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    (∑j,x j^4)≤(endpointRareRow i).zeta := by
  have he2 : (∑j∈Finset.univ.erase top,x j^2)=1-(x top)^2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ top),h2]
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ.erase top)
    (f := fun j => x j^2) (fun j hj => sq_nonneg (x j))
  have hePow (j : ι) : (x j^2)^2=x j^4 := by ring
  simp_rw [hePow] at hs
  rw [he2] at hs
  have he4 := Finset.sum_erase_add Finset.univ (fun j => x j^4) (Finset.mem_univ top)
  have hLo : (9/10 : ℝ)≤(endpointSpectralRow i).lo := by fin_cases i <;> norm_num [endpointSpectralRow]
  have hHi : (endpointSpectralRow i).hi≤1 := by fin_cases i <;> norm_num [endpointSpectralRow]
  have hMon := spectralSquareMass_monotone ⟨hLo.trans hκ.1,hκ.2.trans hHi⟩
    ⟨hLo.trans (hκ.1.trans hκ.2),hHi⟩ hκ.2
  have hζ : (endpointRareRow i).zeta=(endpointSpectralRow i).hi^4+
      (1-(endpointSpectralRow i).hi^2)^2 := by fin_cases i <;> norm_num [endpointRareRow,endpointSpectralRow]
  rw [hζ]
  dsimp only at hMon he4
  linarith

theorem endpointGaussian_mean {x : ι → ℝ} (h2 : ∑j,x j^2=1) :
    (∫g,endpointGaussian x g ∂standardGaussian ι)=1 := by
  unfold endpointGaussian
  have hInt (j : ι) : Integrable (fun g : ι → ℝ => (g j)^2) (standardGaussian ι) := by
    simpa only [pow_one] using standardGaussian_coordinate_even_integrable j 1
  rw [integral_finsetSum _ (fun j hj =>
    (hInt j).const_mul (x j^2))]
  simp only [integral_const_mul]
  have hj (j : ι) : (∫g : ι → ℝ,(g j)^2 ∂standardGaussian ι)=1 := by
    simpa [gaussianSquareCoefficient] using standardGaussian_coordinate_even_moment j 1
  simp_rw [hj,mul_one]
  exact h2

theorem endpointGaussian_second (i : Fin 3) {x : ι → ℝ}
    (h2 : ∑j,x j^2=1) (top : ι)
    (hκ : x top∈Icc (endpointSpectralRow i).lo (endpointSpectralRow i).hi) :
    (∫g,endpointGaussian x g^2 ∂standardGaussian ι)/2≤1/2+(endpointRareRow i).zeta := by
  change (∫g,(∑j,x j^2*(g j)^2)^2 ∂standardGaussian ι)/2≤_
  rw [standardGaussian_quadratic_second,h2]
  have hh := endpoint_spectral_fourth_mass i h2 top hκ
  have he : (∑j,(x j^2)^2)=∑j,x j^4 := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  linarith

variable [Nonempty ι]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Whole Gaussian MGF comparison for the actual square-weight quadratic
form, including integrability. This supplies no original-variable moment
coefficient comparison. -/
theorem upperSquareWeight_gaussian_mgf {X : Ω → ι → ℝ}
    (hsg : SubGaussianMGF μ X 1) (hm : Measurable X)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) {t : ℝ} (ht : 0≤t) (ht4 : 4*t<1) :
    Integrable (fun ω => Real.exp (t*quadraticForm (upperSquareWeight R) X ω)) μ ∧
      (∫ω,Real.exp (t*quadraticForm (upperSquareWeight R) X ω) ∂μ)≤
        ∫g,Real.exp (t*endpointGaussian (upperNormalizedSpectrum R hR) g) ∂standardGaussian ι := by
  let x := upperNormalizedSpectrum R hR
  let w : ι → ℝ := fun j => x j^2
  have hx := upperNormalizedSpectrum_properties hR
  have hw : ∀j,0≤w j := fun j => sq_nonneg _
  have hw1 : ∀j,w j≤1 := by
    intro j
    have hs := Finset.single_le_sum (s := Finset.univ) (fun k hk => sq_nonneg (x k)) (Finset.mem_univ j)
    rwa [hx.2] at hs
  have hgap : ∀j,0<1-2*(1 : ℝ)^2*t*w j := by
    intro j
    have hh := mul_le_mul_of_nonneg_left (hw1 j) ht
    nlinarith
  have hb := unitary_quadratic_exponential_bound hsg hm hR.isHermitian.eigenvectorUnitary w hw t ht hgap
  have hs : upperSquareWeight R=
      (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)*Matrix.diagonal w*
        star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
    have hwEq : upperWeight hR.isHermitian.eigenvalues=w :=
      funext (fun j => upperWeight_eq_normalized_square hR j)
    rw [upperSquareWeight_spectral hR,hwEq]
  rw [← hs] at hb
  have hG : (∫g,Real.exp (t*endpointGaussian x g) ∂standardGaussian ι)=
      ∏j,(Real.sqrt (1-2*t*w j))⁻¹ := by
    simp only [endpointGaussian,Finset.mul_sum]
    simpa only [w,mul_assoc] using
      standardGaussian_integral_exp_sum_sq (fun j => t*w j)
        (by intro j; simpa [mul_assoc] using hgap j)
  norm_num only [one_pow,mul_one] at hb
  rw [hG]
  exact hb

end
end SingularValueBounds.KL
