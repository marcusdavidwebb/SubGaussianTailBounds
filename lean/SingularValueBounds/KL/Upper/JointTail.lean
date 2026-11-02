import SingularValueBounds.KL.Upper.Margin
import SingularValueBounds.KL.Upper.Majorization

open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The joint shape/third-moment logarithmic determinant cost. -/
def upperJointCost (v k a : ℝ) : ℝ :=
  v+(a/k^3)*(-Real.log (1-v*k^2)-v*k^2)

/-- The joint cost is nonnegative, including the zero-deviation endpoint. -/
theorem upperJointCost_nonneg {v k a : ℝ} (hv : 0 ≤ v) (hk : 0 < k)
    (ha : 0 ≤ a) (hvk : v*k^2 < 1) : 0 ≤ upperJointCost v k a := by
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1-v*k^2 by linarith)
  have hrem : 0 ≤ -Real.log (1-v*k^2)-v*k^2 := by linarith
  exact add_nonneg hv (mul_nonneg (div_nonneg ha (by positivity)) hrem)

omit [DecidableEq ι] [Nonempty ι] in
/-- Exact normalization of the spectral probability vector by the Frobenius norm. -/
theorem upperTailWeight_normalize {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {h eta : ℝ} (hh : 0 ≤ h) (heta : 0 < eta) (i : ι) :
    upperTailWeight r h i = normalizedShiftWeight (fun j => r j/eta) (h*eta) i := by
  have hnum : ∀ j, (r j/eta)^2/(1+(h*eta)*(r j/eta)) =
      (r j^2/(1+h*r j))/eta^2 := by
    intro j
    have hd : 1+h*r j ≠ 0 := ne_of_gt (by have hj := hr j; positivity)
    have harg : 1+(h*eta)*(r j/eta) = 1+h*r j := by field_simp
    rw [harg]
    field_simp [heta.ne', hd]
  unfold upperTailWeight normalizedShiftWeight shiftedWeightNormalizer
  simp_rw [hnum]
  rw [← Finset.sum_div, div_div_div_cancel_right₀ (pow_ne_zero 2 heta.ne')]

omit [DecidableEq ι] in
/-- The complete joint determinant estimate at a margin-rescaled rate. -/
theorem upper_tail_spectral_joint {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    {h v theta k eta : ℝ} (hh : 0 ≤ h) (hv : 0 < v) (hv2 : v ≤ 2)
    (htheta : 1 ≤ theta) (hk : 0 < k) (hvk : v*k^2 < 1)
    (heta : 0 < eta) (hnorm : eta^2 = ∑ i, r i^2) (hmax : ∀ i, r i ≤ k*eta)
    (hmargin : ∀ i, h*r i*(v-1) ≤ theta-1) :
    (∀ i, 0 < 1-(v/theta)*upperTailEigenvalue r h i) ∧
      -(∑ i, Real.log (1-(v/theta)*upperTailEigenvalue r h i)) ≤
        (v/theta)*h*(∑ i, r i)+upperJointCost v k (∑ i, (r i/eta)^3) := by
  let ρ : ι → ℝ := fun i => r i/eta
  have hρ : ∀ i, 0 ≤ ρ i := fun i => div_nonneg (hr i).le heta.le
  have hρsum : (∑ i, ρ i^2) = 1 := by
    simp only [ρ, div_pow, ← Finset.sum_div, ← hnorm]
    exact div_self (pow_ne_zero 2 heta.ne')
  have hρmax : ∀ i, ρ i ≤ k := fun i => (div_le_iff₀ heta).2 (hmax i)
  have hp := normalizedShiftWeight_properties hρ hρsum (mul_nonneg hh heta.le) hk.le hρmax
  have hprops (i : ι) := upper_margin_rescaling hv hv2 htheta
    (mul_nonneg hh (hr i).le) (hmargin i)
  have hden : ∀ i, 0 < 1-(v/theta-1)*h*r i := by
    intro i
    simpa only [mul_assoc] using (hprops i).1
  have harg : ∀ i, upperTailSecondArgument r h (v/theta) i ≤
      v*normalizedShiftWeight ρ (h*eta) i := by
    intro i
    have h := mul_le_mul_of_nonneg_right (hprops i).2.1
      ((upperTailWeight_properties hr hh).1 i).le
    convert! h using 1
    · dsimp [upperTailSecondArgument]
      congr 2
      ring
    · rw [upperTailWeight_normalize hr hh heta]
  have hsecond : ∀ i, 0 < 1-upperTailSecondArgument r h (v/theta) i := by
    intro i
    have hshape := normalizedShiftWeight_le_shape hρ hρsum (mul_nonneg hh heta.le) hk.le hρmax i
    have h := mul_le_mul_of_nonneg_left hshape hv.le
    linarith [harg i]
  have hfirst : (∑ i, upperFactorF (v/theta) (h*r i)) ≤ (0 : ℝ) := by
    apply Finset.sum_nonpos
    intro i hi
    have hbound := (hprops i).2.2
    have hlog := Real.log_le_log (Real.exp_pos _) hbound
    rw [Real.log_exp, Real.log_div (hprops i).1.ne'
      (ne_of_gt (show 0 < 1+h*r i by have hi := hr i; positivity))] at hlog
    dsimp [upperFactorF]
    nlinarith
  have hsecondcost := normalizedShiftWeight_log_prefactor_of_le hρ hρsum
    (mul_nonneg hh heta.le) hk hρmax hv.le hvk harg
  have ht := upper_tail_logdet_of_costs hr hh hden hsecond hfirst hsecondcost
  simpa [upperJointCost, ρ] using ht

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Actual normalized joint tail under its finite spectral margin condition. -/
theorem upperShift_tail_joint_of_spectrum {X : Ω → ι → ℝ} {K b v k eta u : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hcap : K^2*Matrix.trace R ≤ b) (hb : b < 1)
    (hv : 0 < v) (hv2 : v ≤ 2) (hk : 0 < k) (hvk : v*k^2 < 1)
    (heta : 0 < eta) (hnorm : eta^2 = ∑ i, hR.isHermitian.eigenvalues i^2)
    (hmax : ∀ i, hR.isHermitian.eigenvalues i ≤ k*eta) (hu : 0 ≤ u)
    (hmargin : ∀ i, u*hR.isHermitian.eigenvalues i*(v-1) ≤ b-K^2*Matrix.trace R) :
    μ.real {ω | u < (1-b)*upperShift R hR (X ω)} ≤
      Real.exp (upperJointCost v k (∑ i, (hR.isHermitian.eigenvalues i/eta)^3)/2-v*u/(2*K^2)) := by
  have hK2 : 0 < K^2 := sq_pos_of_pos hK
  have hb0 : 0 < 1-b := by linarith
  have hcap1 : 0 < 1-K^2*Matrix.trace R := by linarith
  rcases hu.eq_or_lt with rfl | hu
  · have ha : 0 ≤ ∑ i, (hR.isHermitian.eigenvalues i/eta)^3 :=
      Finset.sum_nonneg fun i hi => pow_nonneg (div_nonneg (hR.eigenvalues_pos i).le heta.le) _
    have hcost := upperJointCost_nonneg hv.le hk ha hvk
    have he : 1 ≤ Real.exp (upperJointCost v k (∑ i, (hR.isHermitian.eigenvalues i/eta)^3)/2) :=
      Real.one_le_exp_iff.mpr (by positivity)
    simpa using (measureReal_le_one (μ := μ)).trans he
  let h := u/(1-b)
  let theta := (1-K^2*Matrix.trace R)/(1-b)
  have hh : 0 < h := div_pos hu hb0
  have ht0 : 0 < theta := div_pos hcap1 hb0
  have ht1 : 1 ≤ theta := (one_le_div hb0).2 (by linarith)
  have hmarg (i : ι) : h*hR.isHermitian.eigenvalues i*(v-1) ≤ theta-1 := by
    have ht := div_le_div_of_nonneg_right (hmargin i) hb0.le
    convert! ht using 1 <;> dsimp [h, theta] <;> field_simp [hb0.ne'] <;> ring
  obtain ⟨hgap, hlog⟩ := upper_tail_spectral_joint hR.eigenvalues_pos hh.le hv hv2 ht1 hk hvk heta hnorm hmax hmarg
  have hlog' : -(∑ i, Real.log (1-(v/theta)*upperTailEigenvalue hR.isHermitian.eigenvalues h i)) ≤
      (v/theta)*h*Matrix.trace R+upperJointCost v k (∑ i, (hR.isHermitian.eigenvalues i/eta)^3) := by
    rwa [real_spectral_trace hR.isHermitian]
  have ht := upperShift_tail_of_spectral_logdet hsg hm hK hR hh (div_pos hv ht0) hgap hlog'
  have hevent : {ω | u < (1-b)*upperShift R hR (X ω)} =
      {ω | h < upperShift R hR (X ω)} := by
    ext ω
    change u < (1-b)*upperShift R hR (X ω) ↔ u/(1-b) < upperShift R hR (X ω)
    rw [div_lt_iff₀ hb0, mul_comm]
  rw [hevent]
  convert! ht using 1
  congr 1
  dsimp [h, theta]
  field_simp [hb0.ne', hcap1.ne', hK.ne']

/-- Supplementary joint prefactor tail with the cap supplying the margin. -/
theorem upperShift_tail_joint {X : Ω → ι → ℝ} {K L w b v k eta u : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hcap : K^2*Matrix.trace R+w*K^2*L*eta ≤ b) (hb : b < 1)
    (hv : 0 < v) (hv2 : v ≤ 2) (hk : 0 < k) (hvk : v*k^2 < 1)
    (heta : 0 < eta) (hnorm : eta^2 = ∑ i, hR.isHermitian.eigenvalues i^2)
    (hmax : ∀ i, hR.isHermitian.eigenvalues i ≤ k*eta) (hu : 0 ≤ u)
    (hmargin : u*k*(v-1) ≤ w*K^2*L) :
    μ.real {ω | u < (1-b)*upperShift R hR (X ω)} ≤
      Real.exp (upperJointCost v k (∑ i, (hR.isHermitian.eigenvalues i/eta)^3)/2-v*u/(2*K^2)) := by
  have hcost : 0 ≤ w*K^2*L*eta := by positivity
  apply upperShift_tail_joint_of_spectrum hsg hm hK hR (by linarith) hb hv hv2 hk hvk heta hnorm hmax hu
  intro i
  by_cases hv1 : 1 ≤ v
  · have hm := mul_le_mul_of_nonneg_right (hmax i) (mul_nonneg hu (sub_nonneg.mpr hv1))
    have hc := mul_le_mul_of_nonneg_right hmargin heta.le
    nlinarith
  · have hprod : u*hR.isHermitian.eigenvalues i*(v-1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu (hR.eigenvalues_pos i).le) (by linarith)
    linarith

end
end SingularValueBounds.KL
