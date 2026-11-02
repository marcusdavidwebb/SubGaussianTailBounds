import SingularValueBounds.KL.Lower.GeneralParameters
import SingularValueBounds.KL.Lower.Moments

/-! Supplementary S1.3--S1.5: actual one-row lower Laplace estimates under
the two mixed caps, with all comparison and integrability inputs discharged. -/
open MeasureTheory
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1600000
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem lowerWeight_posSemidef {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (lowerWeight R).PosSemidef := by
  have hsq : (R^2).PosSemidef := by
    simpa only [hR.isHermitian.eq,pow_two] using Matrix.posSemidef_conjTranspose_mul_self R
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · change ((Matrix.trace (R^2))⁻¹ • R^2)ᴴ=(Matrix.trace (R^2))⁻¹ • R^2
    simp only [Matrix.conjTranspose_smul,star_trivial,hsq.isHermitian.eq]
  · intro x
    simpa only [lowerWeight,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul] using
      mul_nonneg (inv_nonneg.mpr (trace_square_pos hR).le) (hsq.dotProduct_mulVec_nonneg x)

theorem lowerWeight_trace_one {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix.trace (lowerWeight R)=1 := by
  rw [lowerWeight,Matrix.trace_smul,smul_eq_mul,inv_mul_cancel₀ (trace_square_pos hR).ne']

theorem lowerShift_general_laplace_of_certificates {X : Ω→ι→ℝ} {K : ℝ}
    (hdata : GeneralLowerCertificateConditions) (hsg : SubGaussianMGF μ X K)
    (hiso : CentredIsotropic μ X) (hK : 1≤K) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {b ℓ : ℝ}
    (hcap : K^2*Matrix.trace R+K^2*logParameter K*frobenius R*
      generalLowerProfile (spectralRatio R hR)≤b) (hℓ : 0≤ℓ) :
    Integrable (fun ω=>Real.exp (-ℓ*(1+b)*lowerShift R hR (X ω))) μ ∧
      (∫ω,Real.exp (-ℓ*(1+b)*lowerShift R hR (X ω)) ∂μ)≤
        Real.exp (-ℓ/(1+((499/100:ℝ)*K^2*logParameter K)*ℓ)) := by
  obtain ⟨B,hB,hcomp,hcost⟩ := general_lower_mixed_cap_of_certificates hdata hsg hiso hK hR
  have hpair : Measurable (fun ω=>((⟨R,hR⟩ : {Q : Matrix ι ι ℝ // Q.PosDef}),X ω)) :=
    measurable_const.prodMk hiso.measurable
  have hm0 := (SingularValueBounds.KL.measurable_lowerShift (ι:=ι)).comp hpair
  have hm : Measurable (fun ω=>lowerShift R hR (X ω)) := by
    exact hm0
  exact quadratic_lower_laplace_general (Δ:=fun ω=>lowerShift R hR (X ω)) (b:=b) (ℓ:=ℓ) hsg hiso hK (lowerWeight R) B
    (lowerWeight_posSemidef hR) hB (lowerWeight_trace_one hR) hm.aemeasurable
    (fun ω=>lowerShift_nonneg hR (X ω)) (hcost.trans hcap) (fun ω=>hcomp (X ω)) hℓ

theorem lowerShift_endpoint_laplace_of_certificates {X : Ω→ι→ℝ}
    (htable : Certificates.EndpointTableConditions) (hfar : Certificates.EndpointFarConditions)
    (hsg : SubGaussianMGF μ X 1) (hiso : CentredIsotropic μ X)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) {b ℓ : ℝ}
    (hcap : Matrix.trace R+frobenius R*min (2*spectralRatio R hR) (73/50)≤b)
    (hℓ : 0≤ℓ) :
    Integrable (fun ω=>Real.exp (-ℓ*(1+b)*lowerShift R hR (X ω))) μ ∧
      (∫ω,Real.exp (-ℓ*(1+b)*lowerShift R hR (X ω)) ∂μ)≤
        Real.exp (-ℓ/(1+(5/2:ℝ)*ℓ)) := by
  obtain ⟨B,hB,hcomp,hcost⟩ := endpoint_lower_mixed_cap_of_certificates hsg hiso htable hfar hR
  have hpair : Measurable (fun ω=>((⟨R,hR⟩ : {Q : Matrix ι ι ℝ // Q.PosDef}),X ω)) :=
    measurable_const.prodMk hiso.measurable
  have hm0 := (SingularValueBounds.KL.measurable_lowerShift (ι:=ι)).comp hpair
  have hm : Measurable (fun ω=>lowerShift R hR (X ω)) := by
    exact hm0
  exact quadratic_lower_laplace_one (Δ:=fun ω=>lowerShift R hR (X ω)) (b:=b) (ℓ:=ℓ) hsg hiso (lowerWeight R) B
    (lowerWeight_posSemidef hR) hB (lowerWeight_trace_one hR) hm.aemeasurable
    (fun ω=>lowerShift_nonneg hR (X ω)) (hcost.trans hcap) (fun ω=>hcomp (X ω)) hℓ

end
end SingularValueBounds.KL
