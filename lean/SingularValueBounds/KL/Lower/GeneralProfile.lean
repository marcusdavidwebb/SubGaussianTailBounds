import SingularValueBounds.KL.Lower.ProfileCells
import SingularValueBounds.KL.Lower.PlateauCost

/-! General lower mixed-cost profile over every normalized spectral shape.
The only added premises are the explicit finite rational certificates. -/
open MeasureTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

def GeneralLowerCertificateConditions : Prop :=
  LowerCertificates.MomentCellConditions ∧ LowerCertificates.PlateauCertificateConditions ∧
    LowerCertificates.PlateauCostCertificateConditions

theorem generalLowerProfile_plateau {k : ℝ} (hk : (711/1000:ℝ) ≤ k) (hk1 : k ≤ 1) :
    generalLowerProfile k = 4137/1000 := by
  have hh := generalLowerPolynomial_mono (show (711/1000:ℝ) ∈ Icc 0 1 by norm_num)
    ⟨by linarith,hk1⟩ hk
  have hp : (4137/1000:ℝ) ≤ generalLowerPolynomial k := by
    norm_num [generalLowerPolynomial] at hh
    unfold generalLowerPolynomial
    linarith
  unfold generalLowerProfile
  exact min_eq_left (hp.trans (le_max_right _ _))

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Supplementary S1.4: the profile is valid for every spectral shape,
including the shared cell boundaries, the effective small-shape cap and both
concentrated-spectrum parameter families. -/
theorem normalized_general_lower_profile {X : Ω → ι → ℝ} {K : ℝ}
    (hdata : GeneralLowerCertificateConditions)
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R = 1) :
    ∃ B : Matrix ι ι ℝ, B.PosDef ∧
      (∀ x : ι → ℝ,x ⬝ᵥ (lowerWeight R *ᵥ x) ≤ (1+x ⬝ᵥ (B *ᵥ x))*lowerShift R hR x) ∧
      (∫ ω,quadraticForm (lowerWeight R) X ω*quadraticForm B X ω ∂μ)-K^2*Matrix.trace R ≤
        generalLowerProfile (spectralMaximum R hR.isHermitian)*K^2*logParameter K := by
  by_cases hk : spectralMaximum R hR.isHermitian ≤ 711/1000
  · exact ⟨lowerComparison0 R hR,lowerComparison0_posDef hR,
      lowerShift_comparison0 hR,normalized_lower_mixed_nonplateau hsg hiso hK hR hF hdata.1 hk⟩
  · have hk' : (711/1000:ℝ) ≤ spectralMaximum R hR.isHermitian := (lt_of_not_ge hk).le
    have hk1 : spectralMaximum R hR.isHermitian ≤ 1 := by simpa [hF] using spectralMaximum_le_frobenius hR.posSemidef
    rw [generalLowerProfile_plateau hk' hk1]
    exact normalized_lower_plateau hdata.2.1 hdata.2.2 hsg hiso hK hR hF (by linarith)

end
end SingularValueBounds.KL
