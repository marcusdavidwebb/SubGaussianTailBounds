import SingularValueBounds.KL.Upper.GeneralMeanOfRow
import SingularValueBounds.KL.Upper.GeneralMeanRowTail
import SingularValueBounds.KL.Upper.GeneralMeanCellBridges

/-! Supplementary S1.6.3: the full general-K upper mean. Every remaining
numerical premise is a finite rational coefficient or rounding predicate. -/
open MeasureTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1800000

def GeneralMeanEntropyConditions : Prop :=
  (∀i : Fin 1330,GeneralMeanNumericalConditions (generalMeanRows i)) ∧
    GeneralMeanNumericalConditions generalMeanSmallRow

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- General upper drift with w=47/20, for every real K≥1 and every spectrum. -/
theorem upperShift_general_mean_of_certificates
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    (hrate : RateCertificateConditions) (hcells : GeneralMeanCellConditions)
    (hnum : GeneralMeanEntropyConditions)
    {X : Ω → ι → ℝ} {K L b : ℝ} (hiso : CentredIsotropic μ X)
    (hsg : SubGaussianMGF μ X K) (hK : 1≤K) (hKL : L=1+Real.log K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hcap : K^2*Matrix.trace R+(47/20)*K^2*L*frobenius R≤b) (hb : b<1) :
    Integrable (fun ω => (1-b)*upperShift R hR (X ω)) μ ∧
      (∫ω,(1-b)*upperShift R hR (X ω) ∂μ)≤1 := by
  have hK0 : 0<K := by linarith
  have hL : 1≤L := by rw [hKL];linarith [Real.log_nonneg hK]
  have hη := frobenius_pos hR
  have hFnorm : (frobenius R)^2=∑i,hR.isHermitian.eigenvalues i^2 := by
    rw [frobenius_eq_sqrt_trace_square hR.isHermitian,
      Real.sq_sqrt (trace_square_pos hR).le,real_spectral_trace_square hR.isHermitian]
  have hmax {r : GeneralMeanRow} (hk : spectralRatio R hR≤(r.khi:ℝ)) :
      ∀i,hR.isHermitian.eigenvalues i≤(r.khi:ℝ)*frobenius R := by
    intro i
    exact (div_le_iff₀ hη).mp ((upperNormalizedSpectrum_le_ratio hR i).trans hk)
  have hthird {r : GeneralMeanRow} (ha : upperComparisonShapeMean R hR≤(r.ahi:ℝ)) :
      (∑i,(hR.isHermitian.eigenvalues i/frobenius R)^3)≤(r.ahi:ℝ) := ha
  by_cases hk : spectralRatio R hR≤2/5
  · have hkrow : spectralRatio R hR≤(generalMeanSmallRow.khi:ℝ) := by
      simpa only [generalMeanSmallRow,Rat.cast_div,Rat.cast_ofNat] using hk
    have harow : upperComparisonShapeMean R hR≤(generalMeanSmallRow.ahi:ℝ) := by
      have hh := (upperComparisonShapeMean_ratio_bounds hR).2.trans hk
      simpa only [generalMeanSmallRow,Rat.cast_div,Rat.cast_ofNat] using hh
    apply upperShift_general_mean_of_row hnum.2 hiso hsg hK0 hL hKL hR hcap hb
      (general_mean_small_logdet hmajor hR hk)
    exact upperShift_tail_general_mean_row hnum.2 hsg hiso.measurable hK0 hR hL hcap hb
      hη hFnorm (hmax hkrow) (hthird harow) generalMeanSmallRow_rateCompatible hrate
  · obtain ⟨i,hi,hJ⟩ := general_mean_spectral_row hcells hmajor hnorm hR (le_of_not_ge hk)
    apply upperShift_general_mean_of_row (hnum.1 i) hiso hsg hK0 hL hKL hR hcap hb hJ
    exact upperShift_tail_general_mean_row (hnum.1 i) hsg hiso.measurable hK0 hR hL hcap hb
      hη hFnorm (hmax hi.2.2) (hthird hi.1.2) (hcells.2.2 i).2.2.2.2.1 hrate

end
end SingularValueBounds.KL
