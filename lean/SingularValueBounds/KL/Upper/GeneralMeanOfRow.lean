import SingularValueBounds.KL.Upper.GeneralMeanTailEntropy
import SingularValueBounds.KL.Upper.MatrixMeanReduction

open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1600000

theorem GeneralMeanTailProfile.mono {T U : ℝ → ℝ} {A q c s K L : ℝ}
    (h : GeneralMeanTailProfile U A q c s K L) (hTU : ∀u,T u≤U u) :
    GeneralMeanTailProfile T A q c s K L := by
  unfold GeneralMeanTailProfile at h ⊢
  split_ifs at h ⊢ with hq
  · exact ⟨fun u hu hv => (hTU u).trans (h.1 u hu hv),
      fun u hu => (hTU u).trans (h.2 u hu)⟩
  · exact fun u hu => (hTU u).trans (h u hu)

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A selected, fully certified spectral row gives the actual upper-shift mean. -/
theorem upperShift_general_mean_of_row {r : GeneralMeanRow}
    (hnum : GeneralMeanNumericalConditions r)
    {X : Ω → ι → ℝ} {K L b : ℝ} (hiso : CentredIsotropic μ X)
    (hsg : SubGaussianMGF μ X K) (hK : 0<K) (hL : 1≤L)
    (hKL : L=1+Real.log K) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (hcap : K^2*Matrix.trace R+(47/20)*K^2*L*frobenius R≤b) (hb : b<1)
    (hJ : upperComparisonMatrixLogdet R≤(r.J:ℝ))
    (hTail : GeneralMeanTailProfile
      (fun u => μ.real {ω | u<(1-b)*upperShift R hR (X ω)})
      r.prefactor r.q r.c r.cutoff K L) :
    Integrable (fun ω => (1-b)*upperShift R hR (X ω)) μ ∧
      (∫ω,(1-b)*upperShift R hR (X ω) ∂μ)≤1 := by
  have hLp : 0≤L := by linarith
  apply upperShift_mean_of_entropy_cost hiso hsg hK hLp (by norm_num : (0:ℝ)≤47/20)
    hR hcap hb
  intro W hW hWi hW0 hMean hWY hWE
  have hTrace : K^2*Matrix.trace R≤b := by
    have hη := (frobenius_pos hR).le
    nlinarith [mul_nonneg (sq_nonneg K) hLp]
  have hDom : ∀u,μ.real {ω | u<W ω}≤μ.real {ω | u<(1-b)*upperShift R hR (X ω)} := by
    intro u
    exact measureReal_mono (fun ω hω => lt_of_lt_of_le hω (hWY ω)) (measure_ne_top μ _)
  have hGlobal : ∀u,0≤u → μ.real {ω | u<W ω}≤
      (Real.sqrt (1-(1/2:ℝ)))⁻¹*Real.exp (-((1/(4*K^2))*u)) := by
    intro u hu
    have ht := upperShift_tail_family hsg hiso.measurable hK hR hTrace hb
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) hu
    apply (hDom u).trans
    convert ht using 1 <;> congr 2 <;> ring
  have hCost := generalMean_entropy_cost_of_row hnum hK hL hKL hW hWi hW0 hMean hWE
    (by positivity : 0≤(Real.sqrt (1-(1/2:ℝ)))⁻¹)
    (by positivity : 0<1/(4*K^2)) hGlobal (hTail.mono hDom)
  linarith

end
end SingularValueBounds.KL
