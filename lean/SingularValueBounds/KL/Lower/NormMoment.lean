import SingularValueBounds.KL.Lower.LogMGF
import SingularValueBounds.KL.Lower.MomentRatio
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The trace-one quadratic exponential bound, retaining an arbitrary
spectral upper cap, and the higher-moment entropy reduction. -/
open MeasureTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1000000

theorem neg_log_secant {x cap t : ℝ} (hcap : 0 < cap) (hx : x ∈ Icc (0:ℝ) cap)
    (ht : 0 ≤ t) (htcap : t*cap < 1) :
    -Real.log (1-t*x) ≤ (x/cap)*(-Real.log (1-t*cap)) := by
  have ha : 0 ≤ 1-x/cap := sub_nonneg.mpr ((div_le_one hcap).2 hx.2)
  have hb : 0 ≤ x/cap := div_nonneg hx.1 hcap.le
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (by norm_num : (0:ℝ) < 1)
    (by linarith : 0 < 1-t*cap) ha hb (show 1-x/cap+x/cap = (1:ℝ) by ring)
  have hid : (1-x/cap)*(1:ℝ)+(x/cap)*(1-t*cap) = 1-t*x := by field_simp; ring
  simp only [smul_eq_mul,Real.log_one,mul_zero,zero_add,hid] at h
  nlinarith

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem unitary_trace_one_exponential {X : Ω → ι → ℝ} {K scale cap : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    (U : Matrix.unitaryGroup ι ℝ) (b : ι → ℝ) (hb : ∀ i,0 ≤ b i)
    (hsum : (∑ i,b i) = 1) (hcap : 0 < cap) (hbound : ∀ i,b i ≤ cap)
    (hscale : 0 < scale) (hgap : 2*cap < scale) :
    Integrable (fun ω => Real.exp (quadraticForm
      ((U:Matrix ι ι ℝ)*Matrix.diagonal b*star (U:Matrix ι ι ℝ)) X ω/(K^2*scale))) μ ∧
    (∫ ω,Real.exp (quadraticForm
      ((U:Matrix ι ι ℝ)*Matrix.diagonal b*star (U:Matrix ι ι ℝ)) X ω/(K^2*scale)) ∂μ) ≤
      Real.exp (-Real.log (1-2*cap/scale)/(2*cap)) := by
  let t := 1/(K^2*scale)
  have hfac : 2*K^2*t = 2/scale := by dsimp [t]; field_simp <;> ring
  have hg : (2/scale)*cap < 1 := by rw [div_mul_eq_mul_div]; exact (div_lt_one hscale).2 hgap
  have hf (i : ι) : 0 < 1-2*K^2*t*b i := by
    rw [hfac]
    nlinarith [mul_le_mul_of_nonneg_left (hbound i) (by positivity : 0 ≤ 2/scale)]
  have h := unitary_quadratic_exponential_bound hsg hm U b hb t (by dsimp [t]; positivity) hf
  have hlog := Real.log_le_log (integral_exp_pos h.1) h.2
  rw [Real.log_prod Finset.univ _ (fun i _ => (inv_pos.mpr (Real.sqrt_pos.2 (hf i))).ne')] at hlog
  simp_rw [Real.log_inv,Real.log_sqrt (hf _).le,hfac] at hlog
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    neg_log_secant hcap ⟨hb i,hbound i⟩ (by positivity : 0 ≤ 2/scale) hg)
  rw [← Finset.sum_mul,← Finset.sum_div,hsum] at hs
  have hcoeff : -Real.log (1-2*cap/scale)/(2*cap) =
      ((1/cap)*(-Real.log (1-(2/scale)*cap)))/2 := by
    rw [div_mul_eq_mul_div]
    ring
  have hl : Real.log (∫ ω,Real.exp (t*quadraticForm
      ((U:Matrix ι ι ℝ)*Matrix.diagonal b*star (U:Matrix ι ι ℝ)) X ω) ∂μ) ≤
      -Real.log (1-2*cap/scale)/(2*cap) := by
    rw [hcoeff]
    have hid : (∑ i,-(Real.log (1-(2/scale)*b i)/2)) =
        (∑ i,-Real.log (1-(2/scale)*b i))/2 := by
      rw [Finset.sum_div]
      simp only [neg_div]
    rw [hid] at hlog
    linarith
  have hbnd := (Real.log_le_iff_le_exp (integral_exp_pos h.1)).1 hl
  simpa only [t,one_div,← div_eq_inv_mul] using And.intro h.1 hbnd

theorem normalized_weight_exponential {X : Ω → ι → ℝ} {K scale k : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R = 1)
    (hk : 0 < k) (hbound : spectralMaximum R hR.isHermitian ≤ k)
    (hscale : 0 < scale) (hgap : 2*k^2 < scale) :
    Integrable (fun ω => Real.exp (quadraticForm (lowerWeight R) X ω/(K^2*scale))) μ ∧
    (∫ ω,Real.exp (quadraticForm (lowerWeight R) X ω/(K^2*scale)) ∂μ) ≤
      Real.exp (-Real.log (1-2*k^2/scale)/(2*k^2)) := by
  have hs : (∑ i,hR.isHermitian.eigenvalues i^2) = 1 := by
    rw [← real_spectral_trace_square hR.isHermitian,normalized_trace_square hR hF]
  have hw : lowerWeight R = R^2 := by simp [lowerWeight,normalized_trace_square hR hF]
  rw [hw,real_spectral_square hR.isHermitian]
  exact unitary_trace_one_exponential hsg hm hK hR.isHermitian.eigenvectorUnitary
    (fun i => hR.isHermitian.eigenvalues i^2) (fun i => sq_nonneg _) hs (sq_pos_of_pos hk)
    (fun i => pow_le_pow_left₀ (hR.eigenvalues_pos i).le
      ((eigenvalue_le_spectralMaximum hR.isHermitian i).trans hbound) 2) hscale hgap

end
end SingularValueBounds.KL
