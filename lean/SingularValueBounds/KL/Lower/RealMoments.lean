import SingularValueBounds.KL.Weighted.EntropyIntegration
import SingularValueBounds.KL.Lower.Shape

/-! # Real-power moments and entropy for the general lower profile (P11)
The entropy step is the printed Jensen inequality under density `T`, proved
directly by the scalar entropy tangent so zero weights need no logarithm.
-/
open MeasureTheory Set
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 800000

theorem rpow_mul_exp_neg_le {p y : ℝ} (hp : 0 < p) (hy : 0 ≤ y) :
    y^p*Real.exp (-y) ≤ p^p*Real.exp (-p) := by
  by_cases hy0 : y = 0
  · simp only [hy0,Real.zero_rpow hp.ne',zero_mul]
    positivity
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hyp hp)
  rw [Real.log_div hyp.ne' hp.ne'] at hlog
  have h := mul_le_mul_of_nonneg_left hlog hp.le
  have hcancel : p*(y/p-1) = y-p := by field_simp
  rw [hcancel] at h
  have he : p*Real.log y-y ≤ p*Real.log p-p := by nlinarith
  have hx (z : ℝ) (hz : 0 < z) : z^p*Real.exp (-z) = Real.exp (p*Real.log z-z) := by
    rw [Real.rpow_def_of_pos hz,← Real.exp_add]
    congr 1
    ring
  rw [hx y hyp,hx p hp]
  exact Real.exp_le_exp.mpr he

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem renyi_entropy_bound [IsProbabilityMeasure μ] {T : Ω → ℝ} {p : ℝ}
    (hT0 : ∀ ω, 0 ≤ T ω) (hT : Integrable T μ)
    (hMean : (∫ ω,T ω ∂μ) = 1)
    (hEntropy : Integrable (fun ω => T ω*Real.log (T ω)) μ)
    (hMoment : Integrable (fun ω => T ω^p) μ)
    (hMomentPos : 0 < ∫ ω,T ω^p ∂μ) (hp : 1 < p) :
    (∫ ω,T ω*Real.log (T ω) ∂μ) ≤ Real.log (∫ ω,T ω^p ∂μ)/(p-1) := by
  let M := ∫ ω,T ω^p ∂μ
  have hM : 0 < M := hMomentPos
  have hpoint (ω : Ω) : p*(T ω*Real.log (T ω))-T ω*Real.log M ≤
      T ω*Real.log (T ω)-T ω+T ω^p/M := by
    by_cases hz : T ω = 0
    · simp [hz,Real.zero_rpow (by linarith : p ≠ 0)]
    have ht : 0 < T ω := lt_of_le_of_ne (hT0 ω) (Ne.symm hz)
    have h := mul_le_mul_log_sub_add_exp (w := T ω) (z := p*Real.log (T ω)-Real.log M) (hT0 ω)
    have he : Real.exp (p*Real.log (T ω)-Real.log M) = T ω^p/M := by
      rw [Real.exp_sub,Real.exp_log hM,Real.rpow_def_of_pos ht]
      congr 2
      ring
    rw [he] at h
    nlinarith
  have hi := integral_mono ((hEntropy.const_mul p).sub (hT.mul_const (Real.log M)))
    ((hEntropy.sub hT).add (hMoment.div_const M)) hpoint
  change (∫ ω,p*(T ω*Real.log (T ω))-T ω*Real.log M ∂μ) ≤
    (∫ ω,T ω*Real.log (T ω)-T ω+T ω^p/M ∂μ) at hi
  have hright : (∫ ω,T ω*Real.log (T ω)-T ω+T ω^p/M ∂μ) =
      (∫ ω,T ω*Real.log (T ω) ∂μ) - 1 + (∫ ω,T ω^p ∂μ)/M := by
    have hs := integral_add (hEntropy.sub hT) (hMoment.div_const M)
    simp only [Pi.sub_apply] at hs
    rw [hs]
    change (∫ ω,T ω*Real.log (T ω)-T ω ∂μ) + (∫ ω,T ω^p/M ∂μ) = _
    rw [integral_sub hEntropy hT,integral_div,hMean]
  rw [hright,integral_sub (hEntropy.const_mul p) (hT.mul_const _),
    integral_const_mul,integral_mul_const,hMean] at hi
  have hMM : (∫ ω,T ω^p ∂μ)/M = 1 := div_self hM.ne'
  rw [hMM,one_mul] at hi
  apply (le_div_iff₀ (by linarith : 0 < p-1)).2
  dsimp [M] at hi
  nlinarith

theorem positive_real_moment_of_mean_one [IsProbabilityMeasure μ] {T : Ω → ℝ} {p : ℝ}
    (hT0 : ∀ ω, 0 ≤ T ω) (hMean : (∫ ω,T ω ∂μ) = 1)
    (hMoment : Integrable (fun ω => T ω^p) μ) (hp : 0 < p) :
    0 < ∫ ω,T ω^p ∂μ := by
  have hn : 0 ≤ ∫ ω,T ω^p ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (hT0 ω) _
  apply lt_of_le_of_ne hn
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg (fun ω => Real.rpow_nonneg (hT0 ω) p) hMoment).1 hz.symm
  have hzero : T =ᵐ[μ] 0 := by
    filter_upwards [he] with ω hω
    change T ω = 0
    have hω' : T ω^p = 0 := hω
    exact (Real.rpow_eq_zero (hT0 ω) hp.ne').1 hω'
  have hi := integral_congr_ae hzero
  have hi' : (∫ ω,T ω ∂μ) = 0 := by simpa only [Pi.zero_apply,integral_zero] using hi
  rw [hMean] at hi'
  norm_num at hi'

end
end SingularValueBounds.KL
