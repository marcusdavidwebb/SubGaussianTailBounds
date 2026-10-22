import SingularValueBounds.KL.Upper.RateAnalysis

/-! # The complete extended upper tail (supplementary Lemma S1.7)
This module combines the analytic rate correction, the determinant comparison,
and Gaussian Chernoff. The only scalar input is the whole-domain correction
bound furnished by `upper_rate_of_certificates` from finite arithmetic. -/
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace SingularValueBounds.KL
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Supplementary `eq:app-upper-extended-tail`, including every intermediate
rate `1<v0≤v` needed above the breakpoint of the two-piece tail. -/
theorem upperShift_tail_extended {X : Ω → ι → ℝ} {K L w b v v0 C k eta u : ℝ}
    (hsg : SubGaussianMGF μ X K) (hm : Measurable X) (hK : 0 < K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hcap : K^2*Matrix.trace R+w*K^2*L*eta ≤ b) (hb : b < 1)
    (hv0 : 1 < v0) (hvv : v0 ≤ v) (hk : 0 < k) (hvk : v*k^2 < 1) (hC : 0 ≤ C)
    (hbound : ∀ theta ∈ Icc (1:ℝ) v,upperRateF v theta ≤ C)
    (heta : 0 < eta) (hnorm : eta^2 = ∑ i,hR.isHermitian.eigenvalues i^2)
    (hmax : ∀ i,hR.isHermitian.eigenvalues i ≤ k*eta) (hu : 0 ≤ u)
    (hmargin : u*k*(v0-1) ≤ w*K^2*L) :
    μ.real {ω | u < (1-b)*upperShift R hR (X ω)} ≤
      Real.exp (-Real.log (1-v*k^2)/(2*k^2)+C/(2*k^2)-v0*u/(2*K^2)) := by
  have hK2 : 0 < K^2 := sq_pos_of_pos hK
  have hv : 0 < v := by linarith
  have hb0 : 0 < 1-b := by linarith
  have hcost : 0 ≤ w*K^2*L*eta := by positivity
  have hcap0 : K^2*Matrix.trace R ≤ b := by linarith
  have hcap1 : 0 < 1-K^2*Matrix.trace R := by linarith
  rcases hu.eq_or_lt with rfl | hu
  · have hlog : Real.log (1-v*k^2) ≤ 0 :=
      Real.log_nonpos (by linarith) (by nlinarith [mul_nonneg hv.le (sq_nonneg k)])
    have he : 1 ≤ Real.exp (-Real.log (1-v*k^2)/(2*k^2)+C/(2*k^2)) :=
      Real.one_le_exp_iff.2 (add_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity))
    simpa using (measureReal_le_one (μ := μ)).trans he
  let r := hR.isHermitian.eigenvalues
  let h := u/(1-b)
  let theta := (1-K^2*Matrix.trace R)/(1-b)
  let q := v0/theta
  have hr : ∀ i,0 < r i := hR.eigenvalues_pos
  have hh : 0 < h := div_pos hu hb0
  have ht0 : 0 < theta := div_pos hcap1 hb0
  have ht1 : 1 ≤ theta := (one_le_div hb0).2 (by linarith)
  have hq : 0 < q := div_pos (by linarith) ht0
  have hnormmargin : h*eta*k*(v0-1) ≤ theta-1 := by
    have hm := mul_le_mul_of_nonneg_right hmargin heta.le
    have hm0 : u*eta*k*(v0-1) ≤ b-K^2*Matrix.trace R := by nlinarith
    have ht := div_le_div_of_nonneg_right hm0 hb0.le
    convert ht using 1 <;> dsimp [h,theta] <;> field_simp only [hb0.ne'] <;> ring
  have hps := upperTailWeight_le_normalized hr hh.le heta hnorm hmax
  have hspec : (∀ i,0 < 1-q*upperTailEigenvalue r h i) ∧
      -(∑ i,Real.log (1-q*upperTailEigenvalue r h i)) ≤
        q*h*(∑ i,r i)+C/k^2-Real.log (1-v*k^2)/k^2 := by
    by_cases hq1 : q ≤ 1
    · have hden (i : ι) : 0 < 1-(q-1)*h*r i := by
        have hnon := mul_nonpos_of_nonpos_of_nonneg (show q-1 ≤ 0 by linarith)
          (mul_nonneg hh.le (hr i).le)
        nlinarith
      have hfirst (i : ι) : Real.exp (-(q*h*r i)) ≤ (1-(q-1)*h*r i)/(1+h*r i) := by
        have he := upper_first_factor_exp_rate (hr i) hh.le hq.le hq1
        convert he using 1 <;> ring
      have hrate (i : ι) : q/(1-(q-1)*h*r i) ≤ v := by
        have hd : 1 ≤ 1-(q-1)*h*r i := by
          have hnon := mul_nonpos_of_nonpos_of_nonneg (show q-1 ≤ 0 by linarith)
            (mul_nonneg hh.le (hr i).le)
          nlinarith
        have hqv0 : q ≤ v0 := div_le_self (by linarith) ht1
        exact (div_le_self hq.le hd).trans (hqv0.trans hvv)
      obtain ⟨hgap,hdet⟩ := upper_tail_spectral_shape_of_factors hr hh.le hq hv
        (sq_pos_of_pos hk) hps hvk hden hfirst hrate
      have hl := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hdet
      rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp,
        Real.log_prod _ _ (fun i _ => (hgap i).ne')] at hl
      refine ⟨hgap,?_⟩
      have hCf : 0 ≤ C/k^2 := div_nonneg hC (sq_nonneg k)
      linarith
    · have hq1 : 1 < q := lt_of_not_ge hq1
      have htheta : 1 < theta := by
        have hpos : 0 < h*eta*k*(v0-1) :=
          mul_pos (mul_pos (mul_pos hh heta) hk) (by linarith)
        linarith
      have hthetav : theta < v0 := (one_lt_div ht0).1 hq1
      have hFc := upperRateF_envelope hv0 hvv hbound ⟨ht1,hthetav.le⟩
      exact upper_extended_spectral_logdet hr hh heta hk hnorm hmax hv0 hvv hvk
        htheta hthetav hC hnormmargin hFc
  have hlog : -(∑ i,Real.log (1-q*upperTailEigenvalue hR.isHermitian.eigenvalues h i)) ≤
      q*h*Matrix.trace R+(C/k^2-Real.log (1-v*k^2)/k^2) := by
    rw [real_spectral_trace hR.isHermitian]
    exact (by convert hspec.2 using 1 <;> ring)
  have ht := upperShift_tail_of_spectral_logdet hsg hm hK hR hh hq hspec.1 hlog
  have hevent : {ω | u < (1-b)*upperShift R hR (X ω)} =
      {ω | h < upperShift R hR (X ω)} := by
    ext ω
    change u < (1-b)*upperShift R hR (X ω) ↔ u/(1-b) < upperShift R hR (X ω)
    rw [div_lt_iff₀ hb0,mul_comm]
  rw [hevent]
  convert ht using 1
  congr 1
  dsimp [q,h,theta]
  field_simp only [hb0.ne',hcap1.ne',hK.ne']
  ring
end
end SingularValueBounds.KL
