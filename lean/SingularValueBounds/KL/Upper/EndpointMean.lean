import SingularValueBounds.KL.Upper.EndpointMeanSurvival
import SingularValueBounds.KL.Upper.EndpointMeanCoverage
import SingularValueBounds.KL.Upper.MatrixMeanReduction

/-! # Endpoint upper mean, supplementary Lemma S1.9

The finite premises are exactly rational rounded-arithmetic and polynomial
certificates. The theorem covers every admissible spectrum, using all fifty
small-shape cells and all 837 clipped joint rectangles.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 2400000
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem upperShapeMean_ratio_bounds {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (spectralRatio R hR)^3≤upperComparisonShapeMean R hR ∧
      upperComparisonShapeMean R hR≤spectralRatio R hR := by
  let x := upperNormalizedSpectrum R hR
  have hx := upperNormalizedSpectrum_properties hR
  obtain ⟨top,_,ht⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hR.isHermitian.eigenvalues
  have he : x top=spectralRatio R hR := by
    dsimp [x,upperNormalizedSpectrum,spectralRatio,spectralMaximum]
    rw [←ht]
  constructor
  · rw [←he]
    exact Finset.single_le_sum (fun j hj => pow_nonneg (hx.1 j) 3) (Finset.mem_univ top)
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun j hj =>
      mul_le_mul_of_nonneg_right (upperNormalizedSpectrum_le_ratio hR j) (sq_nonneg (x j)))
    rw [←Finset.mul_sum,hx.2,mul_one] at hh
    convert! hh using 1
    unfold upperComparisonShapeMean normalizedUpperMean
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem upperShift_endpoint_entropy_cost (h : EndpointMeanCertificateConditions)
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    {X : Ω → ι → ℝ} (hsg : SubGaussianMGF μ X 1) (hm : Measurable X)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) {b : ℝ}
    (hcap : Matrix.trace R+(58/25 : ℝ)*frobenius R≤b) (hb : b<1)
    {W : Ω → ℝ} (hW : Measurable W) (hWi : Integrable W μ)
    (hW0 : ∀ω,0≤W ω) (hW1 : (∫ω,W ω ∂μ)=1)
    (hWY : ∀ω,W ω≤(1-b)*upperShift R hR (X ω))
    (hWE : Integrable (fun ω => W ω*Real.log (W ω)) μ) :
    (∫ω,W ω*Real.log (W ω) ∂μ)+upperComparisonMatrixLogdet R/2≤58/25 := by
  let k := spectralRatio R hR
  let a := upperComparisonShapeMean R hR
  let T := fun u : ℝ => μ.real {ω | u<W ω}
  have hk := spectralRatio_pos_le_one hR
  have ha := upperShapeMean_ratio_bounds hR
  have hη := frobenius_pos hR
  have htrace : Matrix.trace R≤b := by nlinarith
  have hnormR : (frobenius R)^2=∑j,hR.isHermitian.eigenvalues j^2 := by
    rw [frobenius_eq_sqrt_trace_square hR.isHermitian,
      Real.sq_sqrt (trace_square_pos hR).le,real_spectral_trace_square hR.isHermitian]
  have hMax : ∀j,hR.isHermitian.eigenvalues j≤k*frobenius R := by
    intro j
    exact (div_le_iff₀ hη).mp (upperNormalizedSpectrum_le_ratio hR j)
  have hT : Antitone T := by
    intro u v huv
    apply measureReal_mono _ (measure_ne_top μ _)
    intro ω hω
    exact huv.trans_lt hω
  have hT0 : ∀u,0≤T u := fun u => measureReal_nonneg
  have hT1 : ∀u,T u≤1 := fun u => measureReal_le_one
  have hInherit (u : ℝ) : T u≤μ.real {ω | u<(1-b)*upperShift R hR (X ω)} := by
    apply measureReal_mono _ (measure_ne_top μ _)
    intro ω hω
    exact hω.trans_le (hWY ω)
  have hTail : ∀u,0≤u → T u≤(31623/10000 : ℝ)*Real.exp (-((9/20 : ℝ)*u)) := by
    intro u hu
    have ht := upperShift_tail_family hsg hm (by norm_num : (0 : ℝ)<1) hR
      (by simpa using htrace) hb (by norm_num : (0 : ℝ)<9/10) (by norm_num : (9/10 : ℝ)<1) hu
    have hs0 : 0<Real.sqrt (1-(9/10 : ℝ)) := Real.sqrt_pos.mpr (by norm_num)
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ)≤1-(9/10 : ℝ))
    have hs : (Real.sqrt (1-(9/10 : ℝ)))⁻¹≤(31623/10000 : ℝ) := by
      rw [←one_div]
      apply (div_le_iff₀ hs0).2
      nlinarith
    have he : -(9/10*u/(2*(1 : ℝ)^2))=-(9/20*u) := by ring
    rw [he] at ht
    exact (hInherit u).trans (ht.trans (mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _)))
  have hEntropy (j0 : ℕ) (hj0 : 0<j0) :
      (∫ω,W ω*Real.log (W ω) ∂μ)≤Real.log ((j0 : ℝ)/200)+
        (∫u in Ioi ((j0 : ℝ)/200),entropyKernel ((j0 : ℝ)/200) u*T u) :=
    entropy_tail_integral hW hW0 hWi hW1 hWE (by positivity)
  by_cases hSmall : k≤(1/4 : ℝ)
  · obtain ⟨j,hj,hl,hr⟩ := finite_grid_covers_Ioc (fun j => (j : ℝ)/200) (n := 50) (a := k)
      (by norm_num; exact ⟨hk.1,hSmall⟩)
    let i : Fin 50 := ⟨j,hj⟩
    have hki : k≤(endpointSmallK i : ℝ) := by
      simpa only [endpointSmallK,i,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hr
    have hmarg : ∀j∈Finset.Ico (endpointSmallCutoff i) 8000,∀v : Fin 23,
        let q : ℚ := (endpointSmallQ v : ℚ)/100
        (j : ℚ)/200*endpointSmallK i*(q-1)≤58/25 →
        T ((j : ℝ)/200)≤Real.exp (-Real.log (1-(q : ℝ)*(endpointSmallK i : ℝ)^2)/
          (2*(endpointSmallK i : ℝ)^2)-(q : ℝ)*((j : ℝ)/200)/2) := by
      intro j hj v
      dsimp only
      intro hmarg
      have hp := h.smallPrefactors i v
      have hq0 : (0 : ℝ)<((endpointSmallQ v : ℚ)/100 : ℚ) := by
        dsimp [endpointSmallQ]
        push_cast
        positivity
      have hq2 : (((endpointSmallQ v : ℚ)/100 : ℚ) : ℝ)≤2 := by
        have hv : (v.val : ℝ)≤22 := by exact_mod_cast (by have := v.isLt; omega : v.val≤22)
        dsimp [endpointSmallQ]
        push_cast
        linarith
      have hki0 : (0 : ℝ)<endpointSmallK i := by exact_mod_cast hp.1
      have hgap : (((endpointSmallQ v : ℚ)/100 : ℚ) : ℝ)*(endpointSmallK i : ℝ)^2<1 := by
        have hh : (((endpointSmallQ v : ℚ)/100*endpointSmallK i^2 : ℚ) : ℝ)<1 := by exact_mod_cast hp.2.1
        simpa using hh
      have hmargin : (j : ℝ)/200*(endpointSmallK i : ℝ)*((((endpointSmallQ v : ℚ)/100 : ℚ) : ℝ)-1)≤58/25 := by
        have hh : ((((j : ℚ)/200*endpointSmallK i*((endpointSmallQ v : ℚ)/100-1)) : ℚ) : ℝ)≤((58/25 : ℚ) : ℝ) := by exact_mod_cast hmarg
        simpa using hh
      have hmMax (j : ι) : hR.isHermitian.eigenvalues j≤(endpointSmallK i : ℝ)*frobenius R :=
        (hMax j).trans (mul_le_mul_of_nonneg_right hki hη.le)
      have ht := upperShift_tail_margin hsg hm (by norm_num : (0 : ℝ)<1) hR
        (w := (58/25 : ℝ)) (L := 1) (by norm_num) (by norm_num)
        (by simpa using hcap) hb hq0 hq2 hki0 hgap hη hnormR hmMax
        (by positivity : (0 : ℝ)≤(j : ℝ)/200) (by simpa using hmargin)
      exact (hInherit _).trans (by simpa only [one_pow,mul_one] using ht)
    have hD := (hEntropy _ (h.smallCutoff i).1).trans
      (endpoint_mean_small_survival h i hT hT0 hT1 hTail hmarg)
    have hJ := upperComparisonMatrixLogdet_six hmajor 4 hR
      (by
        change a∈Icc (((0/1 : ℚ) : ℝ)) (((13/20 : ℚ) : ℝ))
        norm_num
        exact ⟨le_trans (pow_nonneg hk.1.le 3) ha.1,ha.2.trans (hSmall.trans (by norm_num))⟩)
      (by change k≤(((1/1 : ℚ) : ℝ)); norm_num; exact hk.2)
    norm_num [upperMajorantB] at hJ
    have hTotal : (endpointSmallTarget i : ℝ)+13/12-1/80≤58/25 := by
      have hh : ((endpointSmallTarget i+13/12-1/80 : ℚ) : ℝ)≤((58/25 : ℚ) : ℝ) := by exact_mod_cast h.smallTotal i
      simpa using hh
    linarith
  · obtain ⟨ki,ai,hact,hbox⟩ := endpoint_mean_joint_cover h
      (show k∈Icc (1/4 : ℝ) 1 from ⟨le_of_not_ge hSmall,hk.2⟩) ha
    have hJoint : ∀j∈Finset.Ico (endpointMeanCutoff ki ai) 8000,
        T ((j : ℝ)/200)≤upperJointPrefactor ((endpointMeanRate ki ai j : ℝ)/100) a k*
          Real.exp (-(((endpointMeanRate ki ai j : ℝ)/100)*((j : ℝ)/200)/2)) := by
      intro j hj
      let q : ℝ := (endpointMeanRate ki ai j : ℝ)/100
      have hr := h.jointRates ki ai hact j hj
      have hq : 0<q := by dsimp [q]; have := hr.1; positivity
      have hq2 : q≤2 := by
        dsimp [q]
        have hh : (endpointMeanRate ki ai j : ℝ)≤200 := by exact_mod_cast hr.2.1
        linarith
      have hk0 : (0 : ℝ)≤(endpointMeanBox ki ai).top := hk.1.le.trans hbox.2.2
      have hgapTop : q*((endpointMeanBox ki ai).top : ℝ)^2<1 := by
        have hh : ((((endpointMeanRate ki ai j : ℚ)/100)*(endpointMeanBox ki ai).top^2 : ℚ) : ℝ)<1 := by exact_mod_cast hr.2.2.1
        simpa [q] using hh
      have hgap : q*k^2<1 :=
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.1.le hbox.2.2 2) hq.le).trans_lt hgapTop
      have hmarginTop : (j : ℝ)/200*((endpointMeanBox ki ai).top : ℝ)*(q-1)≤58/25 := by
        have hh : ((((j : ℚ)/200*(endpointMeanBox ki ai).top*((endpointMeanRate ki ai j : ℚ)/100-1)) : ℚ) : ℝ)≤((58/25 : ℚ) : ℝ) := by exact_mod_cast hr.2.2.2
        simpa [q] using hh
      have hmargin : (j : ℝ)/200*k*(q-1)≤58/25 := by
        by_cases hq1 : 1≤q
        · have hh := mul_le_mul_of_nonneg_left hbox.2.2
            (mul_nonneg (by positivity : (0 : ℝ)≤(j : ℝ)/200) (sub_nonneg.mpr hq1))
          nlinarith
        · have hh : (j : ℝ)/200*k*(q-1)≤0 := mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (by positivity) hk.1.le) (by linarith)
          linarith
      have ht := upperShift_tail_joint hsg hm (by norm_num : (0 : ℝ)<1) hR
        (w := (58/25 : ℝ)) (L := 1) (by norm_num) (by norm_num)
        (by simpa using hcap) hb hq hq2 hk.1 hgap hη hnormR hMax
        (by positivity : (0 : ℝ)≤(j : ℝ)/200) (by simpa using hmargin)
      have he : upperJointCost q k (∑j,(hR.isHermitian.eigenvalues j/frobenius R)^3)=upperJointCost q k a := rfl
      rw [he] at ht
      apply (hInherit _).trans
      convert! ht using 1
      unfold upperJointPrefactor
      rw [←Real.exp_add]
      congr 1
      dsimp [q]
      ring
    have hD := (hEntropy _ (h.jointCutoff ki ai hact).1).trans
      (endpoint_mean_joint_survival h ki ai hact hbox hT hT0 hTail hJoint)
    exact endpoint_mean_polynomial_cost h hmajor hnorm hR ki ai hact hbox hD

/-- Lemma S1.9, with endpoint upper drift factor 58/25. -/
theorem upperShift_endpoint_mean (h : EndpointMeanCertificateConditions)
    (hmajor : MajorantCertificateConditions) (hnorm : NormDeterminantCertificateConditions)
    {X : Ω → ι → ℝ} (hiso : CentredIsotropic μ X) (hsg : SubGaussianMGF μ X 1)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) {b : ℝ}
    (hcap : Matrix.trace R+(58/25 : ℝ)*frobenius R≤b) (hb : b<1) :
    Integrable (fun ω => (1-b)*upperShift R hR (X ω)) μ ∧
      (∫ω,(1-b)*upperShift R hR (X ω) ∂μ)≤1 := by
  apply upperShift_mean_of_entropy_cost hiso hsg (by norm_num : (0 : ℝ)<1)
    (L := 1) (w := (58/25 : ℝ)) (by norm_num) (by norm_num) hR
    (by simpa using hcap) hb
  intro W hW hWi hW0 hW1 hWY hWE
  simpa using upperShift_endpoint_entropy_cost h hmajor hnorm hsg hiso.measurable hR hcap hb
    hW hWi hW0 hW1 hWY hWE

end
end SingularValueBounds.KL
