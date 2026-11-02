import SingularValueBounds.KL.Lower.EndpointProfiles
import SingularValueBounds.KL.Lower.EndpointSmallRemainder
import SingularValueBounds.KL.Lower.EndpointRatio
import SingularValueBounds.KL.Upper.ComparisonNormMatrices

/-! # Full endpoint lower mixed-cost cap

Supplementary `eq:app-K-one-uniform-cost` and the profile
`h(κ)=min {2κ,73/50}`. The additional hypotheses below are exclusively the
finite rational table and quartic certificate predicates.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ}

theorem endpoint_diagonal_table_cost (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (hcert : EndpointTableConditions)
    (i : Fin 2) (r : ι → ℝ) (top : ι)
    (hr : ∀ j, 0 ≤ r j ∧ r j ≤ r top) (h2 : spectralMoment r 2 = 1)
    (hk : r top ∈ Icc (endpointKLo i : ℝ) (endpointKHi i : ℝ))
    (hp : 3/20 ≤ endpointRestP r top) :
    (∫ ω, diagonalQuadratic (fun j => r j^2) X ω *
      diagonalQuadratic (fun j => endpointComparisonEigen (endpointTableA i (r top)) (endpointC i) (r j)) X ω ∂μ) -
      (∑ j, r j) ≤ 73/50 := by
  have hklo : 73/100 ≤ r top := by
    fin_cases i <;> norm_num [endpointKLo,endpointKHi] at hk <;> linarith [hk.1]
  have hkhi : r top ≤ 7/9 := by
    fin_cases i <;> norm_num [endpointKLo,endpointKHi] at hk <;> linarith [hk.2]
  have hk0 : 0 < r top := by linarith
  have hk1 : r top ≤ 1 := by linarith
  obtain ⟨hc,hA,hd,hprofile⟩ := endpoint_table_parameters i hk0.le hkhi
  have hf (j : ι) : 0 ≤ endpointComparisonEigen (endpointTableA i (r top)) (endpointC i) (r j) :=
    endpointComparisonEigen_nonneg_of_profile hk0.le (hr j).1 ((hr j).2.trans hk1) hprofile
  have hratio := endpoint_covariance_ratio r top hr h2 hklo hc hA hd hf hp
  have hOrd := (endpoint_diagonal_mixed_cost hsg hiso r (endpointTableA i (r top)) (endpointC i) h2 hf).trans
    (endpoint_ordinary_cost_young r (endpointTableA i (r top)) (endpointC i) h2
      (show (0 : ℝ) < endpointXi i by fin_cases i <;> norm_num [endpointXi]))
  have hRank := (endpoint_diagonal_rankone_cost hsg hiso r top (endpointTableA i (r top)) (endpointC i)
    h2 hk0 (lt_of_lt_of_le (sq_pos_of_pos hk0) hd) hf (by linarith) hratio.1 hratio.2).trans
      (endpoint_rankone_cost_young r top (endpointTableA i (r top)) (endpointC i) h2
        (show (0 : ℝ) < endpointChi i by fin_cases i <;> norm_num [endpointChi]))
  have hrest (j : ι) (hj : j ≠ top) : r j ∈ Icc (0 : ℝ) (7/10) := by
    refine ⟨(hr j).1, ?_⟩
    have he := normalized_other_square_le r top rfl h2 hj
    nlinarith only [he,hklo,(hr j).1]
  exact (le_min hOrd hRank).trans (endpoint_table_min_majorant_le hcert i r top h2 hk hrest)

theorem endpoint_diagonal_cap (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (htable : EndpointTableConditions) (hfar : EndpointFarConditions)
    (r : ι → ℝ) (top : ι) (hr : ∀ j, 0 ≤ r j ∧ r j ≤ r top)
    (h2 : spectralMoment r 2 = 1) (hk0 : 0 < r top) :
    ∃ A c : ℝ, LowerComparisonProfile (r top) A c ∧
      (∫ ω, diagonalQuadratic (fun j => r j^2) X ω *
        diagonalQuadratic (fun j => endpointComparisonEigen A c (r j)) X ω ∂μ) -
        (∑ j, r j) ≤ min (2*r top) (73/50) := by
  have hk1 : r top ≤ 1 := by
    have he := Finset.single_le_sum (s := Finset.univ) (fun j _ => sq_nonneg (r j)) (Finset.mem_univ top)
    change r top^2 ≤ spectralMoment r 2 at he
    rw [h2] at he
    nlinarith
  by_cases hlo : r top ≤ 73/100
  · refine ⟨r top,1,endpoint_canonical_profile _,?_⟩
    have hf (j : ι) : 0 ≤ endpointComparisonEigen (r top) 1 (r j) :=
      endpointComparisonEigen_nonneg_of_profile hk0.le (hr j).1 ((hr j).2.trans hk1)
        (endpoint_canonical_profile _)
    have hm := endpoint_diagonal_mixed_cost hsg hiso r (r top) 1 h2 hf
    have hc := endpoint_operator_cost r hk0.le hlo hr h2 top rfl
    have hmin : min (2*r top) (73/50) = 2*r top := min_eq_left (by linarith)
    rw [hmin]
    dsimp [endpointOrdinaryCost] at hm
    norm_num only [sub_self, zero_mul, add_zero, one_mul] at hm
    linarith
  have hmin : min (2*r top) (73/50) = 73/50 := min_eq_right (by linarith)
  rw [hmin]
  by_cases hnear : r top ≤ 7/9
  · by_cases hp : endpointRestP r top ≤ 3/20
    · refine ⟨r top,1,endpoint_canonical_profile _,?_⟩
      have hf (j : ι) : 0 ≤ endpointComparisonEigen (r top) 1 (r j) :=
        endpointComparisonEigen_nonneg_of_profile hk0.le (hr j).1 ((hr j).2.trans hk1)
          (endpoint_canonical_profile _)
      exact (endpoint_diagonal_mixed_cost hsg hiso r (r top) 1 h2 hf).trans
        (endpoint_small_remainder_cost r top (fun j => (hr j).1) h2 hnear hp).le
    · have hi : ∃ i : Fin 2, r top ∈ Icc (endpointKLo i : ℝ) (endpointKHi i : ℝ) := by
        by_cases hmid : r top ≤ 3/4
        · exact ⟨0, by norm_num [endpointKLo,endpointKHi]; constructor <;> linarith⟩
        · exact ⟨1, by norm_num [endpointKLo,endpointKHi]; constructor <;> linarith⟩
      obtain ⟨i,hik⟩ := hi
      refine ⟨endpointTableA i (r top),endpointC i,
        (endpoint_table_parameters i hk0.le hnear).2.2.2,?_⟩
      exact endpoint_diagonal_table_cost hsg hiso htable i r top hr h2 hik (by linarith)
  · have hp : LowerComparisonProfile (r top) (5/4) (7/4) :=
      endpoint_tangent_profile _ (by norm_num) (by norm_num) (by norm_num)
    refine ⟨5/4,7/4,hp,?_⟩
    have hf (j : ι) : 0 ≤ endpointComparisonEigen (5/4) (7/4) (r j) :=
      endpointComparisonEigen_nonneg_of_profile hk0.le (hr j).1 ((hr j).2.trans hk1) hp
    exact ((endpoint_diagonal_mixed_cost hsg hiso r (5/4) (7/4) h2 hf).trans
      (endpoint_ordinary_cost_young r (5/4) (7/4) h2 (by norm_num : (0 : ℝ) < 8/5))).trans
      (endpoint_far_spectral_bound hfar r top h2 ⟨by linarith,hk1⟩
        (fun j _ => ⟨(hr j).1,(hr j).2.trans hk1⟩))

variable [Nonempty ι]

/-- The complete endpoint mixed-cost cap, restored to every positive scale.
The comparison is simultaneous for all rows, including the zero row. -/
theorem endpoint_lower_mixed_cap_of_certificates (hsg : SubGaussianMGF μ X 1)
    (hiso : CentredIsotropic μ X) (htable : EndpointTableConditions) (hfar : EndpointFarConditions)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    ∃ B : Matrix ι ι ℝ, B.PosSemidef ∧
      (∀ x : ι → ℝ, x ⬝ᵥ (lowerWeight R *ᵥ x) ≤
        (1+x ⬝ᵥ (B *ᵥ x))*lowerShift R hR x) ∧
      (∫ ω, quadraticForm (lowerWeight R) X ω * quadraticForm B X ω ∂μ) ≤
        Matrix.trace R + frobenius R*min (2*spectralRatio R hR) (73/50) := by
  let U := hR.isHermitian.eigenvectorUnitary
  let XR := fun ω => star (U : Matrix ι ι ℝ) *ᵥ X ω
  let r := upperNormalizedSpectrum R hR
  have hη := frobenius_pos hR
  have hf := frobenius_sq R
  rw [← trace_square_eq_sum_sq hR.isHermitian] at hf
  obtain ⟨hr0,h2⟩ := upperNormalizedSpectrum_properties hR
  obtain ⟨top,_,ht⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty hR.isHermitian.eigenvalues
  have htop : r top = spectralRatio R hR := by
    dsimp [r,upperNormalizedSpectrum,spectralRatio,spectralMaximum]
    rw [ht.symm]
  have hr (j : ι) : 0 ≤ r j ∧ r j ≤ r top := by
    refine ⟨hr0 j, ?_⟩
    rw [htop]
    exact (div_le_div_iff_of_pos_right hη).mpr (eigenvalue_le_spectralMaximum hR.isHermitian j)
  have hrtop : 0 < r top := div_pos (hR.eigenvalues_pos top) hη
  obtain ⟨A,c,hprofile,hcost⟩ := endpoint_diagonal_cap (hsg.unitary U) (hiso.unitary U)
    htable hfar r top hr h2 hrtop
  have hprofile' : LowerComparisonProfile (spectralRatio R hR) A c := htop ▸ hprofile
  refine ⟨lowerComparison R A c, lowerComparison_posSemidef hR hprofile',
    (fun x => lowerShift_quadratic_comparison hR x hprofile'),?_⟩
  have hqP (ω : Ω) : quadraticForm (lowerWeight R) X ω =
      diagonalQuadratic (fun j => r j^2) XR ω := by
    dsimp only [lowerWeight,quadraticForm]
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    rw [← hf, real_spectral_square hR.isHermitian,quadratic_conjugate_diagonal]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [diagonalQuadratic,r,upperNormalizedSpectrum,XR,U]
    field_simp [hη.ne']
  have hqB (ω : Ω) : quadraticForm (lowerComparison R A c) X ω =
      frobenius R * diagonalQuadratic (fun j => endpointComparisonEigen A c (r j)) XR ω := by
    dsimp only [quadraticForm]
    rw [lowerComparison_spectral hR,quadratic_conjugate_diagonal]
    dsimp only [diagonalQuadratic]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [r,upperNormalizedSpectrum,XR,U,endpointComparisonEigen]
    rw [← hf]
    field_simp [hη.ne']
    ring
  have htrace : Matrix.trace R = frobenius R*(∑ j, r j) := by
    rw [real_spectral_trace hR.isHermitian,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [r,upperNormalizedSpectrum]
    field_simp [hη.ne']
  have hcost' := mul_le_mul_of_nonneg_left hcost hη.le
  rw [htop] at hcost'
  simp_rw [hqP,hqB]
  have hmul (ω : Ω) : diagonalQuadratic (fun j => r j^2) XR ω *
      (frobenius R*diagonalQuadratic (fun j => endpointComparisonEigen A c (r j)) XR ω) =
      frobenius R*(diagonalQuadratic (fun j => r j^2) XR ω *
        diagonalQuadratic (fun j => endpointComparisonEigen A c (r j)) XR ω) := by ring
  simp_rw [hmul]
  rw [integral_const_mul,htrace]
  linarith

end
end SingularValueBounds.KL
