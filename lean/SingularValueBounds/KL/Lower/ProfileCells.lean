import SingularValueBounds.KL.Lower.HigherCost

/-! Closed cell coverage, the small-shape effective cap, and the full
non-plateau lower profile. -/
open MeasureTheory Set
open scoped Matrix BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1600000

theorem generalLowerProfile_small {k : ℝ} (hk : 0 ≤ k) (hk3 : k ≤ 3/100) :
    generalLowerProfile k = 3/2 := by
  have h := generalLowerPolynomial_mono ⟨hk,by linarith⟩
    (show (3/100:ℝ) ∈ Icc 0 1 by norm_num) hk3
  have hp : generalLowerPolynomial k ≤ 3/2 := by
    unfold generalLowerPolynomial
    norm_num [generalLowerPolynomial] at h
    linarith
  unfold generalLowerProfile
  rw [max_eq_left hp]
  norm_num

theorem lower_moment_cells_cover {k : ℝ} (hk0 : (3/100:ℝ) ≤ k) (hk1 : k ≤ 711/1000) :
    ∃ i : Fin 681,k ∈ Icc (((i.val+30:ℚ)/1000):ℝ) (((i.val+31:ℚ)/1000):ℝ) := by
  let j := min 710 ⌊1000*k⌋₊
  have hk : 0 ≤ 1000*k := by linarith
  have hjlo : 30 ≤ j := le_min (by norm_num) ((Nat.le_floor_iff hk).2 (by norm_num; linarith))
  have hjhi : j ≤ 710 := min_le_left _ _
  let i : Fin 681 := ⟨j-30,by omega⟩
  have hi : i.val+30 = j := by dsimp [i]; omega
  have hi' : i.val+31 = j+1 := by omega
  refine ⟨i,?_⟩
  have hlow : (j:ℝ) ≤ 1000*k := (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le hk)
  have hupp : 1000*k ≤ (j:ℝ)+1 := by
    by_cases hj : ⌊1000*k⌋₊ ≤ 710
    · have he : j = ⌊1000*k⌋₊ := min_eq_right hj
      rw [he]
      exact (Nat.lt_floor_add_one (1000*k)).le
    · have he : j = 710 := min_eq_left (by omega)
      rw [he]
      norm_num
      linarith
  push_cast
  have hiR : (i.val:ℝ)+30=(j:ℝ) := by exact_mod_cast hi
  have hiR' : (i.val:ℝ)+31=(j:ℝ)+1 := by exact_mod_cast hi'
  constructor <;> linarith

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem normalized_lower_mixed_small {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R = 1)
    (hcell : LowerCertificates.MomentCellCertificate (3/100) (3/100) 50)
    (hcap : spectralMaximum R hR.isHermitian ≤ 3/100) :
    (∫ ω,quadraticForm (lowerWeight R) X ω*quadraticForm (lowerComparison0 R hR) X ω ∂μ)-
      K^2*Matrix.trace R ≤ (3/2:ℝ)*K^2*logParameter K := by
  let k := spectralMaximum R hR.isHermitian
  have hk : 0 < k := (hR.eigenvalues_pos (Classical.arbitrary ι)).trans_le
    (eigenvalue_le_spectralMaximum hR.isHermitian _)
  have hcap' : k ≤ 3/100 := hcap
  have hU : lowerMomentU 50 (3/100) = (400/147:ℝ) := by
    norm_num [lowerMomentU,generalLowerProfile,generalLowerPolynomial]
  have hcs := hcell.shape_bounds (k:=(3/100:ℝ)) (by norm_num)
  norm_num only [Rat.cast_ofNat,Rat.cast_div,Rat.cast_zero,Rat.cast_one] at hcs
  rw [hU] at hcs
  have huk : (400/147:ℝ)*k < 1 := by nlinarith [hcs.1]
  have hM : k^2 < lowerM ((400/147:ℝ)*k) := by
    have hh := lowerM_quadratic_le (by positivity : 0 < (400/147:ℝ)*k) huk
    nlinarith [sq_pos_of_pos hk]
  have hJ := lowerJ_scaled_mono (by norm_num : (0:ℝ) ≤ 400/147) le_rfl hk hcap' hcs.1
  have hcond := hcell.entropy_condition (k:=(3/100:ℝ)) (by norm_num)
  norm_num only [Rat.cast_ofNat,Rat.cast_div,Rat.cast_zero,Rat.cast_one] at hcond
  rw [hU] at hcond
  apply normalized_lower_higher_mixed hsg hiso hK hR hF (shape:=(3/100:ℝ))
    (by norm_num) (by norm_num) hcap (p:=50) (u:=400/147) (C:=3/2)
    (by norm_num) (by norm_num) huk hM (by norm_num)
  have he : lowerJ ((400/147:ℝ)*k)/(2*k^2) ≤
      lowerJ ((400/147:ℝ)*(3/100))/(2*(3/100:ℝ)^2) := by
    convert! div_le_div_of_nonneg_right hJ (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring
  dsimp [k] at he
  norm_num at he ⊢
  linarith

theorem normalized_lower_mixed_nonplateau {X : Ω → ι → ℝ} {K : ℝ}
    (hsg : SubGaussianMGF μ X K) (hiso : CentredIsotropic μ X) (hK : 1 ≤ K)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (hF : frobenius R = 1)
    (hdata : LowerCertificates.MomentCellConditions)
    (hcap : spectralMaximum R hR.isHermitian ≤ 711/1000) :
    (∫ ω,quadraticForm (lowerWeight R) X ω*quadraticForm (lowerComparison0 R hR) X ω ∂μ)-
      K^2*Matrix.trace R ≤ generalLowerProfile (spectralMaximum R hR.isHermitian)*K^2*logParameter K := by
  by_cases hsmall : spectralMaximum R hR.isHermitian ≤ 3/100
  · have hk : 0 ≤ spectralMaximum R hR.isHermitian :=
      ((hR.eigenvalues_pos (Classical.arbitrary ι)).trans_le (eigenvalue_le_spectralMaximum hR.isHermitian _)).le
    rw [generalLowerProfile_small hk hsmall]
    exact normalized_lower_mixed_small hsg hiso hK hR hF hdata.2 hsmall
  · obtain ⟨i,hi⟩ := lower_moment_cells_cover (le_of_lt (lt_of_not_ge hsmall)) hcap
    exact normalized_lower_mixed_on_cell hsg hiso hK hR hF (hdata.1 i) (by simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat] using hi)

end
end SingularValueBounds.KL
