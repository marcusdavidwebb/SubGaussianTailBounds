import SingularValueBounds.KL.Upper.GeneralSecondCertificates
import SingularValueBounds.KL.Upper.GeneralLowSecond

/-! Closed coverage of the bounded logarithmic range and the low-shape scalar branch. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
open UpperSecond
noncomputable section
set_option maxHeartbeats 1600000

/-- The 334 closed cells cover their complete stated interval. -/
theorem general_second_cells_cover_y {y : ℝ} (hy0 : (376/1000:ℝ) ≤ y)
    (hy1 : y ≤ 710/1000) :
    ∃ j : Fin 334,y ∈ Icc (secondCellLo j:ℝ) (secondCellHi j:ℝ) := by
  let k := min 709 ⌊1000*y⌋₊
  have hy : 0 ≤ 1000*y := by linarith
  have hklo : 376 ≤ k := le_min (by norm_num) ((Nat.le_floor_iff hy).2 (by norm_num; linarith))
  have hkhi : k ≤ 709 := min_le_left _ _
  let j : Fin 334 := ⟨k-376,by omega⟩
  have hj : j.val+376 = k := by dsimp [j]; omega
  have hj' : j.val+377 = k+1 := by omega
  refine ⟨j,?_⟩
  have hlo : (k:ℝ) ≤ 1000*y := (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le hy)
  have hhi : 1000*y ≤ (k:ℝ)+1 := by
    by_cases hk : ⌊1000*y⌋₊ ≤ 709
    · rw [show k=⌊1000*y⌋₊ from min_eq_right hk]
      exact (Nat.lt_floor_add_one (1000*y)).le
    · rw [show k=709 from min_eq_left (by omega)]
      norm_num
      linarith
  have hjR : (j.val:ℝ)+376=(k:ℝ) := by exact_mod_cast hj
  have hjR' : (j.val:ℝ)+377=(k:ℝ)+1 := by exact_mod_cast hj'
  dsimp [secondCellLo,secondCellHi]
  push_cast
  constructor <;> linarith

/-- The cells overlap the endpoint neighbourhood and the unbounded-range cutoff. -/
theorem general_second_range_coverage (L : ℝ) :
    L ≤ 51/50 ∨ (∃ j : Fin 334,L-1 ∈ Icc (secondCellDLo j:ℝ) (secondCellDHi j:ℝ)) ∨
      5/4 ≤ L := by
  by_cases hs : L ≤ 51/50
  · exact Or.inl hs
  by_cases hl : 5/4 ≤ L
  · exact Or.inr (Or.inr hl)
  have hd : 0 ≤ L-1 := by linarith
  let y := Real.sqrt (Real.sqrt (L-1))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hy4 : y^4=L-1 := by
    have h1 := Real.sq_sqrt hd
    have h2 := Real.sq_sqrt (Real.sqrt_nonneg (L-1))
    dsimp [y]
    nlinarith [sq_nonneg (Real.sqrt (L-1))]
  have hylo : (376/1000:ℝ) ≤ y := by
    by_contra hh
    have hh' : y ≤ 376/1000 := (lt_of_not_ge hh).le
    have hp := pow_le_pow_left₀ hy hh' 4
    norm_num at hp
    nlinarith
  have hyhi : y ≤ 710/1000 := by
    by_contra hh
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤710/1000) (le_of_not_ge hh) 4
    norm_num at hp
    nlinarith
  obtain ⟨j,hj⟩ := general_second_cells_cover_y hylo hyhi
  refine Or.inr (Or.inl ⟨j,?_,?_⟩)
  · have hj0 : (0:ℝ) ≤ (secondCellLo j:ℝ) := by
      dsimp [secondCellLo]
      positivity
    have hp := pow_le_pow_left₀ hj0 hj.1 4
    simpa [secondCellDLo,hy4] using hp
  · have hp := pow_le_pow_left₀ hy hj.2 4
    simpa [secondCellDHi,hy4] using hp

lemma K_sq_eq_exp_logParameter {K : ℝ} (hK : 0 < K) :
    K^2=Real.exp (2*(logParameter K-1)) := by
  rw [show 2*(logParameter K-1)=Real.log K+Real.log K by unfold logParameter; ring]
  rw [Real.exp_add,Real.exp_log hK]
  ring

lemma general_second_K_sq_le {K : ℝ} (hK : 0 < K) {b : ℚ}
    (hb : -50 < 2*b ∧ 2*b < 50) (hL : logParameter K-1 ≤ (b:ℝ)) :
    K^2 ≤ (secondExpUpperQ (2*b):ℝ) := by
  rw [K_sq_eq_exp_logParameter hK]
  have he : Real.exp (2*(logParameter K-1)) ≤ Real.exp (2*(b:ℝ)) := Real.exp_le_exp.mpr (by linarith)
  exact he.trans (by simpa using (second_exp_enclosure hb).2)

lemma general_second_small_fourth {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {K : ℝ}
    (h : GeneralSecondCertificateConditions)
    (hsg : HasSubgaussianMGF Y ⟨K^2,sq_nonneg K⟩ μ)
    (hvar : (∫ ω,Y ω^2 ∂μ)=1) (hK : 0 < K) (hL : logParameter K ≤ 51/50) :
    (∫ ω,Y ω^4 ∂μ)<4 := by
  have hE : K^2 ≤ (secondExpUpperQ (1/25):ℝ) := by
    convert! general_second_K_sq_le hK (b:=1/50) (by norm_num) (by push_cast; linarith) using 1 <;> norm_num
  exact scalar_fourth_exclusion (x:=(5/2:ℝ)) hsg hvar (by norm_num) hE
    (by simpa using fourth_exclusion_of_certificate h.1)

lemma general_second_cell_fourth {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {K : ℝ}
    (h : GeneralSecondCertificateConditions)
    (hsg : HasSubgaussianMGF Y ⟨K^2,sq_nonneg K⟩ μ)
    (hvar : (∫ ω,Y ω^2 ∂μ)=1) (hK : 0 < K) (j : Fin 334)
    (hL : logParameter K-1 ≤ (secondCellDHi j:ℝ)) :
    (∫ ω,Y ω^4 ∂μ)<(secondCellM j:ℝ) := by
  have hc := h.2.2.2.1 j
  have hm : (0:ℝ)<secondCellM j := by exact_mod_cast hc.2.2.2.2.2.2.m_pos
  exact scalar_fourth_exclusion hsg hvar hm
    (general_second_K_sq_le hK (b:=secondCellDHi j) ⟨by linarith [hc.1,hc.2.1],hc.2.2.2.1⟩ hL)
    (fourth_exclusion_of_certificate hc.2.2.2.2.2.2)

/-- The finite certificates control the complete bounded range, with its endpoints. -/
theorem general_second_bounded_range (h : GeneralSecondCertificateConditions) (i : Fin 3)
    {m L : ℝ} (hL : 1 ≤ L) (hLhi : L < 5/4)
    (hsmall : L ≤ 51/50 → m ≤ 4)
    (hcells : ∀ j : Fin 334,L-1 ∈ Icc (secondCellDLo j:ℝ) (secondCellDHi j:ℝ) →
      m ≤ (secondCellM j:ℝ)) :
    generalSecondScalar i m (L-1) ≤ 9/2 := by
  by_cases hs : L ≤ 51/50
  · exact general_second_small_bound h i (hsmall hs) ⟨by linarith,by linarith⟩
  have hcover := general_second_range_coverage L
  rcases hcover with hh|⟨j,hj⟩|hh
  · exact (hs hh).elim
  · exact general_second_cell_bound h j i (hcells j hj) hj
  · exact (not_le_of_gt hLhi hh).elim

def generalLowSecondDerivative (d : ℝ) : ℝ :=
  (5/21)*Real.exp (-5*d/4)*((-5/4)*(13/4+2/(1+d))-2/(1+d)^2)+
    Real.exp (-2*d)*(1/(1+d)+1/(2*(1+d)^2))

lemma hasDerivAt_generalLowSecondCost {d : ℝ} (hd : d ≠ -1) :
    HasDerivAt generalLowSecondCost (generalLowSecondDerivative d) d := by
  have hd1 : 1+d ≠ 0 := by intro hh; apply hd; linarith
  have hr := (hasDerivAt_const d (2:ℝ)).div ((hasDerivAt_id d).const_add 1) (by simpa [add_comm] using sub_ne_zero.mpr hd)
  have he1 := (((hasDerivAt_id d).const_mul (-5:ℝ)).div_const 4).exp
  have he2 := ((hasDerivAt_id d).const_mul (-2:ℝ)).exp
  have ht := he2.div (((hasDerivAt_id d).const_add 1).const_mul 2) (by simpa only [id_eq] using mul_ne_zero (by norm_num : (2:ℝ)≠0) hd1)
  convert! (((he1.mul ((hasDerivAt_const d (13/4:ℝ)).add hr)).const_mul (5/21:ℝ)).const_add (13/4:ℝ)).sub ht using 1 <;>
    (try ext x) <;> dsimp [generalLowSecondCost,generalLowSecondDerivative] <;> field_simp [hd1] <;> ring

lemma generalLowSecond_scaled_derivative {d : ℝ} (hd : 0 ≤ d) :
    -(1+d)^2*Real.exp (2*d)*generalLowSecondDerivative d ≥
      (325/336:ℝ)*(1+d)^2-(17/42)*(1+d)-1/42 := by
  have hd1 : 1+d ≠ 0 := by linarith
  have he1 : Real.exp (-5*d/4)*Real.exp (2*d)=Real.exp (3*d/4) := by
    rw [←Real.exp_add]; congr 1; ring
  have he2 : Real.exp (-2*d)*Real.exp (2*d)=1 := by
    rw [←Real.exp_add]; ring_nf; exact Real.exp_zero
  have heq : -(1+d)^2*Real.exp (2*d)*generalLowSecondDerivative d =
      Real.exp (3*d/4)*((325/336:ℝ)*(1+d)^2+(25/42)*(1+d)+10/21)-(1+d)-1/2 := by
    calc
      _ = (Real.exp (-5*d/4)*Real.exp (2*d))*
        ((325/336:ℝ)*(1+d)^2+(25/42)*(1+d)+10/21)-
        (Real.exp (-2*d)*Real.exp (2*d))*((1+d)+1/2) := by
          dsimp [generalLowSecondDerivative]
          field_simp
          ring
      _ = _ := by rw [he1,he2]; ring
  rw [heq]
  have he : 1 ≤ Real.exp (3*d/4) := Real.one_le_exp_iff.mpr (by positivity)
  have hp : 0 ≤ (325/336:ℝ)*(1+d)^2+(25/42)*(1+d)+10/21 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right he hp]

theorem generalLowSecondCost_antitone : AntitoneOn generalLowSecondCost (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro d hd
    exact (hasDerivAt_generalLowSecondCost (by have hh : 0 ≤ d := hd; linarith)).continuousAt.continuousWithinAt
  · intro d hd
    have hh : 0 ≤ d := interior_subset hd
    exact (hasDerivAt_generalLowSecondCost (by linarith)).hasDerivWithinAt
  · intro d hd
    have hh : 0 ≤ d := interior_subset hd
    have hs := generalLowSecond_scaled_derivative hh
    have hp : 0 < (325/336:ℝ)*(1+d)^2-(17/42)*(1+d)-1/42 := by
      nlinarith [sq_nonneg d]
    have he : 0 < (1+d)^2*Real.exp (2*d) := by positivity
    nlinarith

theorem generalLowSecondCost_le_four {d : ℝ} (hd : 0 ≤ d) : generalLowSecondCost d ≤ 4 := by
  have hh := generalLowSecondCost_antitone (show (0:ℝ)∈Ici 0 by simp) hd hd
  norm_num [generalLowSecondCost] at hh
  unfold generalLowSecondCost
  simp only [neg_mul,neg_div] at *
  linarith

end
end SingularValueBounds.KL
