import SingularValueBounds.KL.Upper.GeneralRareSecond

/-! Low-shape second moments from the capped first-moment cutoff. -/
open MeasureTheory
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1300000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def generalLowSecondCost (d : ℝ) : ℝ :=
  13/4+(5/21)*Real.exp (-5*d/4)*(13/4+2/(1+d))-Real.exp (-2*d)/(2*(1+d))

theorem upper_low_second_of_tail {Y : Ω → ℝ} {K d : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω,0 ≤ Y ω) (hMean : (∫ ω,Y ω ∂μ) ≤ 1)
    (hK : 0 < K) (hd : 0 ≤ d) (hKpow : K^2=Real.exp (2*d))
    (htail : ∀ u,0 ≤ u → μ.real {ω | u<Y ω} ≤ (46/15:ℝ)*Real.exp (-u/(2*K^2))) :
    Integrable (fun ω=>Y ω^2) μ ∧
    (∫ ω,Y ω^2 ∂μ)/(2*K^2*(1+d))-1/(2*K^2*(1+d)) ≤ generalLowSecondCost d := by
  let rate := 1/(2*K^2)
  let A := (13/2:ℝ)*K^2*(1+d)
  let eps := (46/15:ℝ)/rate*Real.exp (-(rate*A))
  have hr : 0 < rate := by dsimp [rate]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ht : ∀ u,0 ≤ u → μ.real {ω | u<Y ω} ≤ (46/15:ℝ)*Real.exp (-(rate*u)) := by
    intro u hu
    convert! htail u hu using 1 <;> congr 2 <;> dsimp [rate] <;> ring
  have hcut := first_moment_cutoff hY hY0 (by norm_num : (0:ℝ)≤46/15) hr hA ht hMean 1
  have hi := (exponential_tail_moment hY.aemeasurable hY0 (by norm_num : (0:ℝ)≤46/15) hr ht 1).1
  have hrate : 1/rate=2*K^2 := by dsimp [rate]; field_simp
  have heps : eps=(92/15:ℝ)*Real.exp (-(13/4:ℝ))*Real.exp (-5*d/4) := by
    have harg : rate*A=(13/4:ℝ)*(1+d) := by dsimp [rate,A]; field_simp; ring
    dsimp [eps]
    rw [harg]
    have hden : (46/15:ℝ)/rate=(92/15:ℝ)*K^2 := by dsimp [rate]; field_simp; ring
    rw [hden,hKpow]
    simp only [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have he0 : 0 ≤ eps := by dsimp [eps]; positivity
  have he : eps ≤ (5/21:ℝ)*Real.exp (-5*d/4) := by
    rw [heps]
    have hh := endpoint_cutoff_epsilon
    norm_num at hh
    exact mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
  have hB : 0 < K^2*(1+d) := by positivity
  have heInv : 1/(K^2)=Real.exp (-2*d) := by rw [hKpow,show -2*d=-(2*d) by ring,Real.exp_neg,one_div]
  norm_num [tailMomentSeries,Finset.sum_range_succ] at hcut
  change (∫ ω,Y ω^2 ∂μ)/2 ≤ (1-eps)*A/2+eps*(rate⁻¹+A) at hcut
  rw [← one_div,hrate] at hcut
  have hcost : (∫ ω,Y ω^2 ∂μ)/(2*K^2*(1+d))-1/(2*K^2*(1+d)) ≤
      13/4+eps*(13/4+2/(1+d))-Real.exp (-2*d)/(2*(1+d)) := by
    rw [← sub_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*K^2*(1+d))).2
    have hh := (div_le_iff₀ (by norm_num : (0:ℝ)<2)).1 hcut
    dsimp [A] at hh
    have heq : Real.exp (-2*d)*K^2=1 := by rw [← heInv]; field_simp
    have hd1 : 1+d ≠ 0 := by linarith
    have hfirst : ((13/4:ℝ)+eps*(13/4+2/(1+d)))*(2*K^2*(1+d)) =
        ((1-eps)*((13/2:ℝ)*K^2*(1+d))/2+eps*(2*K^2+(13/2:ℝ)*K^2*(1+d)))*2 := by
      field_simp [hd1]
      <;> ring
    have hlast : (Real.exp (-2*d)/(2*(1+d)))*(2*K^2*(1+d)) = 1 := by
      calc
        _ = Real.exp (-2*d)*K^2 := by field_simp [hd1]
        _ = 1 := heq
    rw [sub_mul,hfirst,hlast]
    exact sub_le_sub_right hh 1
  refine ⟨hi,hcost.trans ?_⟩
  dsimp [generalLowSecondCost]
  have hcoef : 0 ≤ (13/4:ℝ)+2/(1+d) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right he hcoef]

end
end SingularValueBounds.KL
