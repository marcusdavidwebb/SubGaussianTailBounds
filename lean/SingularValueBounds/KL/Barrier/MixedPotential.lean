import SingularValueBounds.KL.Barrier.MixedInverse
import SingularValueBounds.KL.Barrier.MixedBudget

/-! # The reciprocal-shape trace potential

Writing the primitive in the scalar cap variable avoids differentiating its
inverse. Clipping the lower integration limit makes it nonnegative after the
cap is automatically satisfied.
-/
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace SingularValueBounds.KL
noncomputable section

def mixedTracePotential (b top : ℝ) (j : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (∫ c in min (b/τ) top..top, (j c)⁻¹^2) / b

def mixedTraceKernel (b : ℝ) (j : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (j (b/τ))⁻¹^2 / τ^2

lemma mixedTracePotential_nonneg {b top : ℝ} (hb : 0 < b) (j : ℝ → ℝ) (τ : ℝ) :
    0 ≤ mixedTracePotential b top j τ := by
  apply div_nonneg _ hb.le
  exact intervalIntegral.integral_nonneg (min_le_right _ _) (fun _ _ => sq_nonneg _)

lemma continuousOn_mixedTracePotential {b top : ℝ} {j : ℝ → ℝ}
    (hj : Continuous j) (hj0 : ∀ c, j c ≠ 0) :
    ContinuousOn (mixedTracePotential b top j) (Ioi 0) := by
  have hf : Continuous (fun c => (j c)⁻¹^2) := (hj.inv₀ hj0).pow 2
  have hp : Continuous (fun c => ∫ t in c..top, (j t)⁻¹^2) := by
    apply continuous_iff_continuousAt.mpr
    intro c
    exact (intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable c top)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).continuousAt
  intro τ hτ
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  exact ((hp.continuousAt.comp
    ((continuousAt_const.div continuousAt_id hτ0).min continuousAt_const)).div_const b).continuousWithinAt

theorem hasDerivAt_mixedTracePotential {b top : ℝ} (hb : 0 < b)
    {j : ℝ → ℝ} (hj : Continuous j) (hj0 : ∀ c, j c ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (hactive : b/τ < top) :
    HasDerivAt (mixedTracePotential b top j) (mixedTraceKernel b j τ) τ := by
  have hf : Continuous (fun c => (j c)⁻¹^2) := (hj.inv₀ hj0).pow 2
  have hquot : HasDerivAt (fun t : ℝ => b/t) (-b/τ^2) τ := by
    convert! (hasDerivAt_const τ b).div (hasDerivAt_id τ) hτ.ne' using 1 <;> simp
  have hd := ((intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable (b/τ) top)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).comp τ hquot).div_const b
  have he : mixedTracePotential b top j =ᶠ[𝓝 τ]
      (fun t => (∫ c in b/t..top, (j c)⁻¹^2)/b) := by
    filter_upwards [(continuousAt_const.div continuousAt_id hτ.ne').eventually
      (Iio_mem_nhds hactive)] with t ht
    change b/t < top at ht
    simp only [mixedTracePotential,min_eq_left ht.le]
  have hk : (-(j (b/τ))⁻¹^2 * (-b/τ^2))/b = mixedTraceKernel b j τ := by
    unfold mixedTraceKernel
    calc
      _ = ((j (b/τ))⁻¹^2 / τ^2)*(b/b) := by ring
      _ = _ := by rw [div_self hb.ne',mul_one]
  rw [hk] at hd
  exact hd.congr_of_eventuallyEq he

lemma mixedTracePotential_at_initial {b top low : ℝ} (hb : b ≠ 0) (hlow : low ≠ 0)
    (hle : low ≤ top) (j : ℝ → ℝ) :
    mixedTracePotential b top j (b/low) = (∫ c in low..top, (j c)⁻¹^2)/b := by
  have he : b/(b/low) = low := by field_simp
  simp only [mixedTracePotential,he,min_eq_left hle]

end
end SingularValueBounds.KL
