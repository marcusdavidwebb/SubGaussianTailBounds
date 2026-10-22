import Mathlib
/-! # Averaging an independent new row by Fubini -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SingularValueBounds

noncomputable section

/-- Directly average a new independent input, including product integrability. -/
theorem independent_weighted_average
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Ω → α} {X : Ω → β}
    (hP : Measurable P) (hX : Measurable X) (hind : IndepFun P X μ)
    {w : α → ℝ} (hw : Measurable w) (hw0 : ∀ a, 0 ≤ w a)
    (hwi : Integrable (fun ω => w (P ω)) μ)
    {g : α × β → ℝ} (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) {C : ℝ}
    (hgi : ∀ a, Integrable (fun b => g (a, b)) (μ.map X))
    (hgb : ∀ a, (∫ b, g (a, b) ∂μ.map X) ≤ C) :
    Integrable (fun ω => w (P ω) * g (P ω, X ω)) μ ∧
    (∫ ω, w (P ω) * g (P ω, X ω) ∂μ) ≤ C * ∫ ω, w (P ω) ∂μ := by
  let f : α × β → ℝ := fun z => w z.1 * g z
  have hf : Measurable f := (hw.comp measurable_fst).mul hg
  have hf0 : ∀ z, 0 ≤ f z := fun z => mul_nonneg (hw0 z.1) (hg0 z)
  have hfi : ∀ a, Integrable (fun b => f (a,b)) (μ.map X) :=
    fun a => (hgi a).const_mul (w a)
  have hwb : Integrable w (μ.map P) :=
    (integrable_map_measure hw.aestronglyMeasurable hP.aemeasurable).2 hwi
  have hsec : Measurable (fun a => ∫ b, f (a,b) ∂μ.map X) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hbound (a) : (∫ b, f (a,b) ∂μ.map X) ≤ C * w a := by
    dsimp [f]; rw [integral_const_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hgb a) (hw0 a)
  have hseci : Integrable (fun a => ∫ b, f (a,b) ∂μ.map X) (μ.map P) := by
    apply (hwb.const_mul C).mono' hsec.aestronglyMeasurable
    filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun b => hf0 (a,b)))]
    exact hbound a
  have hprod : Integrable f ((μ.map P).prod (μ.map X)) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall hfi, ?_⟩
    simpa only [Real.norm_of_nonneg (hf0 _)] using hseci
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hP.aemeasurable hX.aemeasurable).1 hind
  have hpair : AEMeasurable (fun ω => (P ω, X ω)) μ := (hP.prodMk hX).aemeasurable
  constructor
  · exact (integrable_map_measure hf.aestronglyMeasurable hpair).1 (hmap.symm ▸ hprod)
  · calc
      _ = ∫ z, f z ∂((μ.map P).prod (μ.map X)) := by
        rw [← hmap, integral_map hpair hf.aestronglyMeasurable]
      _ = ∫ a, ∫ b, f (a,b) ∂μ.map X ∂μ.map P := integral_prod f hprod
      _ ≤ ∫ a, C * w a ∂μ.map P := integral_mono hseci (hwb.const_mul C) hbound
      _ = _ := by rw [integral_const_mul, integral_map hP.aemeasurable hw.aestronglyMeasurable]

end
end SingularValueBounds
