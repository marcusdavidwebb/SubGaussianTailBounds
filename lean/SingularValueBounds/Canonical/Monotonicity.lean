import SingularValueBounds.Canonical.Adapter

/-! Componentwise weakening of the canonical propositions. This permits
baseline corollaries of a stronger jointly proved quartet. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SubGaussian
open SingularValueBounds.Canonical
universe u

theorem GeneralSingularValueTailBound.mono
    {α β γ δ α' β' γ' δ' : ℝ}
    (h : GeneralSingularValueTailBound.{u} α β γ δ)
    (ha : α ≤ α') (hb : β ≤ β') (hg : γ ≤ γ') (hd : δ ≤ δ') :
    GeneralSingularValueTailBound.{u} α' β' γ' δ' := by
  rw [general_iff_previous] at h ⊢
  refine ⟨⟨h.1.1.trans_le ha, h.1.2.1.trans_le hb,
    h.1.2.2.1.trans_le hg, h.1.2.2.2.trans_le hd⟩, ?_⟩
  intro Ω _ μ _ m n hn A K hnm hK hm hind hc hi hsg t ht
  obtain ⟨hl, hu⟩ := h.2 μ m n hn A K hnm hK hm hind hc hi hsg t ht
  have hA : Measurable (fun ω i j => A ω i j) := measurable_pi_lambda _ hm
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hL : 0 ≤ Real.log (Real.exp 1 * K) := by
    rw [logParameter_eq hK]
    exact zero_le_one.trans (SingularValueBounds.one_le_logParameter hK)
  have hKL := mul_nonneg hK0 hL
  have hKt := mul_nonneg (mul_nonneg hK0 (Real.sqrt_nonneg (Real.log (Real.exp 1 * K)))) ht
  have hal := mul_le_mul_of_nonneg_right ha hKL
  have hbl := mul_le_mul_of_nonneg_right hb hKt
  have hgu := mul_le_mul_of_nonneg_right hg hKL
  have hdu := mul_le_mul_of_nonneg_right hd hKt
  constructor
  · refine ⟨measurableSet_le ((measurable_smallestSingularValue hn).comp hA)
      measurable_const, le_trans (measure_mono ?_) hl.2⟩
    intro ω hω
    change Previous.smallestSingularValue hn (A ω) ≤ _ at hω ⊢
    nlinarith
  · refine ⟨measurableSet_le measurable_const
      ((measurable_largestSingularValue hn).comp hA), le_trans (measure_mono ?_) hu.2⟩
    intro ω hω
    change _ ≤ Previous.largestSingularValue hn (A ω) at hω ⊢
    nlinarith

theorem UnitSingularValueTailBound.mono
    {α β γ δ α' β' γ' δ' : ℝ}
    (h : UnitSingularValueTailBound.{u} α β γ δ)
    (ha : α ≤ α') (hb : β ≤ β') (hg : γ ≤ γ') (hd : δ ≤ δ') :
    UnitSingularValueTailBound.{u} α' β' γ' δ' := by
  rw [unit_iff_previous] at h ⊢
  refine ⟨⟨h.1.1.trans_le ha, h.1.2.1.trans_le hb,
    h.1.2.2.1.trans_le hg, h.1.2.2.2.trans_le hd⟩, ?_⟩
  intro Ω _ μ _ m n hn A hnm hm hind hc hi hsg t ht
  obtain ⟨hl, hu⟩ := h.2 μ m n hn A hnm hm hind hc hi hsg t ht
  have hA : Measurable (fun ω i j => A ω i j) := measurable_pi_lambda _ hm
  have hbl := mul_le_mul_of_nonneg_right hb ht
  have hdu := mul_le_mul_of_nonneg_right hd ht
  constructor
  · refine ⟨measurableSet_le ((measurable_smallestSingularValue hn).comp hA)
      measurable_const, le_trans (measure_mono ?_) hl.2⟩
    intro ω hω
    change Previous.smallestSingularValue hn (A ω) ≤ _ at hω ⊢
    linarith
  · refine ⟨measurableSet_le measurable_const
      ((measurable_largestSingularValue hn).comp hA), le_trans (measure_mono ?_) hu.2⟩
    intro ω hω
    change _ ≤ Previous.largestSingularValue hn (A ω) at hω ⊢
    linarith

end SubGaussian
