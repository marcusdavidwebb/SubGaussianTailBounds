import NLAlib.Probability.SubGaussianVector.Basic
import NLAlib.Probability.Isotropic

/-!
# Exact correspondence with NLA-lib's row assumptions

The historical predicates below record the explicit row assumptions used before
the canonical statement imported NLA-lib. They are retained only to state and
prove the equivalence, not as substitutes for the imported definitions.

NLA-lib uses a variance proxy, so its parameter is `K ^ 2`. Its sub-Gaussian
condition already implies centering and coordinate integrability. Measurability
is retained separately: NLA-lib's predicates supply almost-everywhere
measurability, whereas the original theorem requires measurable rows.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix NNReal

namespace SubGaussian

universe u

/-- The original measurable, centered, coordinate-isotropic row hypothesis. -/
structure PreviousIsCentredIsotropic {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (X : Ω → Fin n → ℝ) (μ : Measure Ω) : Prop where
  measurable : Measurable X
  centred : ∀ j, Integrable (fun ω => X ω j) μ ∧ (∫ ω, X ω j ∂μ) = 0
  isotropic : ∀ j k,
    Integrable (fun ω => X ω j * X ω k) μ ∧
    (∫ ω, X ω j * X ω k ∂μ) = if j = k then 1 else 0

/-- The original directional MGF hypothesis, with standard-deviation proxy `K`. -/
def PreviousIsSubgaussianVector {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (X : Ω → Fin n → ℝ) (K : ℝ) (μ : Measure Ω) : Prop :=
  ∀ (v : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
    Integrable (fun ω => Real.exp (θ * (∑ j, X ω j * v j))) μ ∧
    (∫ ω, Real.exp (θ * (∑ j, X ω j * v j)) ∂μ)
      ≤ Real.exp (K ^ 2 * θ ^ 2 * ‖v‖ ^ 2 / 2)

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
  {X : Ω → Fin n → ℝ} {K : ℝ}

/-- The imported MGF hypothesis has exactly the original normalization. -/
theorem isSubgaussianVector_iff_previous :
    NLAlib.IsSubgaussianVector X ⟨K ^ 2, sq_nonneg K⟩ μ ↔
      PreviousIsSubgaussianVector X K μ := by
  constructor
  · intro h v θ
    have hv := h.hasSubgaussianMGF v.ofLp
    have hid : (fun ω => RCLike.re (v.ofLp ⬝ᵥ X ω)) =
        (fun ω => ∑ j, X ω j * v j) := by
      funext ω
      simp only [RCLike.re_to_real, dotProduct, mul_comm]
    rw [hid] at hv
    refine ⟨hv.integrable_exp_mul θ, ?_⟩
    have hb := hv.mgf_le θ
    change (∫ ω, Real.exp (θ * (∑ j, X ω j * v j)) ∂μ) ≤
      Real.exp (K ^ 2 * ‖v‖ ^ 2 * θ ^ 2 / 2) at hb
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hb
  · intro h
    refine ⟨fun v => ⟨?_, ?_⟩⟩
    · intro θ
      simpa only [RCLike.re_to_real, dotProduct, mul_comm] using
        (h (WithLp.toLp 2 v) θ).1
    · intro θ
      change (∫ ω, Real.exp (θ * RCLike.re (v ⬝ᵥ X ω)) ∂μ) ≤
        Real.exp (K ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 * θ ^ 2 / 2)
      simpa only [RCLike.re_to_real, dotProduct, mul_assoc, mul_left_comm, mul_comm]
        using (h (WithLp.toLp 2 v) θ).2

/-- Imported sub-Gaussianity and isotropy recover the original coordinate data. -/
theorem previousIsCentredIsotropic_of_nla [IsProbabilityMeasure μ]
    (hm : Measurable X)
    (hsub : NLAlib.IsSubgaussianVector X ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hiso : NLAlib.IsIsotropic X μ) : PreviousIsCentredIsotropic X μ := by
  refine ⟨hm, ?_, ?_⟩
  · intro j
    exact ⟨memLp_one_iff_integrable.mp (by simpa using hsub.memLp_apply j 1),
      hsub.integral_apply_eq_zero j⟩
  · intro j k
    exact ⟨by simpa only [star_trivial] using hiso.integrable_mul_star j k,
      by simpa only [star_trivial] using hiso.integral_mul_star j k⟩

/-- The original coordinate second moments supply the imported isotropy data. -/
theorem isIsotropic_of_previous
    (hsub : NLAlib.IsSubgaussianVector X ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hprev : PreviousIsCentredIsotropic X μ) : NLAlib.IsIsotropic X μ := by
  refine ⟨fun j => ?_, fun j k => ?_⟩
  · simpa using hsub.memLp_apply j 2
  · simpa only [star_trivial] using (hprev.isotropic j k).2

/-- Replacing the original row assumptions by imported predicates changes no
hypothesis on a probability space, in any sample-space universe. -/
theorem nla_rows_iff_previous [IsProbabilityMeasure μ] :
    (Measurable X ∧ NLAlib.IsSubgaussianVector X ⟨K ^ 2, sq_nonneg K⟩ μ ∧
      NLAlib.IsIsotropic X μ) ↔
    (PreviousIsCentredIsotropic X μ ∧ PreviousIsSubgaussianVector X K μ) := by
  constructor
  · rintro ⟨hm, hsub, hiso⟩
    exact ⟨previousIsCentredIsotropic_of_nla hm hsub hiso,
      isSubgaussianVector_iff_previous.mp hsub⟩
  · rintro ⟨hprev, hsg⟩
    have hsub := isSubgaussianVector_iff_previous.mpr hsg
    exact ⟨hprev.measurable, hsub, isIsotropic_of_previous hsub hprev⟩

end SubGaussian
