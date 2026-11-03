import SingularValueBounds.KL.Certificates.ConcreteRounded
import SingularValueBounds.KL.Certificates.IntegerRoundedExp

/-! The general entropy margins need only 24 Taylor steps. The endpoint
calculations may use their own precision; the existing transcript theorems
justify this shorter calculation directly, with no equality to an 80-step run. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
noncomputable section

def generalMeanExpLowerQ (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 25, expTermLowerQ x j

def generalMeanExpPositiveQ (x : ℚ) : ℚ :=
  (∑ j ∈ Finset.range 25, expTermUpperQ x j)+
    roundUpQ (roundUpQ (expTermUpperQ x 24*x/25)/(1-x/26))

def generalMeanExpUpperQ (x : ℚ) : ℚ :=
  let y := roundUpQ x
  if y < 0 then roundUpQ (1/generalMeanExpLowerQ (-y)) else generalMeanExpPositiveQ y

theorem generalMeanExpDomain_nonpos {x : ℚ} (hx : x ≤ 0) : roundUpQ x < 26 :=
  (roundUpQ_nonpos hx).trans_lt (by norm_num)

theorem generalMeanExpUpper_sound {x : ℚ} (hdom : roundUpQ x < 26) :
    Real.exp (x : ℝ) ≤ (generalMeanExpUpperQ x : ℝ) := by
  have hxy : (x : ℝ) ≤ (roundUpQ x : ℝ) := by exact_mod_cast le_roundUpQ x
  apply (Real.exp_le_exp.mpr hxy).trans
  unfold generalMeanExpUpperQ
  dsimp only
  split_ifs with hy
  · have hlow : ExpLowerTranscript 24 (-roundUpQ x)
        (generalMeanExpLowerQ (-roundUpQ x)) (expTermLowerQ (-roundUpQ x)) := by
      refine ⟨neg_nonneg.mpr hy.le, le_rfl, ?_, le_rfl⟩
      intro j _
      exact roundDownQ_le _
    have hpos : 0 < generalMeanExpLowerQ (-roundUpQ x) := by
      have hh : (1 : ℚ) ≤ generalMeanExpLowerQ (-roundUpQ x) := by
        change expTermLowerQ (-roundUpQ x) 0 ≤ ∑ j ∈ Finset.range 25, expTermLowerQ (-roundUpQ x) j
        exact Finset.single_le_sum (fun j _ => expTermLowerQ_nonneg (neg_nonneg.mpr hy.le) j) (by decide)
      linarith
    simpa only [Rat.cast_neg, neg_neg] using
      exp_neg_upper_of_lower_transcript hlow hpos (le_roundUpQ _)
  · have hu : ExpUpperTranscript 24 (roundUpQ x)
        (generalMeanExpPositiveQ (roundUpQ x)) (expTermUpperQ (roundUpQ x)) := by
      refine ⟨le_of_not_gt hy, by norm_num; exact hdom, le_rfl, ?_, ?_⟩
      · intro j _
        exact le_roundUpQ _
      · unfold generalMeanExpPositiveQ
        apply add_le_add_right
        apply le_trans _ (le_roundUpQ _)
        norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
        apply div_le_div_of_nonneg_right (le_roundUpQ _)
        exact sub_nonneg.mpr ((div_le_one (by norm_num : (0 : ℚ) < 26)).mpr hdom.le)
    exact hu.sound

/-- Integer evaluation of this shorter algorithm. Only its own calculation is
proved equal; no earlier numerical data or longer expansion is reproduced. -/
def integerGeneralMeanExpUpper (x : ℚ) : ℚ :=
  let b : ℤ := -⌊-(x*roundingScale)⌋
  if fixedQ b < 0 then
    roundUpQ (1/fixedQ (expIntegerFoldSaturated false (-b) 24 0 fixedScaleNat fixedScaleNat).2)
  else
    fixedQ (expIntegerFoldSaturated true b 24 0 fixedScaleNat fixedScaleNat).2+
      roundUpQ (roundUpQ (fixedQ (expIntegerTerm true b 24)*fixedQ b/25)/(1-fixedQ b/26))

theorem generalMeanExpUpperQ_eq_integer (x : ℚ) :
    generalMeanExpUpperQ x = integerGeneralMeanExpUpper x := by
  have hr : roundUpQ x = fixedQ (-⌊-(x*roundingScale)⌋) := by
    simp [roundUpQ, fixedQ]
  have hn (b : ℤ) : -fixedQ b = fixedQ (-b) := by simp [fixedQ, neg_div]
  unfold generalMeanExpUpperQ integerGeneralMeanExpUpper
  simp only [expIntegerFoldSaturated_eq]
  rw [hr]
  split_ifs
  · rw [hn]
    unfold generalMeanExpLowerQ
    rw [expLowerSum_fixedQ_order]
  · unfold generalMeanExpPositiveQ
    rw [expUpperSum_fixedQ_order, expTermUpperQ_fixedQ]

end
end SingularValueBounds.KL.Certificates
