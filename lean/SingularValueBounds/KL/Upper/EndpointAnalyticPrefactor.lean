import SingularValueBounds.KL.Upper.GeneralMeanExp
import SingularValueBounds.KL.Certificates.ConcreteLog
import SingularValueBounds.KL.Upper.EntropyConvexity

/-! Sufficient prefactors for analytic endpoint entropy integrals. The logarithm
is enclosed once and the exponential uses the shared 24-step bound directly. -/
namespace SingularValueBounds.KL.Certificates
noncomputable section

def endpointJoint24Argument (k a q : ℚ) : ℚ :=
  q/2 + a*(-(logRoundedQ (1-q*k^2)).1-q*k^2)/(2*k^3)

def endpointJoint24Q (k a q : ℚ) : ℚ :=
  generalMeanExpUpperQ (endpointJoint24Argument k a q)

def endpointSmall24Argument (k q : ℚ) : ℚ :=
  -(logRoundedQ (1-q*k^2)).1/(2*k^2)

def endpointSmall24Q (k q : ℚ) : ℚ :=
  generalMeanExpUpperQ (endpointSmall24Argument k q)

theorem endpointJoint24_sound {k a q : ℚ}
    (hk : 0 < k) (ha : 0 ≤ a) (hgap : q*k^2 < 1)
    (hdom : roundUpQ (endpointJoint24Argument k a q) < 26) :
    SingularValueBounds.KL.upperJointPrefactor (q : ℝ) a k ≤
      (endpointJoint24Q k a q : ℝ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hl := (roundedLogConditions (show 0 < 1-q*k^2 by linarith)).sound.1
  norm_num only [Rat.cast_sub, Rat.cast_one, Rat.cast_mul, Rat.cast_pow] at hl
  have hc : 0 ≤ (a : ℝ)/(2*(k : ℝ)^3) := by positivity
  have hs := mul_le_mul_of_nonneg_left (neg_le_neg hl) hc
  unfold endpointJoint24Q
  apply (Real.exp_le_exp.mpr ?_).trans (generalMeanExpUpper_sound hdom)
  unfold SingularValueBounds.KL.upperJointCost endpointJoint24Argument
  push_cast
  convert! add_le_add_left hs ((q : ℝ)/2 -
    (a : ℝ)*(q : ℝ)*(k : ℝ)^2/(2*(k : ℝ)^3)) using 1 <;> ring

theorem endpointSmall24_sound {k q : ℚ}
    (hk : 0 < k) (hgap : q*k^2 < 1)
    (hdom : roundUpQ (endpointSmall24Argument k q) < 26) :
    Real.exp (-Real.log (1-(q : ℝ)*(k : ℝ)^2)/(2*(k : ℝ)^2)) ≤
      (endpointSmall24Q k q : ℝ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hl := (roundedLogConditions (show 0 < 1-q*k^2 by linarith)).sound.1
  norm_num only [Rat.cast_sub, Rat.cast_one, Rat.cast_mul, Rat.cast_pow] at hl
  unfold endpointSmall24Q
  apply (Real.exp_le_exp.mpr ?_).trans (generalMeanExpUpper_sound hdom)
  unfold endpointSmall24Argument
  push_cast
  exact div_le_div_of_nonneg_right (neg_le_neg hl) (by positivity)

end
end SingularValueBounds.KL.Certificates
