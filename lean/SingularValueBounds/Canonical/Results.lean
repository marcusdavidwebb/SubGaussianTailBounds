import SingularValueBounds.Canonical.General
import SingularValueBounds.Canonical.Unit
import SingularValueBounds.Canonical.Monotonicity
import SingularValueBounds.Canonical.AcceptedConstants

/-! Public interface for the single current formalization. The accepted snapshot
records each jointly proved quartet; the trusted verifier supplies the independent
previous ceiling. Baseline corollaries use the same proof by monotonicity. -/

namespace SubGaussian.Current
universe u
noncomputable section

def generalAlpha : ℝ := SubGaussian.AcceptedConstants.generalAlpha
def generalBeta : ℝ := SubGaussian.AcceptedConstants.generalBeta
def generalGamma : ℝ := SubGaussian.AcceptedConstants.generalGamma
def generalDelta : ℝ := SubGaussian.AcceptedConstants.generalDelta

theorem general : SubGaussian.GeneralSingularValueTailBound.{u} generalAlpha generalBeta generalGamma generalDelta :=
  SingularValueBounds.Canonical.general_baseline.{u}

theorem general_recorded : (generalAlpha, generalBeta, generalGamma, generalDelta) =
    (SubGaussian.AcceptedConstants.generalAlpha, SubGaussian.AcceptedConstants.generalBeta, SubGaussian.AcceptedConstants.generalGamma, SubGaussian.AcceptedConstants.generalDelta) := rfl

theorem general_baseline_alpha : generalAlpha ≤ 3.84 := le_rfl
theorem general_baseline_beta : generalBeta ≤ 1.58 := le_rfl
theorem general_baseline_gamma : generalGamma ≤ 2.35 := le_rfl
theorem general_baseline_delta : generalDelta ≤ 1.5 := le_rfl

theorem general_current_alpha : generalAlpha ≤ 3.84 := le_rfl
theorem general_current_beta : generalBeta ≤ 1.58 := le_rfl
theorem general_current_gamma : generalGamma ≤ 2.35 := le_rfl
theorem general_current_delta : generalDelta ≤ 1.5 := le_rfl

theorem general_baseline : SubGaussian.GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.5 :=
  general.{u}.mono general_baseline_alpha general_baseline_beta general_baseline_gamma general_baseline_delta

def unitAlpha : ℝ := SubGaussian.AcceptedConstants.unitAlpha
def unitBeta : ℝ := SubGaussian.AcceptedConstants.unitBeta
def unitGamma : ℝ := SubGaussian.AcceptedConstants.unitGamma
def unitDelta : ℝ := SubGaussian.AcceptedConstants.unitDelta

theorem unit : SubGaussian.UnitSingularValueTailBound.{u} unitAlpha unitBeta unitGamma unitDelta :=
  SingularValueBounds.Canonical.unit_baseline.{u}

theorem unit_recorded : (unitAlpha, unitBeta, unitGamma, unitDelta) =
    (SubGaussian.AcceptedConstants.unitAlpha, SubGaussian.AcceptedConstants.unitBeta, SubGaussian.AcceptedConstants.unitGamma, SubGaussian.AcceptedConstants.unitDelta) := rfl

theorem unit_baseline_alpha : unitAlpha ≤ 1.32 := le_rfl
theorem unit_baseline_beta : unitBeta ≤ 1.12 := le_rfl
theorem unit_baseline_gamma : unitGamma ≤ 2.32 := le_rfl
theorem unit_baseline_delta : unitDelta ≤ (Real.sqrt 2) := le_rfl

theorem unit_current_alpha : unitAlpha ≤ 1.32 := le_rfl
theorem unit_current_beta : unitBeta ≤ 1.12 := le_rfl
theorem unit_current_gamma : unitGamma ≤ 2.32 := le_rfl
theorem unit_current_delta : unitDelta ≤ (Real.sqrt 2) := le_rfl

theorem unit_baseline : SubGaussian.UnitSingularValueTailBound.{u} 1.32 1.12 2.32 (Real.sqrt 2) :=
  unit.{u}.mono unit_baseline_alpha unit_baseline_beta unit_baseline_gamma unit_baseline_delta

end
end SubGaussian.Current
