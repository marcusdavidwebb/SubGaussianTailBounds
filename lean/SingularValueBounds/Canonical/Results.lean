import SingularValueBounds.Canonical.General
import SingularValueBounds.Canonical.Unit
import SingularValueBounds.Canonical.Constants

/-! The two complete results. The canonical root defines their propositions;
`Constants` supplies the published exact rational coefficients. -/
namespace SubGaussian.Current
open SubGaussian.Constants
universe u

theorem general : GeneralSingularValueTailBound.{u}
    generalAlpha generalBeta generalGamma generalDelta :=
  SingularValueBounds.Canonical.general_baseline.{u}

theorem unit : UnitSingularValueTailBound.{u}
    unitAlpha unitBeta unitGamma unitDelta :=
  SingularValueBounds.Canonical.unit_baseline.{u}

end SubGaussian.Current
