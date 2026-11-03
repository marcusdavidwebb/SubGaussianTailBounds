import MainTheoremStatement
import SingularValueBounds.Canonical.Results

/-!
The two propositions checked by the `SingularValueBounds.CheckStatements` Lake
target. Their definitions and hypotheses are in `MainTheoremStatement.lean`;
the proof terms below are the project's canonical results. The decimal literals
are exact real numbers, and `u` allows any sample-space universe.

Lean checks these literal types against the results, whose coefficients come
from `Canonical/Constants.lean`; a change that makes them disagree fails here.
-/

universe u

namespace SubGaussian.StatementChecks

theorem general : GeneralSingularValueTailBound.{u} 3.84 1.58 2.35 1.50 :=
  Current.general.{u}

theorem unit : UnitSingularValueTailBound.{u} 1.32 1.12 2.32 1.42 :=
  Current.unit.{u}

end SubGaussian.StatementChecks
