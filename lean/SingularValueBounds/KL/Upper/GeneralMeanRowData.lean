import SingularValueBounds.KL.Upper.RoundedAlgorithm

/-! Pure rational row parameters, the prefactor input, and the uniform grid.
The analytic error and soundness rules remain in `GeneralMeanNumerics`. -/
namespace SingularValueBounds.KL.Certificates
noncomputable section

structure GeneralMeanRow where
  klo : ℚ
  khi : ℚ
  alo : ℚ
  ahi : ℚ
  J : ℚ
  q : ℚ
  c : ℚ
  C : ℚ
  majorant : Fin 8
  deriving DecidableEq

def GeneralMeanRow.prefactorArgument (r : GeneralMeanRow) : ℚ :=
  r.q/2+r.ahi/(2*r.khi^3)*(-(logRoundedQ (1-r.q*r.khi^2)).1-r.q*r.khi^2)+
    r.C/(2*r.khi^2)

def generalMeanGrid (j : ℕ) : ℚ := (j+40:ℚ)/40

end
end SingularValueBounds.KL.Certificates
