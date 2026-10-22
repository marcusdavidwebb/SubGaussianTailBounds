import SingularValueBounds.KL.Lower.PlateauGeometry

/-! # Finite rational certificates for the whole-interval plateau costs
A direct Taylor/Bernstein certificate proves the same final cost inequality
on each complete spectral range, including all endpoints. -/
open Polynomial Set
open scoped Polynomial BigOperators
namespace SingularValueBounds.KL.LowerCertificates
open SingularValueBounds.KL.Certificates
noncomputable section

def plateauCostU (i : Fin 2) : ℚ := if i=0 then 1207/1000 else 6/5
def plateauCostW (i : Fin 2) : ℚ := if i=0 then 26/25 else 21/20
def plateauCostC (i : Fin 2) : ℚ := if i=0 then 17/10 else 19/10
def plateauCostLo (i : Fin 2) : ℚ := if i=0 then 71/100 else 147/200
def plateauCostHi (i : Fin 2) : ℚ := if i=0 then 147/200 else 1

def plateauCostA (i : Fin 2) : ℚ[X] :=
  if i=0 then X+C ((7/10)/(2*(347/500)))*(1+C ((347/500)^2)-X^2) else C (74/55)
def plateauCostV (i : Fin 2) : ℚ[X] :=
  if i=0 then C (1631/1000)+C ((167/100-1631/1000)/(1211/1000-6/5))*(plateauCostA i-C (6/5))
  else C (27/16)

def plateauCostD (i : Fin 2) : ℚ[X] :=
  1-C (plateauCostU i)*(X+plateauCostA i*X^2-C (plateauCostC i)*X^3)
def plateauCostE (i : Fin 2) : ℚ[X] :=
  plateauCostV i*(1-X^2)-C 4+C (plateauCostW i/2)-C (plateauCostU i/2)*X+C (plateauCostW i)*X^4

def plateauCostMargin (i : Fin 2) : ℚ[X] :=
  plateauCostD i*polynomialExpTaylor 24 (-C 2*plateauCostE i)-
    C (400/(9*(plateauCostW i)^2*((plateauCostU i)*(4137/1000)-4)^2))

def PlateauCostCertificateConditions : Prop :=
  ∀ i : Fin 2,
    IntervalCertificate (-plateauCostE i) (plateauCostLo i) (plateauCostHi i) 4
      (bernsteinCoefficients ((-plateauCostE i).comp
        (affine (plateauCostLo i) (plateauCostHi i-plateauCostLo i))) 4) ∧
    IntervalCertificate (plateauCostD i-C (1/1000000)) (plateauCostLo i) (plateauCostHi i) 4
      (bernsteinCoefficients ((plateauCostD i-C (1/1000000)).comp
        (affine (plateauCostLo i) (plateauCostHi i-plateauCostLo i))) 4) ∧
    IntervalCertificate (plateauCostMargin i) (plateauCostLo i) (plateauCostHi i) 100
      (bernsteinCoefficients ((plateauCostMargin i).comp
        (affine (plateauCostLo i) (plateauCostHi i-plateauCostLo i))) 100)

end
end SingularValueBounds.KL.LowerCertificates
