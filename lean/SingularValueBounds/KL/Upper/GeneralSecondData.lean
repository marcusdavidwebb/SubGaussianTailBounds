import SingularValueBounds.KL.Certificates.Enclosures

/-! # Finite rational witnesses for the general upper second moment
Every condition below is a bounded family of rational comparisons. -/
open scoped BigOperators
namespace SingularValueBounds.KL.UpperSecond
open SingularValueBounds.KL.Certificates
open SingularValueBounds.KL.Certificates.NumericalCertificateConditions
noncomputable section

def secondUpQ (x : ℚ) : ℚ := (⌈x*10^12⌉:ℚ)/10^12
def secondDownQ (x : ℚ) : ℚ := (⌊x*10^12⌋:ℚ)/10^12
def secondExpUpperQ (x : ℚ) : ℚ :=
  secondUpQ (if 0 ≤ x then expTaylorUpperQ 48 x else 1/expTaylorQ 48 (-x))
def secondExpLowerQ (x : ℚ) : ℚ :=
  secondDownQ (if 0 ≤ x then expTaylorQ 48 x else 1/expTaylorUpperQ 48 (-x))
def secondLogCount (x : ℚ) : ℕ := if 8 ≤ x then 3 else if 4 ≤ x then 2 else if 2 ≤ x then 1 else 0
def secondLogReduced (x : ℚ) : ℚ := x/(2:ℚ)^(secondLogCount x)
def secondLogLowerQ (x : ℚ) : ℚ :=
  let r := secondLogReduced x
  secondDownQ (logTaylorQ 24 ((r-1)/(r+1))+(secondLogCount x:ℚ)*logTaylorQ 24 (1/3))
def secondCoshLowerQ (x : ℚ) : ℚ := (secondExpLowerQ x+secondExpLowerQ (-x))/2-1
def secondExclusionQ (m E x : ℚ) : ℚ :=
  m*secondLogLowerQ (1+secondCoshLowerQ x/m)-E*x^2/2

def secondRarePQ (i : Fin 3) : ℚ := if i=0 then 91/2000 else if i=1 then 7/160 else 19/500
def secondRareAQ (i : Fin 3) : ℚ := if i=0 then 947/100 else if i=1 then 239/25 else 10
def secondRareZQ (i : Fin 3) : ℚ := if i=0 then (47/50)^4+(1-(47/50)^2)^2
  else if i=1 then (19/20)^4+(1-(19/20)^2)^2 else 1

def secondRarePolyQ (i : Fin 3) (d : ℚ) : ℚ :=
  (secondRareAQ i+6*d)^2/2+(50/23)*(secondRareAQ i+6*d)+(50/23)^2

def secondCellLo (j : Fin 334) : ℚ := (j.val+376:ℚ)/1000
def secondCellHi (j : Fin 334) : ℚ := (j.val+377:ℚ)/1000
def secondCellDLo (j : Fin 334) : ℚ := (secondCellLo j)^4
def secondCellDHi (j : Fin 334) : ℚ := (secondCellHi j)^4
def secondCellE (j : Fin 334) : ℚ := secondExpUpperQ (2*secondCellDHi j)
def secondCellM (j : Fin 334) : ℚ :=
  let y := secondCellHi j
  secondUpQ ((3+(9/2)*y^2-(21/10)*y^4-(4/5)*y^6)*secondCellE j*(1+y^4))
def secondCellX (j : Fin 334) : ℚ :=
  let y := secondCellHi j
  (⌊20*y*(29/5+3*y^2)+1/2⌋:ℚ)/20

def secondSmallUpperQ (i : Fin 3) : ℚ :=
  4*(1+2*secondRareZQ i)/6+secondRarePQ i*secondRarePolyQ i 0-
    secondExpLowerQ (-1/25)/(2*(51/50))
def secondCellUpperQ (j : Fin 334) (i : Fin 3) : ℚ :=
  let dl := secondCellDLo j
  let dh := secondCellDHi j
  secondCellM j*secondExpUpperQ (-2*dl)*(1+2*secondRareZQ i)/(6*(1+dl))+
    secondRarePQ i*secondExpUpperQ (-(19/25)*dl)*secondRarePolyQ i dl/(1+dl)-
      secondExpLowerQ (-2*dh)/(2*(1+dh))

structure FourthExclusionCertificate (m E x : ℚ) : Prop where
  m_pos : 0 < m
  x_pos : 0 < x
  x_domain : x < 50
  cosh_nonneg : 0 ≤ secondCoshLowerQ x
  exclusion : 0 < secondExclusionQ m E x

/-- Exactly the finite scalar families checked in the Python companion. -/
def GeneralSecondCertificateConditions : Prop :=
  FourthExclusionCertificate 4 (secondExpUpperQ (1/25)) (5/2) ∧
  0 ≤ secondExpLowerQ (-1/25) ∧
  (∀ i : Fin 3, secondSmallUpperQ i < 9/2) ∧
  (∀ j : Fin 334,
    0 ≤ secondCellDLo j ∧ secondCellDLo j ≤ secondCellDHi j ∧ secondCellDHi j < 1 ∧
    2*secondCellDHi j < 50 ∧ 0 ≤ secondExpUpperQ (-2*secondCellDLo j) ∧
    0 ≤ secondExpLowerQ (-2*secondCellDHi j) ∧
    FourthExclusionCertificate (secondCellM j) (secondCellE j) (secondCellX j)) ∧
  (∀ j : Fin 334, ∀ i : Fin 3, secondCellUpperQ j i < 9/2)

end
end SingularValueBounds.KL.UpperSecond
