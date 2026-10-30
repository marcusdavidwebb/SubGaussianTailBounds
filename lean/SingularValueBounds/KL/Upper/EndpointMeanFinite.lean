import SingularValueBounds.KL.Upper.EndpointMeanData
import SingularValueBounds.KL.Upper.EndpointRoundedEval
import SingularValueBounds.KL.Upper.LogdetCertificates
import SingularValueBounds.KL.Upper.ComparisonLogdet

/-! # The finite endpoint upper-mean conditions

All fields of the numerical predicate below are finite rational inequalities
or polynomial coefficient identities. They refer to the actual 50 intervals,
837 clipped rectangles, computed rounded sums and selected determinant tests.
-/
open Polynomial Set
open scoped Polynomial BigOperators
namespace SingularValueBounds.KL.Certificates
noncomputable section
set_option maxHeartbeats 2000000

def endpointMeanBox (ki : Fin 60) (ai : Fin 42) : RationalBox :=
  let kl : ℚ := (ki.val+20 : ℚ)/80
  ⟨max (endpointMeanAPoint ⟨ai.val,by omega⟩) (kl^3),
    endpointMeanAPoint ⟨ai.val+1,by omega⟩,kl,(ki.val+21 : ℚ)/80⟩

def endpointMeanActive (ki : Fin 60) (ai : Fin 42) : Prop :=
  let b := endpointMeanBox ki ai
  b.left<b.right ∧ b.left≤b.top

def endpointMeanCutoff (ki : Fin 60) (ai : Fin 42) : ℕ :=
  (endpointMeanCornerData ki.val ai.val).2.2

def endpointMeanChoice (ki : Fin 60) (ai : Fin 42) : Fin 7 :=
  (endpointMeanCornerData ki.val ai.val).2.1

def endpointMeanCorner (ki : Fin 60) (ai : Fin 42) : Fin 4 → ℚ :=
  let p := (endpointMeanCornerData ki.val ai.val).1
  ![p.1,p.2.1,p.2.2.1,p.2.2.2]

def endpointMeanCornerA (ki : Fin 60) (ai : Fin 42) (h : Fin 4) : ℚ :=
  if h=0 ∨ h=2 then (endpointMeanBox ki ai).left else (endpointMeanBox ki ai).right
def endpointMeanCornerK (ki : Fin 60) (ai : Fin 42) (h : Fin 4) : ℚ :=
  if h=0 ∨ h=1 then (endpointMeanBox ki ai).bottom else (endpointMeanBox ki ai).top

def endpointMeanRate (ki : Fin 60) (ai : Fin 42) (j : ℕ) : ℕ :=
  let b := endpointMeanBox ki ai
  let k := (b.bottom+b.top)/2
  let a := (b.left+b.right)/2
  let u := (j : ℚ)/200
  let opt : ℤ := ⌊100*(u-1)/(k*a+k^2*(u-1))⌋
  let margin : ℤ := 100+⌊100*(58/25)/(u*b.top)⌋
  let spectral : ℤ := -⌊-(100/b.top^2)⌋-1
  (max 90 (min 200 (min opt (min margin spectral)))).toNat

def endpointMeanNumericCorner (ki : Fin 60) (ai : Fin 42) (h : Fin 4) : ℚ :=
  entropyGridBoundQ (endpointMeanCutoff ki ai)
    (fun j => endpointJointPrefactorQ (endpointMeanCornerK ki ai h)
      (endpointMeanCornerA ki ai h) ((endpointMeanRate ki ai j : ℚ)/100)*
        endpointDecayQ (endpointMeanRate ki ai j) j) (endpointDecayQ 90 8000)

def endpointMeanBilinearQ (ki : Fin 60) (ai : Fin 42) : Polynomial (Polynomial ℚ) :=
  let b := endpointMeanBox ki ai
  let D := endpointMeanCorner ki ai
  let ac := (D 1-D 0)/(b.right-b.left)
  let kc := (D 2-D 0)/(b.top-b.bottom)
  let cross := (D 3-D 2-D 1+D 0)/((b.right-b.left)*(b.top-b.bottom))
  C (C (D 0-ac*b.left-kc*b.bottom+cross*b.left*b.bottom))+
    C (C (ac-cross*b.bottom))*C X+C (C (kc-cross*b.left))*X+C (C cross)*C X*X

def endpointMeanMajorantIndex (h : Fin 7) : Fin 6 :=
  match h.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | _ => 0

def endpointMeanJ0Q : Polynomial (Polynomial ℚ) :=
  C (-2*X+C (671/100)*(1-X^2-X^2*(1-X)^2))

def endpointMeanTestQ (ki : Fin 60) (ai : Fin 42) : Polynomial (Polynomial ℚ) :=
  let base := C (C (58/25))-endpointMeanBilinearQ ki ai
  let h := endpointMeanChoice ki ai
  let i := endpointMeanMajorantIndex h
  if h=3 then base-C (C (1/2))*endpointMeanJ0Q else
    (base-C (C (1/2))*C (majorantBQ i)+C (C (1/2))*majorantHQ i)*padeDQ comparisonZQ-
      C (C (1/2))*padeNQ comparisonZQ

def endpointSmallK (i : Fin 50) : ℚ := (i.val+1 : ℚ)/200
def endpointSmallQ (h : Fin 23) : ℕ := 90+5*h.val

def endpointSmallBoundTerm (i : Fin 50) (j : ℕ) (h : Fin 23) : ℚ :=
  let q : ℚ := (endpointSmallQ h : ℚ)/100
  if (j : ℚ)/200*endpointSmallK i*(q-1)≤58/25 then
    roundUpQ (endpointSmallPrefactorQ (endpointSmallK i) q*endpointDecayQ (endpointSmallQ h) j)
  else 1

def endpointSmallBound (i : Fin 50) (j : ℕ) : ℚ :=
  min 1 (Finset.univ.inf' Finset.univ_nonempty (endpointSmallBoundTerm i j))

def endpointSmallTarget (i : Fin 50) : ℚ :=
  239/200+(9/20)*(i.val : ℚ)^2/200^2+(i.val : ℚ)^4/(2*200^4)

structure EndpointMeanCertificateConditions : Prop where
  gridLogs : ∀j : ℕ,j∈Finset.Icc 1 8001 → RoundedLogConditions ((j : ℚ)/200)
  decays : ∀qi∈Finset.Icc 90 200,EndpointDecayConditions qi
  aGrid : endpointMeanAPoint 0=0 ∧ endpointMeanAPoint 42=1 ∧
    ∀ai : Fin 42,endpointMeanAPoint ⟨ai.val,by omega⟩<endpointMeanAPoint ⟨ai.val+1,by omega⟩
  quarterNondegenerate : ∀ai : Fin 42,(1/4 : ℚ)^3≠endpointMeanAPoint ⟨ai.val+1,by omega⟩
  smallCutoff : ∀i : Fin 50,0<endpointSmallCutoff i ∧ endpointSmallCutoff i≤8000
  smallPrefactors : ∀i : Fin 50,∀h : Fin 23,
    EndpointSmallPrefactorConditions (endpointSmallK i) ((endpointSmallQ h : ℚ)/100)
  smallRounding : ∀i : Fin 50,∀j∈Finset.Ico (endpointSmallCutoff i) 8000,∀h : Fin 23,
    endpointSmallPrefactorQ (endpointSmallK i) ((endpointSmallQ h : ℚ)/100)*
      endpointDecayQ (endpointSmallQ h) j≤
        roundUpQ (endpointSmallPrefactorQ (endpointSmallK i) ((endpointSmallQ h : ℚ)/100)*
          endpointDecayQ (endpointSmallQ h) j)
  smallNumerical : ∀i : Fin 50,entropyGridBoundQ (endpointSmallCutoff i)
    (endpointSmallBound i) (endpointDecayQ 90 8000)≤endpointSmallTarget i
  smallTotal : ∀i : Fin 50,endpointSmallTarget i+13/12-1/80≤58/25
  jointCutoff : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    0<endpointMeanCutoff ki ai ∧ endpointMeanCutoff ki ai≤8000
  jointBoxes : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    0≤(endpointMeanBox ki ai).left ∧ 0<(endpointMeanBox ki ai).bottom ∧
      (endpointMeanBox ki ai).bottom<(endpointMeanBox ki ai).top ∧ (endpointMeanBox ki ai).top≤1
  jointRates : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    ∀j∈Finset.Ico (endpointMeanCutoff ki ai) 8000,
    let q : ℚ := (endpointMeanRate ki ai j : ℚ)/100
    90≤endpointMeanRate ki ai j ∧ endpointMeanRate ki ai j≤200 ∧
    q*(endpointMeanBox ki ai).top^2<1 ∧
    (j : ℚ)/200*(endpointMeanBox ki ai).top*(q-1)≤58/25
  jointPrefactors : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    ∀h : Fin 4,∀j∈Finset.Ico (endpointMeanCutoff ki ai) 8000,
    EndpointJointPrefactorConditions (endpointMeanCornerK ki ai h)
      (endpointMeanCornerA ki ai h) ((endpointMeanRate ki ai j : ℚ)/100)
  jointCorners : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    ∀h : Fin 4,endpointMeanNumericCorner ki ai h≤endpointMeanCorner ki ai h
  chosenDomain : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    let b := endpointMeanBox ki ai
    let h := endpointMeanChoice ki ai
    if h=3 then 5/6≤b.left else
      let i := endpointMeanMajorantIndex h
      (majorantBoxes i).left≤b.left ∧ b.right≤(majorantBoxes i).right ∧
        b.top≤(majorantBoxes i).top
  polynomialTests : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    ∃ n m, BoxCertificate (endpointMeanTestQ ki ai) n m (endpointMeanBox ki ai)

end
end SingularValueBounds.KL.Certificates
