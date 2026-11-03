import SingularValueBounds.KL.Upper.EndpointMeanData
import SingularValueBounds.KL.Upper.EndpointEntropyRunData
import SingularValueBounds.KL.Upper.EntropyAnalyticRunNumerics
import SingularValueBounds.KL.Upper.EndpointAnalyticPrefactor
import SingularValueBounds.KL.Upper.LogdetCertificates
import SingularValueBounds.KL.Upper.ComparisonLogdet

/-! # The finite endpoint upper-mean conditions

All fields of the numerical predicate below are finite rational inequalities
or polynomial coefficient identities. The endpoint entropy is integrated over
finite rational rate intervals, with no uniform Riemann grid or decay transcript.
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

def endpointRunPointQ (j0 j : ℕ) : ℚ := ((max j0 (j-1) : ℕ):ℚ)/200

def endpointRunWeightQ (j0 : ℕ) (r : EndpointRateRun) : ℚ :=
  entropyExpWeightUpperQ ((j0 : ℚ)/200) ((r.rate : ℚ)/100)
    (endpointRunPointQ j0 r.start) (endpointRunPointQ j0 r.stop)

def endpointAnalyticTailQ (j0 : ℕ) : ℚ :=
  roundUpQ ((31623/10000)*primitiveUpperQ ((j0 : ℚ)/200) (9/10) (endpointRunPointQ j0 8000))

def endpointMeanNumericCorner (ki : Fin 60) (ai : Fin 42) (h : Fin 4) : ℚ :=
  (logRoundedQ ((endpointMeanCutoff ki ai : ℚ)/200)).2+
    endpointAnalyticTailQ (endpointMeanCutoff ki ai)+
    ((endpointMeanRuns ki ai).map (fun r => endpointRunWeightQ (endpointMeanCutoff ki ai) r*
      endpointJoint24Q (endpointMeanCornerK ki ai h) (endpointMeanCornerA ki ai h)
        ((r.rate : ℚ)/100))).sum

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
def endpointSmallNumeric (i : Fin 50) : ℚ :=
  (logRoundedQ ((endpointSmallCutoff i : ℚ)/200)).2+
    endpointAnalyticTailQ (endpointSmallCutoff i)+
    ((endpointSmallRuns i).map (fun r => endpointRunWeightQ (endpointSmallCutoff i) r*
      endpointSmall24Q (endpointSmallK i) ((r.rate : ℚ)/100))).sum

def endpointSmallTarget (i : Fin 50) : ℚ :=
  239/200+(9/20)*(i.val : ℚ)^2/200^2+(i.val : ℚ)^4/(2*200^4)

/-- Every interval lies above the entropy cutoff and has an admissible tail rate.
The last inequality is the cap condition at its right endpoint. -/
def EndpointRunConditions (j0 : ℕ) (k : ℚ) (r : EndpointRateRun) : Prop :=
  j0 ≤ r.start ∧ r.start < r.stop ∧ r.stop ≤ 8000 ∧
  90 ≤ r.rate ∧ r.rate ≤ 200 ∧
  ((r.rate : ℚ)/100)*k^2 < 1 ∧
  endpointRunPointQ j0 r.stop*k*((r.rate : ℚ)/100-1) ≤ 58/25

def EndpointJointNumericalConditions (ki : Fin 60) (ai : Fin 42) : Prop :=
  EndpointRunsCover (endpointMeanCutoff ki ai) 8000 (endpointMeanRuns ki ai) ∧
  (∀ r ∈ endpointMeanRuns ki ai, EndpointRunConditions (endpointMeanCutoff ki ai)
    (endpointMeanBox ki ai).top r) ∧
  (∀ h : Fin 4, ∀ r ∈ endpointMeanRuns ki ai,
    roundUpQ (endpointJoint24Argument (endpointMeanCornerK ki ai h)
      (endpointMeanCornerA ki ai h) ((r.rate : ℚ)/100)) < 26) ∧
  (∀ h : Fin 4, endpointMeanNumericCorner ki ai h ≤ endpointMeanCorner ki ai h)

def EndpointSmallNumericalConditions (i : Fin 50) : Prop :=
  EndpointRunsCover (endpointSmallCutoff i) 8000 (endpointSmallRuns i) ∧
  (∀ r ∈ endpointSmallRuns i, EndpointRunConditions (endpointSmallCutoff i) (endpointSmallK i) r) ∧
  (∀ r ∈ endpointSmallRuns i,
    roundUpQ (endpointSmall24Argument (endpointSmallK i) ((r.rate : ℚ)/100)) < 26) ∧
  endpointSmallNumeric i ≤ endpointSmallTarget i

theorem endpointRunPointQ_mono (j0 : ℕ) : Monotone (endpointRunPointQ j0) := by
  intro i j hij
  unfold endpointRunPointQ
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℚ)≤200)
  exact_mod_cast max_le_max le_rfl (Nat.sub_le_sub_right hij 1)

theorem endpointRunPointQ_above (j0 j : ℕ) : (j0:ℚ)/200≤endpointRunPointQ j0 j := by
  unfold endpointRunPointQ
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℚ)≤200)
  exact_mod_cast (le_max_left j0 (j-1))

theorem endpointRunPointQ_cast (j0 j : ℕ) :
    (endpointRunPointQ j0 j:ℝ)=endpointRunPoint j0 j := by
  simp [endpointRunPointQ,endpointRunPoint]

theorem endpointRunWeightQ_nonneg {j0 : ℕ} (hj0 : 0<j0) {r : EndpointRateRun}
    (hr : r.start≤r.stop) (hq : 0<r.rate) : 0≤endpointRunWeightQ j0 r := by
  apply entropyExpWeightUpperQ_nonneg (by positivity)
    (endpointRunPointQ_above _ _) (endpointRunPointQ_mono _ hr) (by positivity)

structure EndpointMeanCertificateConditions : Prop where
  aGrid : endpointMeanAPoint 0=0 ∧ endpointMeanAPoint 42=1 ∧
    ∀ai : Fin 42,endpointMeanAPoint ⟨ai.val,by omega⟩<endpointMeanAPoint ⟨ai.val+1,by omega⟩
  quarterNondegenerate : ∀ai : Fin 42,(1/4 : ℚ)^3≠endpointMeanAPoint ⟨ai.val+1,by omega⟩
  smallCutoff : ∀i : Fin 50,0<endpointSmallCutoff i ∧ endpointSmallCutoff i≤8000
  smallNumerical : ∀i : Fin 50,EndpointSmallNumericalConditions i
  smallTotal : ∀i : Fin 50,endpointSmallTarget i+13/12-1/80≤58/25
  jointCutoff : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    0<endpointMeanCutoff ki ai ∧ endpointMeanCutoff ki ai≤8000
  jointBoxes : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    0≤(endpointMeanBox ki ai).left ∧ 0<(endpointMeanBox ki ai).bottom ∧
      (endpointMeanBox ki ai).bottom<(endpointMeanBox ki ai).top ∧ (endpointMeanBox ki ai).top≤1
  jointNumerical : ∀ki : Fin 60,∀ai : Fin 42,endpointMeanActive ki ai →
    EndpointJointNumericalConditions ki ai
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
