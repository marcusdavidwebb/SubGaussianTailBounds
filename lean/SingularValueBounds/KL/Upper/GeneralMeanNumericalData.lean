import SingularValueBounds.KL.Upper.GeneralMeanExp
import SingularValueBounds.KL.Upper.GeneralMeanRowData
import SingularValueBounds.KL.Upper.RoundedAlgorithmSoundness

/-! Rational data and sufficient conditions for the general upper-mean bounds.
Finite certificates import this interface without the probability and matrix
arguments used to interpret it in `GeneralMeanNumerics`.
-/
namespace SingularValueBounds.KL.Certificates
noncomputable section
set_option maxHeartbeats 1800000

def resolventLowerQ (x : ℚ) : ℚ := (x^2+8*x+11)/(x^3+9*x^2+18*x+6)
def resolventUpperQ (x : ℚ) : ℚ :=
  (x^3+11*x^2+26*x+6)/(x*(x^3+12*x^2+36*x+24))
def GeneralMeanRow.cutoff (r : GeneralMeanRow) : ℚ := (47/20)/(r.khi*(r.q-1))
def GeneralMeanRow.prefactor (r : GeneralMeanRow) : ℚ := generalMeanExpUpperQ r.prefactorArgument
def GeneralMeanRow.rawError (r : GeneralMeanRow) (L : ℚ) : ℚ :=
  (2*r.prefactor/r.q)*generalMeanExpUpperQ (-2-(r.q*r.c/2-2)*L)*
      (1+resolventUpperQ (r.q*r.c*L/2))+
    if 1<r.q then
      r.prefactor*generalMeanExpUpperQ (-2-(r.q*r.cutoff/2-2)*L)*
        ((2-2/r.q)*(1+(logRoundedQ (r.cutoff/r.c)).2)+
          2*resolventUpperQ (r.cutoff*L/2)-(2/r.q)*resolventLowerQ (r.q*r.cutoff*L/2))
    else 0
/-- Six decimal places suffice for the final scalar entropy margins. -/
def GeneralMeanRow.error (r : GeneralMeanRow) (L : ℚ) : ℚ :=
  -(⌊-(r.rawError L*1000000)⌋ : ℚ)/1000000

theorem GeneralMeanRow.rawError_le_error (r : GeneralMeanRow) (L : ℚ) :
    r.rawError L ≤ r.error L := by
  unfold GeneralMeanRow.error
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 1000000)]
  have h := Int.floor_le (-(r.rawError L*1000000))
  linarith
def GeneralMeanRow.slope (r : GeneralMeanRow) (j k : ℕ) : ℚ :=
  (r.error (generalMeanGrid k)-r.error (generalMeanGrid j))/
    (generalMeanGrid k-generalMeanGrid j)
def GeneralMeanRow.criticalRate (r : GeneralMeanRow) (j k : ℕ) : ℚ := 47/20-2-r.slope j k
def GeneralMeanRow.criticalPoint (r : GeneralMeanRow) (j k : ℕ) : ℚ :=
  min (generalMeanGrid k) (max (generalMeanGrid j) (1/r.criticalRate j k))

/-- Scalar domains and a finite partition with sufficient rational margins.
No numerical obligation is imposed at unused interior grid points. -/
structure GeneralMeanNumericalConditions (r : GeneralMeanRow) : Prop where
  shape : 0<r.khi
  third : 0≤r.ahi
  rate : 0<r.q
  cutoff : 0<r.c
  gap : r.q*r.khi^2<1
  correction : 0≤r.C
  decay : 2<r.q*r.c/2
  continuation : 1<r.q → r.c≤r.cutoff ∧ 2<r.q*r.cutoff/2
  prefactorLog : RoundedLogConditions (1-r.q*r.khi^2)
  prefactorExp : roundUpQ r.prefactorArgument < 26
  continuationLog : 1<r.q → RoundedLogConditions (r.cutoff/r.c)
  nodeExp : ∀j : Fin 121,
    roundUpQ (-2-(r.q*r.c/2-2)*generalMeanGrid j.val) < 26
  nodeContinuationExp : 1<r.q → ∀j : Fin 121,
    roundUpQ (-2-(r.q*r.cutoff/2-2)*generalMeanGrid j.val) < 26
  nodeRound : ∀j : Fin 121,r.rawError (generalMeanGrid j.val)≤r.error (generalMeanGrid j.val)
  intervals : ∃ ps : List (Fin 121 × Fin 121),
    (∀ p ∈ ps, p.1 < p.2 ∧ 0 < r.criticalRate p.1.val p.2.val ∧
      RoundedLogConditions (r.c*r.criticalPoint p.1.val p.2.val) ∧
      0≤2+r.criticalRate p.1.val p.2.val*r.criticalPoint p.1.val p.2.val-
        (logRoundedQ (r.c*r.criticalPoint p.1.val p.2.val)).2-r.J/2-
        r.error (generalMeanGrid p.1.val)+r.slope p.1.val p.2.val*generalMeanGrid p.1.val) ∧
    ∀ j : Fin 120, ∃ p ∈ ps, p.1.val ≤ j.val ∧ j.val < p.2.val
  finalLog : RoundedLogConditions (4*r.c)
  finalMargin : 0≤2+4*(47/20-2)-(logRoundedQ (4*r.c)).2-r.J/2-r.error 4

end
end SingularValueBounds.KL.Certificates
