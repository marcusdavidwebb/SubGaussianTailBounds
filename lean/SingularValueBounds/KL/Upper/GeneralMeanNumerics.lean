import SingularValueBounds.KL.Upper.GeneralMeanExp
import SingularValueBounds.KL.Upper.GeneralMeanRowData
import SingularValueBounds.KL.Upper.GeneralMeanError
import SingularValueBounds.KL.Upper.RoundedAlgorithmSoundness
import SingularValueBounds.KL.Upper.JointTail

/-! General upper-mean entropy bounds from adaptive convex chords.

The error is convex and decreasing for `L ≥ 1`. A chord between any two
certified nodes bounds the error throughout that interval; the logarithmic
part is then checked at its exact critical point. The finite partition may
therefore skip the many unnecessary nodes of a uniform fine grid. The final
node at `L = 4` also controls the unbounded range.
-/

open MeasureTheory Set
open scoped BigOperators
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

theorem GeneralMeanNumericalConditions.prefactor_sound {r : GeneralMeanRow}
    (h : GeneralMeanNumericalConditions r) :
    Real.exp (((r.C:ℝ)/(r.khi:ℝ)^2+upperJointCost r.q r.khi r.ahi)/2)≤
      (r.prefactor : ℝ) := by
  have hk : (0:ℝ)<r.khi := by exact_mod_cast h.shape
  have ha : (0:ℝ)≤r.ahi := by exact_mod_cast h.third
  have hl := h.prefactorLog.sound.1
  have he := generalMeanExpUpper_sound h.prefactorExp
  have hcoef : 0≤(r.ahi:ℝ)/(2*(r.khi:ℝ)^3) := by positivity
  have harg : ((r.C:ℝ)/(r.khi:ℝ)^2+upperJointCost r.q r.khi r.ahi)/2≤
      (r.prefactorArgument : ℝ) := by
    dsimp [GeneralMeanRow.prefactorArgument,upperJointCost]
    push_cast at hl ⊢
    have hm := mul_le_mul_of_nonneg_left hl hcoef
    ring_nf at hm ⊢
    linarith
  exact (Real.exp_le_exp.mpr harg).trans he

theorem resolvent_bounds_cast {x : ℚ} (hx : 0<x) :
    (resolventLowerQ x : ℝ)≤exponentialResolvent (x : ℝ) ∧
    exponentialResolvent (x : ℝ)≤(resolventUpperQ x : ℝ) := by
  have hh := exponentialResolvent_rational_bounds (by exact_mod_cast hx : (0:ℝ)<x)
  simpa only [resolventLowerQ,resolventUpperQ,Rat.cast_div,Rat.cast_add,
    Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using hh

theorem GeneralMeanNumericalConditions.prefactor_pos {r : GeneralMeanRow}
    (h : GeneralMeanNumericalConditions r) : (0:ℝ)<r.prefactor :=
  (Real.exp_pos _).trans_le h.prefactor_sound

theorem GeneralMeanNumericalConditions.node_sound {r : GeneralMeanRow}
    (h : GeneralMeanNumericalConditions r) (j : Fin 121) :
    generalMeanError r.prefactor r.q r.c r.cutoff (generalMeanGrid j.val)≤
      (r.error (generalMeanGrid j.val) : ℝ) := by
  have hA := h.prefactor_pos.le
  have hq : (0:ℝ)<r.q := by exact_mod_cast h.rate
  have hc : (0:ℝ)<r.c := by exact_mod_cast h.cutoff
  have hLj : (1:ℚ)≤generalMeanGrid j.val := by
    unfold generalMeanGrid
    have hj : (0:ℚ)≤j.val := by positivity
    linarith
  have hL : (1:ℝ)≤(generalMeanGrid j.val : ℝ) := by exact_mod_cast hLj
  have he := generalMeanExpUpper_sound (h.nodeExp j)
  push_cast at he
  have hI := (resolvent_bounds_cast (show 0<r.q*r.c*generalMeanGrid j.val/2 by
    have hLp : (0:ℚ)<generalMeanGrid j.val := lt_of_lt_of_le (by norm_num) hLj
    exact div_pos (mul_pos (mul_pos h.rate h.cutoff) hLp) (by norm_num))).2
  push_cast at hI
  have hR := generalMeanRemainder_bound hA hq hc hL he hI
  have hraw : generalMeanError r.prefactor r.q r.c r.cutoff (generalMeanGrid j.val)≤
      (r.rawError (generalMeanGrid j.val) : ℝ) := by
    by_cases hq1 : 1<r.q
    · have hq1r : (1:ℝ)<r.q := by exact_mod_cast hq1
      have hcs : (r.c:ℝ)≤r.cutoff := by exact_mod_cast (h.continuation hq1).1
      have hs : (0:ℚ)<r.cutoff := lt_of_lt_of_le h.cutoff (h.continuation hq1).1
      have hLp : (0:ℚ)<generalMeanGrid j.val := lt_of_lt_of_le (by norm_num) hLj
      have het := generalMeanExpUpper_sound (h.nodeContinuationExp hq1 j)
      have hlog := (h.continuationLog hq1).sound.2
      have hIt := (resolvent_bounds_cast (show 0<r.cutoff*generalMeanGrid j.val/2 by positivity)).2
      have hItq := (resolvent_bounds_cast (show 0<r.q*r.cutoff*generalMeanGrid j.val/2 by
        exact div_pos (mul_pos (mul_pos h.rate hs) hLp) (by norm_num))).1
      push_cast at het hlog hIt hItq
      have hT := generalMeanContinuation_bound hA hq1r hc hcs hL het hlog hIt hItq
      dsimp [generalMeanError,GeneralMeanRow.rawError]
      rw [if_pos hq1r,if_pos hq1]
      push_cast
      exact add_le_add hR hT
    · have hq1r : ¬(1:ℝ)<r.q := by exact_mod_cast hq1
      dsimp [generalMeanError,GeneralMeanRow.rawError]
      rw [if_neg hq1r,if_neg hq1]
      push_cast
      simpa only [add_zero] using hR
  exact hraw.trans (by exact_mod_cast h.nodeRound j)

theorem generalMeanGrid_cast (j : ℕ) :
    (generalMeanGrid j : ℝ)=((j : ℝ)+40)/40 := by
  simp only [generalMeanGrid,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat]

theorem GeneralMeanNumericalConditions.chord_sound {r : GeneralMeanRow}
    (h : GeneralMeanNumericalConditions r) (p : Fin 121 × Fin 121)
    (hp : p.1 < p.2) (hs : 0 < r.criticalRate p.1.val p.2.val)
    (hl : RoundedLogConditions (r.c*r.criticalPoint p.1.val p.2.val))
    (hmarg : 0≤2+r.criticalRate p.1.val p.2.val*r.criticalPoint p.1.val p.2.val-
      (logRoundedQ (r.c*r.criticalPoint p.1.val p.2.val)).2-r.J/2-
      r.error (generalMeanGrid p.1.val)+r.slope p.1.val p.2.val*generalMeanGrid p.1.val)
    {L : ℝ}
    (hL : L∈Icc (generalMeanGrid p.1.val : ℝ) (generalMeanGrid p.2.val : ℝ)) :
    2*L-2+Real.log ((r.c:ℝ)*L)+
      generalMeanError r.prefactor r.q r.c r.cutoff L+(r.J:ℝ)/2≤(47/20)*L := by
  have hc : (0:ℝ)<r.c := by exact_mod_cast h.cutoff
  have hq : (0:ℝ)<r.q := by exact_mod_cast h.rate
  have hqc : (2:ℝ)≤(r.q:ℝ)*(r.c:ℝ)/2 := by exact_mod_cast h.decay.le
  have hcont : (1:ℝ)<r.q → (r.c:ℝ)≤r.cutoff ∧ 2≤(r.q:ℝ)*(r.cutoff:ℝ)/2 := by
    intro hqr
    have hqq : (1:ℚ)<r.q := by exact_mod_cast hqr
    exact ⟨by exact_mod_cast (h.continuation hqq).1,
      by exact_mod_cast (h.continuation hqq).2.le⟩
  have hconv := (generalMeanError_convex_antitone h.prefactor_pos.le hq hc hqc hcont).1
  have hlo : (0:ℝ)<(generalMeanGrid p.1.val : ℝ) := by rw [generalMeanGrid_cast]; positivity
  have hgrid : (generalMeanGrid p.1.val : ℝ)<(generalMeanGrid p.2.val : ℝ) := by
    rw [generalMeanGrid_cast,generalMeanGrid_cast]
    have hh : (p.1.val : ℝ) < p.2.val := by exact_mod_cast hp
    linarith
  have hlo1 : (1:ℝ)≤(generalMeanGrid p.1.val : ℝ) := by
    rw [generalMeanGrid_cast]
    have hj : (0:ℝ)≤p.1.val := by positivity
    linarith
  have hconv' : ConvexOn ℝ
      (Icc (generalMeanGrid p.1.val:ℝ) (generalMeanGrid p.2.val:ℝ))
      (generalMeanError r.prefactor r.q r.c r.cutoff) :=
    hconv.subset (fun x hx => hlo1.trans hx.1) (convex_Icc _ _)
  let slope : ℝ := ((r.error (generalMeanGrid p.2.val):ℝ)-
    (r.error (generalMeanGrid p.1.val):ℝ))/
      ((generalMeanGrid p.2.val:ℝ)-(generalMeanGrid p.1.val:ℝ))
  have hslope : slope=(r.slope p.1.val p.2.val : ℝ) := by
    dsimp [slope,GeneralMeanRow.slope]
    push_cast
    rfl
  have hrate : (47/20:ℝ)-2-slope=(r.criticalRate p.1.val p.2.val:ℝ) := by
    rw [hslope]
    dsimp [GeneralMeanRow.criticalRate]
    push_cast
    rfl
  have hcritical : generalMeanCritical ((47/20:ℝ)-2-slope)
      (generalMeanGrid p.1.val) (generalMeanGrid p.2.val)=(r.criticalPoint p.1.val p.2.val:ℝ) := by
    rw [hrate]
    dsimp [generalMeanCritical,GeneralMeanRow.criticalPoint]
    push_cast
    rfl
  have hlog := (hl).sound.2
  push_cast at hlog
  have hm : (0:ℝ)≤2+(r.criticalRate p.1.val p.2.val:ℝ)*(r.criticalPoint p.1.val p.2.val:ℝ)-
      Real.log ((r.c:ℝ)*(r.criticalPoint p.1.val p.2.val:ℝ))-(r.J:ℝ)/2-
      (r.error (generalMeanGrid p.1.val):ℝ)+(r.slope p.1.val p.2.val:ℝ)*(generalMeanGrid p.1.val:ℝ) := by
    have hh : (0:ℝ)≤((2+r.criticalRate p.1.val p.2.val*r.criticalPoint p.1.val p.2.val-
      (logRoundedQ (r.c*r.criticalPoint p.1.val p.2.val)).2-r.J/2-r.error (generalMeanGrid p.1.val)+
      r.slope p.1.val p.2.val*generalMeanGrid p.1.val : ℚ):ℝ) := by exact_mod_cast hmarg
    push_cast at hh
    linarith
  have hr : (0:ℝ)<(47/20:ℝ)-2-slope := by
    rw [hrate]
    exact_mod_cast hs
  apply generalMean_chord_cost hc hlo hgrid hconv'
    (h.node_sound p.1) (h.node_sound p.2) hr
  · change 0≤2+((47/20:ℝ)-2-slope)*
        generalMeanCritical ((47/20:ℝ)-2-slope) (generalMeanGrid p.1.val) (generalMeanGrid p.2.val)-
      Real.log ((r.c:ℝ)*generalMeanCritical ((47/20:ℝ)-2-slope)
        (generalMeanGrid p.1.val) (generalMeanGrid p.2.val))-(r.J:ℝ)/2-
        (r.error (generalMeanGrid p.1.val):ℝ)+slope*(generalMeanGrid p.1.val:ℝ)
    rw [hcritical,hrate,hslope]
    exact hm
  · exact hL

theorem GeneralMeanNumericalConditions.allL_sound {r : GeneralMeanRow}
    (h : GeneralMeanNumericalConditions r) {L : ℝ} (hL : 1≤L) :
    2*L-2+Real.log ((r.c:ℝ)*L)+
      generalMeanError r.prefactor r.q r.c r.cutoff L+(r.J:ℝ)/2≤(47/20)*L := by
  by_cases h4 : 4≤L
  · have hc : (0:ℝ)<r.c := by exact_mod_cast h.cutoff
    have hq : (0:ℝ)<r.q := by exact_mod_cast h.rate
    have hqc : (2:ℝ)≤(r.q:ℝ)*(r.c:ℝ)/2 := by exact_mod_cast h.decay.le
    have hcont : (1:ℝ)<r.q → (r.c:ℝ)≤r.cutoff ∧ 2≤(r.q:ℝ)*(r.cutoff:ℝ)/2 := by
      intro hqr
      have hqq : (1:ℚ)<r.q := by exact_mod_cast hqr
      exact ⟨by exact_mod_cast (h.continuation hqq).1,
        by exact_mod_cast (h.continuation hqq).2.le⟩
    have hanti := (generalMeanError_convex_antitone h.prefactor_pos.le hq hc hqc hcont).2
    have he4 := h.node_sound (⟨120,by norm_num⟩ : Fin 121)
    norm_num [generalMeanGrid] at he4
    have heL := (hanti (by norm_num : (4:ℝ)∈Ici 1) hL h4).trans he4
    have hl := h.finalLog.sound.2
    push_cast at hl
    have hm : (0:ℝ)≤2+4*((47/20:ℝ)-2)-Real.log (4*(r.c:ℝ))-(r.J:ℝ)/2-(r.error 4:ℝ) := by
      have hh : (0:ℝ)≤((2+4*(47/20-2)-(logRoundedQ (4*r.c)).2-r.J/2-r.error 4:ℚ):ℝ) := by
        exact_mod_cast h.finalMargin
      push_cast at hh
      linarith
    apply generalMean_unbounded_cost hc (by norm_num : (0:ℝ)<4) h4 heL (by norm_num)
    rw [mul_comm (r.c:ℝ) 4]
    nlinarith only [hm]
  · let j := ⌊40*(L-1)⌋₊
    have ht : 0≤40*(L-1) := by linarith
    have hjlo : (j:ℝ)≤40*(L-1) := Nat.floor_le ht
    have hjhi : 40*(L-1)<(j:ℝ)+1 := Nat.lt_floor_add_one _
    have hj : j<120 := by
      have hh : (j:ℝ)<120 := by linarith
      exact_mod_cast hh
    obtain ⟨ps, hps, hcover⟩ := h.intervals
    obtain ⟨p, hp, hlo, hhi⟩ := hcover ⟨j,hj⟩
    obtain ⟨hord, hs, hl, hm⟩ := hps p hp
    apply h.chord_sound p hord hs hl hm
    rw [generalMeanGrid_cast,generalMeanGrid_cast]
    have hlo' : (p.1.val : ℝ) ≤ j := by exact_mod_cast hlo
    have hhi' : (j : ℝ)+1 ≤ p.2.val := by exact_mod_cast hhi
    constructor <;> linarith

end
end SingularValueBounds.KL.Certificates
