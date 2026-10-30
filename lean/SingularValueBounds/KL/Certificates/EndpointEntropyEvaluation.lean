import SingularValueBounds.KL.Certificates.EntropyLookup
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Upper.EndpointRoundedEval

/-! Balanced exact tables and checkpointed integer evaluation of the endpoint
entropy quadrature. The lookup tree is purely functional and its reductions
are checked by the Lean kernel. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure EndpointEntropyState where
  decay : ℤ
  mass : ℤ
  weighted : ℤ
  deriving DecidableEq

def endpointEntropyInitial : EndpointEntropyState := ⟨fixedScaleNat,0,0⟩
-- Nonnegative states use natural arithmetic; all other inputs retain the reference rule.
private theorem endpointDecayCeilNat_eq (n : ℕ) :
    (((n + fixedScaleNat - 1) / fixedScaleNat : ℕ) : ℤ) =
      -(-(n : ℤ)/(fixedScaleNat : ℤ)) := by
  norm_num only [fixedScaleNat]
  omega

def endpointDecayStepInt : ℤ → ℤ → ℤ
  | .ofNat b, .ofNat v => ((v*b+fixedScaleNat-1)/fixedScaleNat : ℕ)
  | b, v => -(-(v*b)/(fixedScaleNat:ℤ))

private theorem endpointDecayStepInt_eq_reference (b v : ℤ) :
    endpointDecayStepInt b v = -(-(v*b)/(fixedScaleNat:ℤ)) := by
  cases b with
  | ofNat b =>
    cases v with
    | ofNat v => exact endpointDecayCeilNat_eq (v*b)
    | negSucc v => rfl
  | negSucc b => cases v <;> rfl

def endpointEntropyAdvance (b : ℤ) (up : ℕ → ℤ) (j : ℕ)
    (v : EndpointEntropyState) : EndpointEntropyState :=
  ⟨endpointDecayStepInt b v.decay, v.mass+v.decay,
    v.weighted+up (j+1)*v.decay⟩

def endpointEntropyState (b : ℤ) (up : ℕ → ℤ) : ℕ → EndpointEntropyState
  | 0 => endpointEntropyInitial
  | j+1 => endpointEntropyAdvance b up j (endpointEntropyState b up j)

def endpointEntropyRun (b : ℤ) (up : ℕ → ℤ) : ℕ → ℕ →
    EndpointEntropyState → EndpointEntropyState
  | _, 0, v => v
  | j, n+1, v => endpointEntropyRun b up (j+1) n (endpointEntropyAdvance b up j v)

theorem endpointEntropyRun_state (b : ℤ) (up : ℕ → ℤ) (j n : ℕ) :
    endpointEntropyRun b up j n (endpointEntropyState b up j) =
      endpointEntropyState b up (j+n) := by
  induction n generalizing j with
  | zero => simp [endpointEntropyRun]
  | succ n ih =>
    rw [endpointEntropyRun]
    change endpointEntropyRun b up (j+1) n (endpointEntropyState b up (j+1)) = _
    rw [ih]
    congr 1
    omega

theorem endpointEntropyState_decay {qi : ℕ} {b : ℤ} (up : ℕ → ℤ)
    (hb : endpointDecayBaseQ qi = fixedQ b) (j : ℕ) :
    endpointDecayQ qi j = fixedQ (endpointEntropyState b up j).decay := by
  induction j with
  | zero => norm_num [endpointDecayQ, endpointEntropyState, endpointEntropyInitial,
      fixedQ, fixedScaleNat, roundingScale]
  | succ j ih =>
    rw [endpointDecayQ, ih, hb]
    change roundUpQ (fixedQ (endpointEntropyState b up j).decay*fixedQ b) =
      fixedQ (endpointDecayStepInt b (endpointEntropyState b up j).decay)
    simpa [endpointDecayStepInt_eq_reference] using
      roundUpQ_fixed_mul_div (endpointEntropyState b up j).decay b 1

theorem endpointEntropyState_mass (b : ℤ) (up : ℕ → ℤ) (j : ℕ) :
    (endpointEntropyState b up j).mass =
      ∑ i ∈ Finset.range j, (endpointEntropyState b up i).decay := by
  induction j with
  | zero => simp [endpointEntropyState, endpointEntropyInitial]
  | succ j ih => simp only [endpointEntropyState, endpointEntropyAdvance,
      Finset.sum_range_succ, ih]

theorem endpointEntropyState_weighted (b : ℤ) (up : ℕ → ℤ) (j : ℕ) :
    (endpointEntropyState b up j).weighted =
      ∑ i ∈ Finset.range j, up (i+1)*(endpointEntropyState b up i).decay := by
  induction j with
  | zero => simp [endpointEntropyState, endpointEntropyInitial]
  | succ j ih => simp only [endpointEntropyState, endpointEntropyAdvance,
      Finset.sum_range_succ, ih]

def endpointEntropyCached (b : ℤ) (up : ℕ → ℤ)
    (checkpoints : ℕ → EndpointEntropyState) (j : ℕ) : EndpointEntropyState :=
  endpointEntropyRun b up (32*(j/32)) (j%32) (checkpoints (j/32))

theorem endpointEntropy_checkpoints (b : ℤ) (up : ℕ → ℤ)
    (c : ℕ → EndpointEntropyState) (n : ℕ)
    (hz : c 0 = endpointEntropyInitial)
    (hs : ∀ i, i < n → c (i+1) = endpointEntropyRun b up (32*i) 32 (c i)) :
    ∀ i, i ≤ n → c i = endpointEntropyState b up (32*i) := by
  intro i
  induction i with
  | zero => intro _; simpa [endpointEntropyState] using hz
  | succ i ih =>
    intro hi
    rw [hs i (by omega), ih (by omega), endpointEntropyRun_state]
    congr 1

theorem endpointEntropyCached_correct (b : ℤ) (up : ℕ → ℤ)
    (c : ℕ → EndpointEntropyState) (n j : ℕ)
    (hz : c 0 = endpointEntropyInitial)
    (hs : ∀ i, i < n → c (i+1) = endpointEntropyRun b up (32*i) 32 (c i))
    (hj : j/32 ≤ n) :
    endpointEntropyCached b up c j = endpointEntropyState b up j := by
  unfold endpointEntropyCached
  rw [endpointEntropy_checkpoints b up c n hz hs _ hj, endpointEntropyRun_state]
  congr 1
  omega

end SingularValueBounds.KL.Certificates
