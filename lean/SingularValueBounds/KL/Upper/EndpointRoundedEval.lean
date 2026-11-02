import SingularValueBounds.KL.Upper.EntropyGrid
import SingularValueBounds.KL.Upper.EntropyConvexity

open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
noncomputable section
set_option maxHeartbeats 1200000

def endpointDecayBaseQ (qi : ℕ) : ℚ :=
  expUpperRoundedQ (-roundDownQ ((qi : ℚ)/40000))
def endpointDecayQ (qi : ℕ) : ℕ → ℚ
  | 0 => 1
  | j+1 => roundUpQ (endpointDecayQ qi j*endpointDecayBaseQ qi)

def EndpointDecayConditions (qi : ℕ) : Prop :=
  (qi : ℚ)/40000≥roundDownQ ((qi : ℚ)/40000) ∧
  RoundedExpConditions (-roundDownQ ((qi : ℚ)/40000)) ∧
  ∀j∈Finset.range 8001,
    endpointDecayQ qi j*endpointDecayBaseQ qi≤endpointDecayQ qi (j+1)

theorem EndpointDecayConditions.sound {qi j : ℕ} (h : EndpointDecayConditions qi)
    (hj : j≤8001) : Real.exp (-((qi : ℝ)/100*((j : ℝ)/200)/2))≤(endpointDecayQ qi j : ℝ) := by
  have hBase : Real.exp (-((qi : ℝ)/40000))≤(endpointDecayBaseQ qi : ℝ) := by
    have hr : -((qi : ℝ)/40000)≤(-roundDownQ ((qi : ℚ)/40000) : ℚ) := by
      have hh : ((-((qi : ℚ)/40000) : ℚ) : ℝ)≤
          ((-roundDownQ ((qi : ℚ)/40000) : ℚ) : ℝ) := by exact_mod_cast (neg_le_neg h.1)
      simpa using hh
    exact (Real.exp_le_exp.mpr hr).trans h.2.1.sound
  induction j with
  | zero => simp [endpointDecayQ]
  | succ j ih =>
    have hj' : j≤8001 := by omega
    have he : -((qi : ℝ)/100*(((j+1 : ℕ) : ℝ)/200)/2)=
        -((qi : ℝ)/100*((j : ℝ)/200)/2)+-((qi : ℝ)/40000) := by push_cast; ring
    have hround : (endpointDecayQ qi j : ℝ)*(endpointDecayBaseQ qi : ℝ)≤
        (endpointDecayQ qi (j+1) : ℝ) := by
      exact_mod_cast h.2.2 j (Finset.mem_range.mpr (by omega))
    rw [he,Real.exp_add]
    exact (mul_le_mul (ih hj') hBase (Real.exp_nonneg _) ((Real.exp_nonneg _).trans (ih hj'))).trans hround

def endpointJointLogUpperQ (k a q : ℚ) : ℚ :=
  roundUpQ (q/2)+roundUpQ (a*(-(logRoundedQ (1-q*k^2)).1-roundDownQ (q*k^2))/(2*k^3))
def endpointJointPrefactorQ (k a q : ℚ) : ℚ :=
  expUpperRoundedQ (endpointJointLogUpperQ k a q)

def EndpointJointPrefactorConditions (k a q : ℚ) : Prop :=
  0<k ∧ 0≤a ∧ q*k^2<1 ∧ RoundedLogConditions (1-q*k^2) ∧
  roundDownQ (q*k^2)≤q*k^2 ∧ q/2≤roundUpQ (q/2) ∧
  a*(-(logRoundedQ (1-q*k^2)).1-roundDownQ (q*k^2))/(2*k^3)≤
    roundUpQ (a*(-(logRoundedQ (1-q*k^2)).1-roundDownQ (q*k^2))/(2*k^3)) ∧
  RoundedExpConditions (endpointJointLogUpperQ k a q)

theorem EndpointJointPrefactorConditions.sound {k a q : ℚ}
    (h : EndpointJointPrefactorConditions k a q) :
    upperJointPrefactor (q : ℝ) a k≤(endpointJointPrefactorQ k a q : ℝ) := by
  have hk : (0 : ℝ)<k := by exact_mod_cast h.1
  have ha : (0 : ℝ)≤a := by exact_mod_cast h.2.1
  have hLog := h.2.2.2.1.sound.1
  norm_num only [Rat.cast_sub,Rat.cast_one,Rat.cast_mul,Rat.cast_pow] at hLog
  have hDown : (roundDownQ (q*k^2) : ℝ)≤(q : ℝ)*(k : ℝ)^2 := by exact_mod_cast h.2.2.2.2.1
  have hQ : (q : ℝ)/2≤(roundUpQ (q/2) : ℝ) := by exact_mod_cast h.2.2.2.2.2.1
  have hRound : (a : ℝ)*(-(logRoundedQ (1-q*k^2)).1-roundDownQ (q*k^2))/(2*(k : ℝ)^3)≤
      (roundUpQ (a*(-(logRoundedQ (1-q*k^2)).1-roundDownQ (q*k^2))/(2*k^3)) : ℝ) := by
    exact_mod_cast h.2.2.2.2.2.2.1
  have hScale := mul_le_mul_of_nonneg_left
    (show -Real.log (1-(q : ℝ)*(k : ℝ)^2)-(q : ℝ)*(k : ℝ)^2≤
      -((logRoundedQ (1-q*k^2)).1 : ℝ)-(roundDownQ (q*k^2) : ℝ) by linarith)
    (show 0≤(a : ℝ)/(2*(k : ℝ)^3) by positivity)
  apply (Real.exp_le_exp.mpr ?_).trans h.2.2.2.2.2.2.2.sound
  dsimp [upperJointPrefactor,upperJointCost,endpointJointLogUpperQ]
  push_cast
  calc
    _ ≤ (q : ℝ)/2+(a : ℝ)*(-((logRoundedQ (1-q*k^2)).1 : ℝ)-roundDownQ (q*k^2))/(2*(k : ℝ)^3) := by
      convert! add_le_add_left hScale ((q : ℝ)/2) using 1 <;> ring
    _ ≤ _ := add_le_add hQ hRound

def endpointSmallPrefactorQ (k q : ℚ) : ℚ :=
  expUpperRoundedQ (roundUpQ (-(logRoundedQ (1-q*k^2)).1/(2*k^2)))

def EndpointSmallPrefactorConditions (k q : ℚ) : Prop :=
  0<k ∧ q*k^2<1 ∧ RoundedLogConditions (1-q*k^2) ∧
  -(logRoundedQ (1-q*k^2)).1/(2*k^2)≤roundUpQ (-(logRoundedQ (1-q*k^2)).1/(2*k^2)) ∧
  RoundedExpConditions (roundUpQ (-(logRoundedQ (1-q*k^2)).1/(2*k^2)))

theorem EndpointSmallPrefactorConditions.sound {k q : ℚ}
    (h : EndpointSmallPrefactorConditions k q) :
    Real.exp (-Real.log (1-(q : ℝ)*(k : ℝ)^2)/(2*(k : ℝ)^2))≤
      (endpointSmallPrefactorQ k q : ℝ) := by
  have hk : (0 : ℝ)<k := by exact_mod_cast h.1
  have hl := h.2.2.1.sound.1
  norm_num only [Rat.cast_sub,Rat.cast_one,Rat.cast_mul,Rat.cast_pow] at hl
  have hr : (-((logRoundedQ (1-q*k^2)).1 : ℝ))/(2*(k : ℝ)^2)≤
      (roundUpQ (-(logRoundedQ (1-q*k^2)).1/(2*k^2)) : ℝ) := by exact_mod_cast h.2.2.2.1
  exact (Real.exp_le_exp.mpr ((div_le_div_of_nonneg_right (neg_le_neg hl) (by positivity)).trans hr)).trans
    h.2.2.2.2.sound

end
end SingularValueBounds.KL.Certificates
