import SingularValueBounds.KL.Upper.EndpointMeanFinite
import SingularValueBounds.KL.Certificates.ConcreteLog

/-! Exact grid, cutoff, domain and rounding facts for the endpoint upper mean.
The entropy sums and polynomial signs remain separate mathematical obligations. -/
namespace SingularValueBounds.KL.Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem endpointMean_gridLogs (j : ℕ) (hj : j ∈ Finset.Icc 1 8001) :
    RoundedLogConditions ((j : ℚ) / 200) := by
  apply roundedLogConditions
  have h : 0 < j := by have := (Finset.mem_Icc.mp hj).1; omega
  positivity

theorem endpointMean_aGrid : endpointMeanAPoint 0 = 0 ∧ endpointMeanAPoint 42 = 1 ∧
    ∀ ai : Fin 42, endpointMeanAPoint ⟨ai.val, by omega⟩ <
      endpointMeanAPoint ⟨ai.val + 1, by omega⟩ := by
  decide +kernel

theorem endpointMean_quarterNondegenerate (ai : Fin 42) :
    (1 / 4 : ℚ)^3 ≠ endpointMeanAPoint ⟨ai.val + 1, by omega⟩ := by
  revert ai
  decide +kernel

theorem endpointMean_smallCutoff (i : Fin 50) :
    0 < endpointSmallCutoff i ∧ endpointSmallCutoff i ≤ 8000 := by
  revert i
  decide +kernel

theorem endpointMean_smallRounding (i : Fin 50) (j : ℕ) (h : Fin 23) :
    endpointSmallPrefactorQ (endpointSmallK i) ((endpointSmallQ h : ℚ) / 100) *
      endpointDecayQ (endpointSmallQ h) j ≤
        roundUpQ (endpointSmallPrefactorQ (endpointSmallK i) ((endpointSmallQ h : ℚ) / 100) *
          endpointDecayQ (endpointSmallQ h) j) :=
  le_roundUpQ _

theorem endpointMean_smallTotal (i : Fin 50) :
    endpointSmallTarget i + 13 / 12 - 1 / 80 ≤ 58 / 25 := by
  revert i
  decide +kernel

theorem endpointMean_jointCutoff (ki : Fin 60) (ai : Fin 42)
    (h : endpointMeanActive ki ai) :
    0 < endpointMeanCutoff ki ai ∧ endpointMeanCutoff ki ai ≤ 8000 := by
  unfold endpointMeanActive at h
  revert ki ai h
  decide +kernel

theorem endpointMean_jointBoxes (ki : Fin 60) (ai : Fin 42)
    (h : endpointMeanActive ki ai) :
    0 ≤ (endpointMeanBox ki ai).left ∧ 0 < (endpointMeanBox ki ai).bottom ∧
    (endpointMeanBox ki ai).bottom < (endpointMeanBox ki ai).top ∧
    (endpointMeanBox ki ai).top ≤ 1 := by
  unfold endpointMeanActive at h
  revert ki ai h
  decide +kernel

theorem endpointMean_chosenDomain (ki : Fin 60) (ai : Fin 42)
    (hactive : endpointMeanActive ki ai) :
    let b := endpointMeanBox ki ai
    let h := endpointMeanChoice ki ai
    if h = 3 then 5 / 6 ≤ b.left else
      let i := endpointMeanMajorantIndex h
      (majorantBoxes i).left ≤ b.left ∧ b.right ≤ (majorantBoxes i).right ∧
        b.top ≤ (majorantBoxes i).top := by
  unfold endpointMeanActive at hactive
  revert ki ai hactive
  decide +kernel

end SingularValueBounds.KL.Certificates
