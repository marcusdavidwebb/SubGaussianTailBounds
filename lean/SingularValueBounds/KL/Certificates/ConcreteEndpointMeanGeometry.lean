import SingularValueBounds.KL.Upper.EndpointMeanFinite
import SingularValueBounds.KL.Certificates.ConcreteLog

/-! Exact grid, cutoff, domain and rounding facts for the endpoint upper mean.
The entropy sums and polynomial signs remain separate mathematical obligations. -/
namespace SingularValueBounds.KL.Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem endpointMean_smallTotal (i : Fin 50) :
    endpointSmallTarget i + 13 / 12 - 1 / 80 ≤ 58 / 25 := by
  have hi0 : (0 : ℚ) ≤ i.val := Nat.cast_nonneg _
  have hi : (i.val : ℚ) ≤ 50 := by exact_mod_cast (show i.val ≤ 50 by omega)
  have hsq := pow_le_pow_left₀ hi0 hi 2
  have hfour := pow_le_pow_left₀ hi0 hi 4
  norm_num at hsq hfour
  unfold endpointSmallTarget
  linarith

/-- Only cutoff and polynomial-choice data require joint table checks. -/
private def endpointJointPrimary (ki : Fin 60) (ai : Fin 42) : Prop :=
  endpointMeanActive ki ai →
    (0 < endpointMeanCutoff ki ai ∧ endpointMeanCutoff ki ai ≤ 8000) ∧
      (let b := endpointMeanBox ki ai
       let h := endpointMeanChoice ki ai
       if h = 3 then 5 / 6 ≤ b.left else
         let i := endpointMeanMajorantIndex h
         (majorantBoxes i).left ≤ b.left ∧ b.right ≤ (majorantBoxes i).right ∧
           b.top ≤ (majorantBoxes i).top)

private def endpointJointIndex (b : Fin 12) (i : Fin 5) : Fin 60 :=
  ⟨b.val * 5 + i.val, by omega⟩

/- Each declaration checks five spectral rows. The index identity below
   reconstructs every original row without padding or omitted cases. -/
private theorem endpointJointPrimary_block00 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 0 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block01 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 1 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block02 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 2 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block03 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 3 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block04 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 4 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block05 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 5 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block06 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 6 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block07 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 7 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block08 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 8 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block09 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 9 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block10 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 10 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_block11 : ∀ i : Fin 5, ∀ ai : Fin 42,
    endpointJointPrimary (endpointJointIndex 11 i) ai := by
  unfold endpointJointPrimary endpointMeanActive
  decide +kernel

private theorem endpointJointPrimary_all (ki : Fin 60) (ai : Fin 42) :
    endpointJointPrimary ki ai := by
  have blocks (b : Fin 12) (i : Fin 5) (a : Fin 42) :
      endpointJointPrimary (endpointJointIndex b i) a := by
    fin_cases b
    · exact endpointJointPrimary_block00 i a
    · exact endpointJointPrimary_block01 i a
    · exact endpointJointPrimary_block02 i a
    · exact endpointJointPrimary_block03 i a
    · exact endpointJointPrimary_block04 i a
    · exact endpointJointPrimary_block05 i a
    · exact endpointJointPrimary_block06 i a
    · exact endpointJointPrimary_block07 i a
    · exact endpointJointPrimary_block08 i a
    · exact endpointJointPrimary_block09 i a
    · exact endpointJointPrimary_block10 i a
    · exact endpointJointPrimary_block11 i a
  let b : Fin 12 := ⟨ki.val / 5, by omega⟩
  let i : Fin 5 := ⟨ki.val % 5, Nat.mod_lt _ (by norm_num)⟩
  have hi : endpointJointIndex b i = ki := by
    apply Fin.ext
    dsimp [endpointJointIndex, b, i]
    omega
  have h := blocks b i ai
  simpa only [hi] using h

theorem endpointMean_jointCutoff (ki : Fin 60) (ai : Fin 42)
    (h : endpointMeanActive ki ai) :
    0 < endpointMeanCutoff ki ai ∧ endpointMeanCutoff ki ai ≤ 8000 := by
  exact (endpointJointPrimary_all ki ai h).1

theorem endpointMean_jointBoxes (ki : Fin 60) (ai : Fin 42) :
    0 ≤ (endpointMeanBox ki ai).left ∧ 0 < (endpointMeanBox ki ai).bottom ∧
    (endpointMeanBox ki ai).bottom < (endpointMeanBox ki ai).top ∧
    (endpointMeanBox ki ai).top ≤ 1 := by
  have hi : (ki.val : ℚ) ≤ 59 := by exact_mod_cast (show ki.val ≤ 59 by omega)
  dsimp only [endpointMeanBox]
  exact ⟨le_trans (by positivity) (le_max_right _ _), by positivity, by linarith, by linarith⟩

theorem endpointMean_chosenDomain (ki : Fin 60) (ai : Fin 42)
    (hactive : endpointMeanActive ki ai) :
    let b := endpointMeanBox ki ai
    let h := endpointMeanChoice ki ai
    if h = 3 then 5 / 6 ≤ b.left else
      let i := endpointMeanMajorantIndex h
      (majorantBoxes i).left ≤ b.left ∧ b.right ≤ (majorantBoxes i).right ∧
        b.top ≤ (majorantBoxes i).top := by
  exact (endpointJointPrimary_all ki ai hactive).2

end SingularValueBounds.KL.Certificates
