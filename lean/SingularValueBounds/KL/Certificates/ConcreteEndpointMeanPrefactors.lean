import SingularValueBounds.KL.Certificates.ConcreteEndpointJointPrefactors

/-! The complete endpoint joint-prefactor family, assembled from exact grid bounds. -/
namespace SingularValueBounds.KL.Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem endpointMean_aPoint_bounds (i : Fin 43) :
    0 ≤ endpointMeanAPoint i ∧ endpointMeanAPoint i ≤ 1 := by
  revert i
  decide +kernel

/-- Corner bounds follow uniformly from the spectral grid and 43 scalar endpoints. -/
theorem endpointMean_cornerBounds (ki : Fin 60) (ai : Fin 42) (h : Fin 4) :
    0 < endpointMeanCornerK ki ai h ∧
    endpointMeanCornerK ki ai h ≤ (endpointMeanBox ki ai).top ∧
    0 ≤ endpointMeanCornerA ki ai h ∧ endpointMeanCornerA ki ai h ≤ 1 := by
  have hlo := endpointMean_aPoint_bounds ⟨ai.val, by omega⟩
  have hhi := endpointMean_aPoint_bounds ⟨ai.val+1, by omega⟩
  have hki : (ki.val : ℚ) ≤ 59 := by exact_mod_cast (show ki.val ≤ 59 by omega)
  have hk0 : (0 : ℚ) < (ki.val+20 : ℚ)/80 := by positivity
  have hk1 : (ki.val+20 : ℚ)/80 ≤ 1 := by linarith
  have hc : ((ki.val+20 : ℚ)/80)^3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hk0.le hk1 3
  have ha : 0 ≤ max (endpointMeanAPoint ⟨ai.val, by omega⟩)
      (((ki.val+20 : ℚ)/80)^3) ∧
      max (endpointMeanAPoint ⟨ai.val, by omega⟩) (((ki.val+20 : ℚ)/80)^3) ≤ 1 :=
    ⟨hlo.1.trans (le_max_left _ _), max_le hlo.2 hc⟩
  have hA : 0 ≤ endpointMeanCornerA ki ai h ∧ endpointMeanCornerA ki ai h ≤ 1 := by
    unfold endpointMeanCornerA
    split_ifs
    · simpa only [endpointMeanBox] using ha
    · simpa only [endpointMeanBox] using hhi
  have hK : 0 < endpointMeanCornerK ki ai h ∧
      endpointMeanCornerK ki ai h ≤ (endpointMeanBox ki ai).top := by
    unfold endpointMeanCornerK
    split_ifs
    · dsimp [endpointMeanBox]
      constructor
      · exact hk0
      · linarith
    · dsimp [endpointMeanBox]
      exact ⟨by positivity, le_rfl⟩
  exact ⟨hK.1, hK.2, hA⟩

theorem endpointMean_cornerIndex (ki : Fin 60) (ai : Fin 42) (h : Fin 4) :
    ∃ n : Fin 61, endpointMeanCornerK ki ai h = ((n.val+20 : ℚ)/80) := by
  unfold endpointMeanCornerK
  split_ifs
  · exact ⟨⟨ki.val, by omega⟩, rfl⟩
  · refine ⟨⟨ki.val+1, by omega⟩, ?_⟩
    dsimp [endpointMeanBox]
    push_cast
    ring

theorem endpointMean_cornerGap (ki : Fin 60) (ai : Fin 42)
    (hactive : endpointMeanActive ki ai) (h : Fin 4) (j : ℕ)
    (hj : j ∈ Finset.Ico (endpointMeanCutoff ki ai) 8000) :
    ((endpointMeanRate ki ai j : ℚ)/100) * (endpointMeanCornerK ki ai h)^2 < 1 := by
  have hb := endpointMean_cornerBounds ki ai h
  have hr := endpointMean_jointRates ki ai hactive j hj
  dsimp only at hr
  have hq : (0:ℚ) ≤ (endpointMeanRate ki ai j : ℚ)/100 := by positivity
  apply lt_of_le_of_lt _ hr.2.2.1
  apply mul_le_mul_of_nonneg_left _ hq
  exact sq_le_sq₀ hb.1.le (hb.1.le.trans hb.2.1) |>.mpr hb.2.1

theorem endpointMean_jointPrefactor_expDomain (ki : Fin 60) (ai : Fin 42)
    (hactive : endpointMeanActive ki ai) (h : Fin 4) (j : ℕ)
    (hj : j ∈ Finset.Ico (endpointMeanCutoff ki ai) 8000) :
    roundUpQ (endpointJointLogUpperQ (endpointMeanCornerK ki ai h)
      (endpointMeanCornerA ki ai h) ((endpointMeanRate ki ai j : ℚ)/100)) < 82 := by
  have hb := endpointMean_cornerBounds ki ai h
  have hr := endpointMean_jointRates ki ai hactive j hj
  dsimp only at hr
  let qi : Fin 111 := ⟨endpointMeanRate ki ai j - 90, by omega⟩
  have hn : qi.val + 90 = endpointMeanRate ki ai j := Nat.sub_add_cancel hr.1
  have hq : ((qi.val+90 : ℚ)/100) = ((endpointMeanRate ki ai j : ℚ)/100) := by
    congr 1
    exact_mod_cast hn
  obtain ⟨n, hk⟩ := endpointMean_cornerIndex ki ai h
  have hgap : ((qi.val+90 : ℚ)/100) * ((n.val+20 : ℚ)/80)^2 < 1 := by
    rw [hq, ← hk]
    exact endpointMean_cornerGap ki ai hactive h j hj
  have hd := endpointJoint_grid_expDomain n qi hgap
  rw [hq, ← hk] at hd
  exact (roundUpQ_mono (endpointJointLog_le_unitMax hb.2.2.1 hb.2.2.2)).trans_lt hd

/-- Every joint endpoint prefactor condition, for all active boxes, corners and nodes. -/
theorem endpointMean_jointPrefactors (ki : Fin 60) (ai : Fin 42)
    (hactive : endpointMeanActive ki ai) (h : Fin 4) (j : ℕ)
    (hj : j ∈ Finset.Ico (endpointMeanCutoff ki ai) 8000) :
    EndpointJointPrefactorConditions (endpointMeanCornerK ki ai h)
      (endpointMeanCornerA ki ai h) ((endpointMeanRate ki ai j : ℚ)/100) := by
  have hb := endpointMean_cornerBounds ki ai h
  exact endpointJointPrefactorConditions hb.1 hb.2.2.1
    (endpointMean_cornerGap ki ai hactive h j hj)
    (endpointMean_jointPrefactor_expDomain ki ai hactive h j hj)

end SingularValueBounds.KL.Certificates
