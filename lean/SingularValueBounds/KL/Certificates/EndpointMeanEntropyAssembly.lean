import SingularValueBounds.KL.Certificates.EndpointEntropyTables
import SingularValueBounds.KL.Certificates.EndpointMeanRateRuns
import SingularValueBounds.KL.Certificates.EndpointSmallSelection
import SingularValueBounds.KL.Certificates.EndpointEntropyRounding

/-! Assembly of exact integer entropy certificates for endpoint boxes. -/
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0

/-- Reuse a corner value after checking the rate/value correspondence. Keeping
this transfer abstract avoids elaborating the same argument in every box. -/
theorem endpointPrefactorValues_of_sharedCorner
    {k a k' a' : ℚ} {rs ss : List EndpointRateRun} {p p' : ℕ → ℤ}
    (hk : k = k') (ha : a = a')
    (hp : ∀ s ∈ ss, endpointJointPrefactorQ k' a' ((s.rate : ℚ)/100) =
      fixedQ (p' s.rate))
    (hb : ∀ r ∈ rs, ∃ s ∈ ss, s.rate = r.rate ∧ p' s.rate = p r.rate) :
    ∀ r ∈ rs, endpointJointPrefactorQ k a ((r.rate : ℚ)/100) =
      fixedQ (p r.rate) := by
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := hb r hr
  calc
    _ = endpointJointPrefactorQ k' a' ((s.rate : ℚ)/100) := by rw [hk, ha, hrate]
    _ = fixedQ (p' s.rate) := hp s hs
    _ = _ := congrArg fixedQ hvalue


/-- Project either checked prefactor correspondence from a shared rate search. -/
theorem endpointPrefactorBridge_left {rs ss : List EndpointRateRun}
    {p p' q q' : ℕ → ℤ}
    (h : ∀ r ∈ rs, ∃ s ∈ ss, s.rate = r.rate ∧
      p' s.rate = p r.rate ∧ q' s.rate = q r.rate) :
    ∀ r ∈ rs, ∃ s ∈ ss, s.rate = r.rate ∧ p' s.rate = p r.rate := by
  intro r hr
  obtain ⟨s, hs, he, hp, _⟩ := h r hr
  exact ⟨s, hs, he, hp⟩

theorem endpointPrefactorBridge_right {rs ss : List EndpointRateRun}
    {p p' q q' : ℕ → ℤ}
    (h : ∀ r ∈ rs, ∃ s ∈ ss, s.rate = r.rate ∧
      p' s.rate = p r.rate ∧ q' s.rate = q r.rate) :
    ∀ r ∈ rs, ∃ s ∈ ss, s.rate = r.rate ∧ q' s.rate = q r.rate := by
  intro r hr
  obtain ⟨s, hs, he, _, hq⟩ := h r hr
  exact ⟨s, hs, he, hq⟩

 theorem endpointMeanNumericCorner_le_of_runs (ki : Fin 60) (ai : Fin 42)
    (hact : endpointMeanActive ki ai) (rs : List EndpointRateRun) (p : Fin 4 → ℕ → ℤ)
    (hc : EndpointRunsCover (endpointMeanCutoff ki ai) 8000 rs)
    (hd : ∀ r ∈ rs, 90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000)
    (hr : ∀ r ∈ rs, EndpointRateRunValid ki ai r)
    (hp : ∀ h : Fin 4, ∀ r ∈ rs,
      endpointJointPrefactorQ (endpointMeanCornerK ki ai h) (endpointMeanCornerA ki ai h)
        ((r.rate:ℚ)/100) = fixedQ (p h r.rate))
    (ht : ∀ h : Fin 4, endpointEntropyByRuns (endpointMeanCutoff ki ai) (p h) rs ≤
      endpointMeanCorner ki ai h) :
    ∀ h : Fin 4, endpointMeanNumericCorner ki ai h ≤ endpointMeanCorner ki ai h := by
  intro h
  have hcut := endpointMean_jointCutoff ki ai hact
  unfold endpointMeanNumericCorner
  rw [endpointEntropyByRuns_eq (endpointMeanCutoff ki ai) (endpointMeanRate ki ai)
    (fun q => endpointJointPrefactorQ (endpointMeanCornerK ki ai h)
      (endpointMeanCornerA ki ai h) ((q:ℚ)/100)) (p h) rs hcut.1 hcut.2 hc hd
    (fun r hm j hj => endpointMeanRate_constant_on_run ki ai hact r (hr r hm) j hj) (hp h)]
  exact ht h

theorem endpointSmallNumerical_le_of_runs (i : Fin 50) (rs : List EndpointRateRun)
    (p : ℕ → ℤ)
    (hc : EndpointRunsCover (endpointSmallCutoff i) 8000 rs)
    (hd : ∀ r ∈ rs, 90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧
      r.stop ≤ 8000 ∧ (r.rate-90)%5 = 0)
    (hm : ∀ r ∈ rs, (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK i*((r.rate:ℚ)/100-1) ≤ 58/25)
    (hp : ∀ r ∈ rs, endpointSmallPrefactorQ (endpointSmallK i) ((r.rate:ℚ)/100) =
      fixedQ (p r.rate))
    (ht : endpointEntropyByRuns (endpointSmallCutoff i) p rs+440/roundingScale ≤
      endpointSmallTarget i) :
    entropyGridBoundQ (endpointSmallCutoff i) (endpointSmallBound i) (endpointDecayQ 90 8000) ≤
      endpointSmallTarget i := by
  have hcut := endpointMean_smallCutoff i
  let A : ℕ → ℚ := fun j => endpointSmallPrefactorQ (endpointSmallK i)
    ((endpointRateOfRuns rs j:ℚ)/100)*endpointDecayQ (endpointRateOfRuns rs j) j
  have hBA (j : ℕ) (hj : j ∈ Finset.Ico (endpointSmallCutoff i) 8000) :
      endpointSmallBound i j ≤ A j+1/roundingScale := by
    obtain ⟨r,hr,hjr⟩ := hc.exists_run hj
    obtain ⟨hlo,hhi,_,_,hmod⟩ := hd r hr
    let index : Fin 23 := ⟨(r.rate-90)/5,by omega⟩
    have hq : endpointSmallQ index = r.rate := by
      dsimp [endpointSmallQ,index]
      omega
    have hmargin : (j:ℚ)/200*endpointSmallK i*((r.rate:ℚ)/100-1) ≤ 58/25 := by
      by_cases h : (r.rate:ℚ)/100 ≤ 1
      · exact endpointSmall_margin_of_le_one i j _ h
      · exact endpointSmall_margin_of_upper i j (r.stop-1) _
          (by have := Finset.mem_Ico.mp hjr; omega) (le_of_not_ge h) (hm r hr)
    have hb := endpointSmallBound_le_selected_add i j index
      (by simpa only [hq] using hmargin)
    simpa only [A,hc.rateOfRuns_eq hr hjr,hq] using hb
  have hbound := entropyGridBoundQ_rounding_allowance (endpointSmallCutoff i)
    (endpointSmallBound i) A (endpointDecayQ 90 8000) hcut.1 hcut.2 hBA
    (fun j hj => endpointEntropyKernel_bounds _ j hcut.1 hj)
  have he : entropyGridBoundQ (endpointSmallCutoff i) A (endpointDecayQ 90 8000) =
      endpointEntropyByRuns (endpointSmallCutoff i) p rs := by
    apply endpointEntropyByRuns_eq _ (endpointRateOfRuns rs)
      (fun q => endpointSmallPrefactorQ (endpointSmallK i) ((q:ℚ)/100)) p rs
      hcut.1 hcut.2 hc
    · intro r hr
      have hrd := hd r hr
      exact ⟨hrd.1,hrd.2.1,hrd.2.2.1,hrd.2.2.2.1⟩
    · intro r hr j hj
      exact hc.rateOfRuns_eq hr hj
    · exact hp
  rw [he] at hbound
  exact hbound.trans ht

end SingularValueBounds.KL.Certificates
