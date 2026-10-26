import SingularValueBounds.KL.Certificates.EndpointEntropyLog
import SingularValueBounds.KL.Certificates.EndpointEntropyDecay
import SingularValueBounds.KL.Certificates.EndpointEntropyIntegral
import SingularValueBounds.KL.Certificates.ConcreteLog

/-! An exact, kernel-checked evaluation of entropy sums by constant-rate runs. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0

 theorem endpointEntropyKernel_bounds (j0 j : ℕ) (hj0 : 0 < j0)
    (hj : j ∈ Finset.Ico j0 8000) :
    0 ≤ entropyGridKernelQ j0 j ∧ entropyGridKernelQ j0 j ≤ 11 := by
  have hj' := Finset.mem_Ico.mp hj
  have hlog0 := endpointLogGrid_eq j0 (by omega) (by omega)
  have hlogj := endpointLogGrid_eq (j+1) (by omega) (by omega)
  have hbounds0 := endpointLogGrid_bounds j0 (by omega) (by omega)
  have hboundsj := endpointLogGrid_bounds (j+1) (by omega) (by omega)
  have hlo : -(6:ℚ) ≤ fixedQ (endpointLogLower j0) := by
    unfold fixedQ
    apply (le_div_iff₀ (by norm_num [roundingScale])).2
    norm_num only [roundingScale, fixedScaleNat] at hbounds0 ⊢
    exact_mod_cast hbounds0.1
  have hhi : fixedQ (endpointLogUpper (j+1)) ≤ (4:ℚ) := by
    unfold fixedQ
    apply (div_le_iff₀ (by norm_num [roundingScale])).2
    norm_num only [roundingScale, fixedScaleNat] at hboundsj ⊢
    exact_mod_cast hboundsj.2
  constructor
  · apply entropyGridKernel_nonneg hj0 hj'.1
    · apply roundedLogConditions
      positivity
    · apply roundedLogConditions
      positivity
  · unfold entropyGridKernelQ
    simp only [Nat.cast_add,Nat.cast_one] at hlogj
    rw [hlog0,hlogj]
    dsimp only
    linarith

noncomputable def endpointEntropyMoment (j0 q a z : ℕ) : ℤ :=
  (endpointDecayState q z).weighted-(endpointDecayState q a).weighted+
    ((fixedScaleNat:ℤ)-endpointLogLower j0)*
      ((endpointDecayState q z).mass-(endpointDecayState q a).mass)

noncomputable def endpointEntropyRunValue (j0 : ℕ) (p : ℕ → ℤ) (r : EndpointRateRun) : ℤ :=
  p r.rate*endpointEntropyMoment j0 r.rate r.start r.stop

noncomputable def endpointEntropyByRuns (j0 : ℕ) (p : ℕ → ℤ)
    (rs : List EndpointRateRun) : ℚ :=
  fixedQ (endpointLogUpper j0)+
    ((rs.map (endpointEntropyRunValue j0 p)).sum:ℤ)/(200*roundingScale^3)+
    entropyGridTailQ j0 (fixedQ (endpointDecayState 90 8000).decay)

 theorem endpointEntropyByRuns_eq (j0 : ℕ) (rate : ℕ → ℕ) (pref : ℕ → ℚ)
    (p : ℕ → ℤ) (rs : List EndpointRateRun)
    (hj0 : 0 < j0) (hjEnd : j0 ≤ 8000)
    (hc : EndpointRunsCover j0 8000 rs)
    (hd : ∀ r ∈ rs, 90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000)
    (hr : ∀ r ∈ rs, ∀ j ∈ Finset.Ico r.start r.stop, rate j = r.rate)
    (hp : ∀ r ∈ rs, pref r.rate = fixedQ (p r.rate)) :
    entropyGridBoundQ j0 (fun j => pref (rate j)*endpointDecayQ (rate j) j)
      (endpointDecayQ 90 8000) = endpointEntropyByRuns j0 p rs := by
  have he (r : EndpointRateRun) (hmem : r ∈ rs) :
      (∑ j ∈ Finset.Ico r.start r.stop,
        entropyGridKernelQ j0 j*(pref (rate j)*endpointDecayQ (rate j) j)/200) =
        ((endpointEntropyRunValue j0 p r:ℤ):ℚ)/(200*roundingScale^3) := by
    have hrd := hd r hmem
    calc
      _ = ∑ j ∈ Finset.Ico r.start r.stop,
          entropyGridKernelQ j0 j*(fixedQ (p r.rate)*endpointDecayQ r.rate j)/200 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hr r hmem j hj,hp r hmem]
      _ = _ := by
        rw [endpointEntropy_constant_interval (L := endpointLogLower j0) (A := p r.rate)
          endpointLogUpper hrd.2.2.1
          (endpointDecayBase_eq r.rate hrd.1 hrd.2.1)]
        · unfold endpointEntropyRunValue endpointEntropyMoment
          rw [endpointDecayState_correct r.rate r.stop hrd.1 hrd.2.1 hrd.2.2.2,
            endpointDecayState_correct r.rate r.start hrd.1 hrd.2.1
              (hrd.2.2.1.trans hrd.2.2.2)]
        · exact congrArg Prod.fst (endpointLogGrid_eq j0 (by omega) (by omega))
        · intro j hj
          have hj' := Finset.mem_Ico.mp hj
          simpa only [Nat.cast_add,Nat.cast_one] using
            congrArg Prod.snd (endpointLogGrid_eq (j+1) (by omega) (by omega))
  have hs : (rs.map (fun r => ∑ j ∈ Finset.Ico r.start r.stop,
      entropyGridKernelQ j0 j*(pref (rate j)*endpointDecayQ (rate j) j)/200)).sum =
      ((rs.map (endpointEntropyRunValue j0 p)).sum:ℤ)/(200*roundingScale^3) := by
    have hm : rs.map (fun r => ∑ j ∈ Finset.Ico r.start r.stop,
        entropyGridKernelQ j0 j*(pref (rate j)*endpointDecayQ (rate j) j)/200) =
        rs.map (fun r => ((endpointEntropyRunValue j0 p r:ℤ):ℚ)/(200*roundingScale^3)) := by
      apply List.map_congr_left
      exact he
    rw [hm]
    have hcast (xs : List EndpointRateRun) :
        (xs.map (fun r => ((endpointEntropyRunValue j0 p r:ℤ):ℚ)/(200*roundingScale^3))).sum =
          ((xs.map (endpointEntropyRunValue j0 p)).sum:ℤ)/(200*roundingScale^3) := by
      induction xs with
      | nil => simp
      | cons r xs ih => simp only [List.map_cons,List.sum_cons,Int.cast_add,add_div,ih]
    exact hcast rs
  unfold entropyGridBoundQ endpointEntropyByRuns
  rw [endpointLogGrid_eq j0 (by omega) (by omega), endpointDecay_eq 90 8000 (by norm_num)
    (by norm_num) (by norm_num), hc.sum, hs]

end SingularValueBounds.KL.Certificates
