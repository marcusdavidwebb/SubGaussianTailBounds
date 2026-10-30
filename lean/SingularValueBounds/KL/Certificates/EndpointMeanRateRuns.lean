import SingularValueBounds.KL.Certificates.EndpointRateIntervals
import SingularValueBounds.KL.Certificates.EndpointEntropyRuns

/-! Finite endpoint checks imply that the selected rate is constant on a run. -/
namespace SingularValueBounds.KL.Certificates

def endpointMeanRateLower (ki : Fin 60) (ai : Fin 42) (r : EndpointRateRun) : ℕ :=
  let b := endpointMeanBox ki ai
  endpointRateClip (endpointRateOpt ((b.bottom+b.top)/2) ((b.left+b.right)/2)
    ((r.start : ℚ)/200)) (endpointRateMargin b.top (((r.stop-1 : ℕ) : ℚ)/200))
      (endpointRateSpectral b.top)

def endpointMeanRateUpper (ki : Fin 60) (ai : Fin 42) (r : EndpointRateRun) : ℕ :=
  let b := endpointMeanBox ki ai
  endpointRateClip (endpointRateOpt ((b.bottom+b.top)/2) ((b.left+b.right)/2)
    (((r.stop-1 : ℕ) : ℚ)/200)) (endpointRateMargin b.top ((r.start : ℚ)/200))
      (endpointRateSpectral b.top)

def EndpointRateRunValid (ki : Fin 60) (ai : Fin 42) (r : EndpointRateRun) : Prop :=
  200 ≤ r.start ∧ r.start < r.stop ∧ endpointMeanRateLower ki ai r = r.rate ∧
    endpointMeanRateUpper ki ai r = r.rate

instance (ki : Fin 60) (ai : Fin 42) (r : EndpointRateRun) :
    Decidable (EndpointRateRunValid ki ai r) :=
  inferInstanceAs (Decidable (200 ≤ r.start ∧ r.start < r.stop ∧
    endpointMeanRateLower ki ai r = r.rate ∧ endpointMeanRateUpper ki ai r = r.rate))

theorem endpointMeanRate_constant_on_run (ki : Fin 60) (ai : Fin 42)
    (hactive : endpointMeanActive ki ai) (r : EndpointRateRun)
    (h : EndpointRateRunValid ki ai r) (j : ℕ) (hj : j ∈ Finset.Ico r.start r.stop) :
    endpointMeanRate ki ai j = r.rate := by
  obtain ⟨hstart, hstop, hl, hh⟩ := h
  obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj
  obtain ⟨ha0, hk0, hkk, hk1⟩ := endpointMean_jointBoxes ki ai hactive
  have haa : (endpointMeanBox ki ai).left < (endpointMeanBox ki ai).right := hactive.1
  apply endpointRate_constant_on_interval
    (((endpointMeanBox ki ai).bottom+(endpointMeanBox ki ai).top)/2)
    (((endpointMeanBox ki ai).left+(endpointMeanBox ki ai).right)/2)
    (endpointMeanBox ki ai).top ((r.start:ℚ)/200)
    (((r.stop-1:ℕ):ℚ)/200) ((j:ℚ)/200) r.rate
  · linarith
  · linarith
  · linarith
  · have : (200:ℚ) ≤ r.start := by exact_mod_cast hstart
    linarith
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hjlo) (by norm_num)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : j ≤ r.stop-1))
      (by norm_num)
  · exact hl
  · exact hh

end SingularValueBounds.KL.Certificates
