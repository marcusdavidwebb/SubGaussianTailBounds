import SingularValueBounds.KL.Certificates.EndpointEntropyEvaluation
import SingularValueBounds.KL.Certificates.EndpointEntropyRuns

/-! Exact reduction of a constant-rate entropy interval to two integer prefix moments. -/
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0

 theorem endpointEntropyState_interval (b L : ℤ) (up : ℕ → ℤ)
    (a z : ℕ) (haz : a ≤ z) :
    (∑ j ∈ Finset.Ico a z,
      ((fixedScaleNat:ℤ)+up (j+1)-L)*(endpointEntropyState b up j).decay) =
    (endpointEntropyState b up z).weighted-(endpointEntropyState b up a).weighted+
      ((fixedScaleNat:ℤ)-L)*
        ((endpointEntropyState b up z).mass-(endpointEntropyState b up a).mass) := by
  have he (j : ℕ) : ((fixedScaleNat:ℤ)+up (j+1)-L)*(endpointEntropyState b up j).decay =
      up (j+1)*(endpointEntropyState b up j).decay+
        ((fixedScaleNat:ℤ)-L)*(endpointEntropyState b up j).decay := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_Ico_eq_sub _ haz, Finset.sum_Ico_eq_sub _ haz]
  rw [← endpointEntropyState_weighted, ← endpointEntropyState_weighted,
    ← endpointEntropyState_mass, ← endpointEntropyState_mass]

 theorem endpointEntropy_constant_interval {qi j0 a z : ℕ} {b L A : ℤ}
    (up : ℕ → ℤ) (haz : a ≤ z)
    (hb : endpointDecayBaseQ qi = fixedQ b)
    (hl : (logRoundedQ ((j0:ℚ)/200)).1 = fixedQ L)
    (hu : ∀ j ∈ Finset.Ico a z,
      (logRoundedQ ((j+1:ℚ)/200)).2 = fixedQ (up (j+1))) :
    (∑ j ∈ Finset.Ico a z,
      entropyGridKernelQ j0 j*(fixedQ A*endpointDecayQ qi j)/200) =
    ((A*((endpointEntropyState b up z).weighted-(endpointEntropyState b up a).weighted+
      ((fixedScaleNat:ℤ)-L)*
        ((endpointEntropyState b up z).mass-(endpointEntropyState b up a).mass)) : ℤ) : ℚ)/
      (200*roundingScale^3) := by
  have he (j : ℕ) (hj : j ∈ Finset.Ico a z) :
      entropyGridKernelQ j0 j*(fixedQ A*endpointDecayQ qi j)/200 =
        ((A*(((fixedScaleNat:ℤ)+up (j+1)-L)*(endpointEntropyState b up j).decay):ℤ):ℚ)/
          (200*roundingScale^3) := by
    rw [entropyGridKernelQ, hl, hu j hj, endpointEntropyState_decay up hb]
    simp only [fixedQ, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast]
    norm_num only [fixedScaleNat, roundingScale, Nat.cast_ofNat]
    ring
  simp_rw [Finset.sum_congr rfl he]
  rw [← Finset.sum_div, ← Int.cast_sum, ← Finset.mul_sum,
    endpointEntropyState_interval b L up a z haz]

end SingularValueBounds.KL.Certificates
