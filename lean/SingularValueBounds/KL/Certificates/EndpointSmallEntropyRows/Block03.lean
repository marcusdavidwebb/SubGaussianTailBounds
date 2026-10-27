import SingularValueBounds.KL.Certificates.EndpointMeanEntropyAssembly
import SingularValueBounds.KL.Certificates.IntegerRoundedLogEvaluation
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer entropy certificates, independently checked by Lean's kernel. -/
namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy30
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨442,2994,200⟩,⟨2994,3152,195⟩,⟨3152,3327,190⟩,⟨3327,3522,185⟩,⟨3522,3742,180⟩,⟨3742,3992,175⟩,⟨3992,4277,170⟩,⟨4277,4606,165⟩,⟨4606,4990,160⟩,⟨4990,5443,155⟩,⟨5443,5988,150⟩,⟨5988,6653,145⟩,⟨6653,7484,140⟩,⟨7484,8000,135⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1576073062314533) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2381774173240806)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1935502517858501) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2644192819510775))) (.branch (.branch (.leaf 1746123516698081) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2146519673555393) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2038151085984307) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1658816203431983) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2509391111604434)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2260942488340845)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2786603431043950))) (.branch (.branch (.leaf 1838258972555687) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2202952631199703)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2714419499679963))) (.branch (.branch (.leaf 1791570616094564) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1616890011752771) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2444710075094175)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1986131923229750) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1886224086093752) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2320534223485871)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2091599953574485) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1701883203439803) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2575867956038075)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 30) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 30*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 30) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 30) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 30 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 30) (endpointSmallBound 30)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 30 :=
  endpointSmallNumerical_le_of_runs 30 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy30

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy31
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨442,2901,200⟩,⟨2901,3053,195⟩,⟨3053,3223,190⟩,⟨3223,3412,185⟩,⟨3412,3626,180⟩,⟨3626,3867,175⟩,⟨3867,4143,170⟩,⟨4143,4462,165⟩,⟨4462,4834,160⟩,⟨4834,5273,155⟩,⟨5273,5801,150⟩,⟨5801,6445,145⟩,⟨6445,7251,140⟩,⟨7251,8000,135⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1576591168536277) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2384646222687709)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1936848416814605) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2648203867799230))) (.branch (.branch (.leaf 1746986881505344) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2148520775108798) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2039800507237198) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1659491728288802) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2512795476338019)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2263349062902619)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2791303813914818))) (.branch (.branch (.leaf 1839344396754836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2205149371179181)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2718764334806080))) (.branch (.branch (.leaf 1792540480679603) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1617483247454441) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2447839473538884)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1987623894716217) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1887434666938777) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2323165623275321)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2093418855911795) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1702648617120451) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2579565867344265)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 31) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 31*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 31) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 31) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 31 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 31) (endpointSmallBound 31)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 31 :=
  endpointSmallNumerical_le_of_runs 31 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy31

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy32
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨443,2813,200⟩,⟨2813,2961,195⟩,⟨2961,3125,190⟩,⟨3125,3309,185⟩,⟨3309,3516,180⟩,⟨3516,3750,175⟩,⟨3750,4018,170⟩,⟨4018,4327,165⟩,⟨4327,4687,160⟩,⟨4687,5113,155⟩,⟨5113,5625,150⟩,⟨5625,6250,145⟩,⟨6250,7031,140⟩,⟨7031,8000,135⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1577126951177607) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2387624314624802)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1938242006193646) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2652366266089592))) (.branch (.branch (.leaf 1747880252222756) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2150594228692614) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2041508960554871) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1660190512003136) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2516326899049220)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2265843558341373)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2796183544391007))) (.branch (.branch (.leaf 1840467907335278) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2207425948334165)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2723274026768721))) (.branch (.branch (.leaf 1793544213377212) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1618096814997920) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2451085037594697)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1989168995862115) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1888687932953964) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2325893665254111)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2095303186834824) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1703440507530461) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2583402547405193)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 32) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 32*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 32) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 32) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 32 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 32) (endpointSmallBound 32)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 32 :=
  endpointSmallNumerical_le_of_runs 32 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy32

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy33
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨444,2730,200⟩,⟨2730,2874,195⟩,⟨2874,3033,190⟩,⟨3033,3212,185⟩,⟨3212,3412,180⟩,⟨3412,3640,175⟩,⟨3640,3900,170⟩,⟨3900,4200,165⟩,⟨4200,4550,160⟩,⟨4550,4963,155⟩,⟨4963,5459,150⟩,⟨5459,6066,145⟩,⟨6066,6824,140⟩,⟨6824,7799,135⟩,⟨7799,8000,130⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1577680530388303) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2390709970234229)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1939683782076608) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2656682502335711))) (.branch (.branch (.leaf 1748803885593588) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2152740926572773) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2043277116350059) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1660912732874636) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2519987334112689)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2268427146506471)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2801245763705260))) (.branch (.branch (.leaf 1841629864920810) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2209783386800309)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2727951373871769))) (.branch (.branch (.leaf 1794582119332733) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1618730861357532) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2454448493585472)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1990767804548358) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1889984308117680) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2328719686390231)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2097253721143943) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1704259089354537) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2587380203699516)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 33) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 33*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 33) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 33) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 33 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 33) (endpointSmallBound 33)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 33 :=
  endpointSmallNumerical_le_of_runs 33 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy33

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy34
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨445,2652,200⟩,⟨2652,2791,195⟩,⟨2791,2947,190⟩,⟨2947,3120,185⟩,⟨3120,3315,180⟩,⟨3315,3536,175⟩,⟨3536,3788,170⟩,⟨3788,4080,165⟩,⟨4080,4420,160⟩,⟨4420,4821,155⟩,⟨4821,5303,150⟩,⟨5303,5893,145⟩,⟨5893,6629,140⟩,⟨6629,7576,135⟩,⟨7576,8000,130⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1578252030808583) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2393904778676378)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1941174260814405) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2661155180752899))) (.branch (.branch (.leaf 1749758048393107) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2154961799143484) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2045105673049063) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1661658576015931) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2523778825213971)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2271101050456380)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2806493763187523))) (.branch (.branch (.leaf 1842830644544965) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2212222754969325)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2732799306649054))) (.branch (.branch (.leaf 1795654515748846) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1619385539062026) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2457931645847530)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1992420922534336) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1891324233539689) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2331645082733276)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2099271266379673) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1705104585573134) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2591501145716357)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 34) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 34*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 34) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 34) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 34 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 34) (endpointSmallBound 34)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 34 :=
  endpointSmallNumerical_le_of_runs 34 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy34

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy35
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨445,2578,200⟩,⟨2578,2714,195⟩,⟨2714,2865,190⟩,⟨2865,3033,185⟩,⟨3033,3223,180⟩,⟨3223,3438,175⟩,⟨3438,3683,170⟩,⟨3683,3966,165⟩,⟨3966,4297,160⟩,⟨4297,4687,155⟩,⟨4687,5156,150⟩,⟨5156,5729,145⟩,⟨5729,6445,140⟩,⟨6445,7366,135⟩,⟨7366,8000,130⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1578841581647650) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2397210399371931)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1942713979545111) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2665787026192756))) (.branch (.branch (.leaf 1750743017644450) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2157257816052176) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2046995357862486) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1662428233486335) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2527703508529022)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2273866546073455)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2811930990219981))) (.branch (.branch (.leaf 1844070635989020) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2214745166839602)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2737820892975155))) (.branch (.branch (.leaf 1796761732156693) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1620061006297063) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2461536379428581)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1994128976090467) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1892708167880857) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2334671311337676)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2101356663755867) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1705977227632394) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2595767788689737)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 35) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 35*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 35) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 35) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 35 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 35) (endpointSmallBound 35)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 35 :=
  endpointSmallNumerical_le_of_runs 35 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy35

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy36
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨446,2509,200⟩,⟨2509,2641,195⟩,⟨2641,2787,190⟩,⟨2787,2951,185⟩,⟨2951,3136,180⟩,⟨3136,3345,175⟩,⟨3345,3584,170⟩,⟨3584,3859,165⟩,⟨3859,4181,160⟩,⟨4181,4561,155⟩,⟨4561,5017,150⟩,⟨5017,5574,145⟩,⟨5574,6271,140⟩,⟨6271,7167,135⟩,⟨7167,8000,130⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1579449316765717) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2400628564412099)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1944303496735972) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2670580888782035))) (.branch (.branch (.leaf 1751759080843963) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2159629987384976) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2048946927594477) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1663221904430047) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2531763616088446)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2276724963766969)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2817561054561585))) (.branch (.branch (.leaf 1845350244136875) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2217351783439869)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2743019343489101))) (.branch (.branch (.leaf 1797904110699665) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1620757427012628) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2465264662939165)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1995892616662577) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1894136587792652) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2337799892292958)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2103510789141726) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1706877255621960) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2600182657555328)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 36) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 36*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 36) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 36) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 36 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 36) (endpointSmallBound 36)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 36 :=
  endpointSmallNumerical_le_of_runs 36 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy36

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy37
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨447,2443,200⟩,⟨2443,2571,195⟩,⟨2571,2714,190⟩,⟨2714,2874,185⟩,⟨2874,3053,180⟩,⟨3053,3257,175⟩,⟨3257,3489,170⟩,⟨3489,3758,165⟩,⟨3758,4071,160⟩,⟨4071,4441,155⟩,⟨4441,4885,150⟩,⟨4885,5427,145⟩,⟨5427,6106,140⟩,⟨6106,6978,135⟩,⟨6978,8000,130⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1580075374759396) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2404161081104745)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1945943392752280) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2675539748839415))) (.branch (.branch (.leaf 1752806536196799) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2162079364913737) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2050961169494169) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1664039795220811) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2535961479337578)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2279677690269681)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2823387735064616))) (.branch (.branch (.leaf 1846669889346223) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2220043814329176)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2748398017348716))) (.branch (.branch (.leaf 1799082006430116) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1621474971034855) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2469118551568663)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1997712521569738) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1895609988378473) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2341032410865781)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2105734554094366) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1707804918460211) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2604748391139893)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 37) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 37*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 37) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 37) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 37 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 37) (endpointSmallBound 37)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 37 :=
  endpointSmallNumerical_le_of_runs 37 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy37

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy38
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨448,2380,200⟩,⟨2380,2505,195⟩,⟨2505,2644,190⟩,⟨2644,2800,185⟩,⟨2800,2975,180⟩,⟨2975,3173,175⟩,⟨3173,3400,170⟩,⟨3400,3661,165⟩,⟨3661,3966,160⟩,⟨3966,4327,155⟩,⟨4327,4759,150⟩,⟨4759,5288,145⟩,⟨5288,5949,140⟩,⟨5949,6799,135⟩,⟨6799,7932,130⟩,⟨7932,8000,125⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1580719899050657) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2407809834664067)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1947634270453876) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2680666722088395))) (.branch (.branch (.leaf 1753885692863651) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2164607043408938) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2053038902149430) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1664882119613447) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2540299532904022)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2282726170531229)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2829414986808770))) (.branch (.branch (.leaf 1848030007837312) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2222822519176844)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2753960428336328))) (.branch (.branch (.leaf 1800295787620749) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1622213814182282) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2473100190273669)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1999589394736453) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1897128883676778) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2344370519761223)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2108028906944912) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1708760474088263) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2609467746599631)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 38) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 38*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 38) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 38) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 38 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 38) (endpointSmallBound 38)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 38 :=
  endpointSmallNumerical_le_of_runs 38 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy38

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy39
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨449,2321,200⟩,⟨2321,2443,195⟩,⟨2443,2578,190⟩,⟨2578,2730,185⟩,⟨2730,2901,180⟩,⟨2901,3094,175⟩,⟨3094,3315,170⟩,⟨3315,3570,165⟩,⟨3570,3867,160⟩,⟨3867,4219,155⟩,⟨4219,4641,150⟩,⟨4641,5156,145⟩,⟨5156,5801,140⟩,⟨5801,6629,135⟩,⟨6629,7734,130⟩,⟨7734,8000,125⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1581383037979499) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2411576791051630)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1949376755820876) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2685965065184132))) (.branch (.branch (.leaf 1754996871217968) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2167214162021207) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2055180976426578) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1665749098901053) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2544780318584372)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2285871909714900)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2835646948679647))) (.branch (.branch (.leaf 1849431052100030) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2225689209426799)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2759710251339865))) (.branch (.branch (.leaf 1801545836088838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1622974138387908) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2477211817148928)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2001523967461535) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1898693807167260) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2347815941508409)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2110394833940247) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1709744189672646) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2614343604120914)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 39) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 39*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 39) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 39) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 39 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 39) (endpointSmallBound 39)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 39 :=
  endpointSmallNumerical_le_of_runs 39 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy39

