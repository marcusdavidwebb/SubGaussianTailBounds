import SingularValueBounds.KL.Certificates.EndpointMeanEntropyAssembly
import SingularValueBounds.KL.Certificates.IntegerRoundedLogEvaluation
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer entropy certificates, independently checked by Lean's kernel. -/
namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy20
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨436,4420,200⟩,⟨4420,4652,195⟩,⟨4652,4911,190⟩,⟨4911,5199,185⟩,⟨5199,5524,180⟩,⟨5524,5893,175⟩,⟨5893,6313,170⟩,⟨6313,6799,165⟩,⟨6799,7366,160⟩,⟨7366,8000,155⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1571840839409314) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2358595966603827)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1924570939395984) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2611934763438933))) (.branch (.branch (.leaf 1739090497770472) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2130316998283040) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2024774812592717) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1653305599515592) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2481964004526457)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2241488360990764)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2748869663854115))) (.branch (.branch (.leaf 1829429843997391) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2185180231163324)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2679508330387067))) (.branch (.branch (.leaf 1783675721471431) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1612047358373583) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2419476474500587)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1974023157263926) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1876384189408445) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2299280284093965)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2076860806609642) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1695643683150986) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2546101915982342)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 20) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 20*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 20) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 20) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 20 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 20) (endpointSmallBound 20)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 20 :=
  endpointSmallNumerical_le_of_runs 20 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy20

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy21
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨436,4219,200⟩,⟨4219,4441,195⟩,⟨4441,4687,190⟩,⟨4687,4963,185⟩,⟨4963,5273,180⟩,⟨5273,5625,175⟩,⟨5625,6026,170⟩,⟨6026,6490,165⟩,⟨6490,7031,160⟩,⟨7031,7670,155⟩,⟨7670,8000,150⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1572187851666578) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2360477704908312)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1925463082210563) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2614546241491494))) (.branch (.branch (.leaf 1739665853085315) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2131635964187961) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2025865102764823) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1653756927293763) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2484187579748612)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2243069910460562)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2751919935556918))) (.branch (.branch (.leaf 1830151281034808) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2186626027044916)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2682332525524524))) (.branch (.branch (.leaf 1784321205820304) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1612444202394589) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2421523658292147)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1975010757210974) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1877187731281636) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2301006983077471)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2078061414531314) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1696154419423188) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2548513392757807)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 21) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 21*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 21) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 21) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 21 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 21) (endpointSmallBound 21)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 21 :=
  endpointSmallNumerical_le_of_runs 21 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy21

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy22
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨437,4035,200⟩,⟨4035,4248,195⟩,⟨4248,4484,190⟩,⟨4484,4747,185⟩,⟨4747,5044,180⟩,⟨5044,5380,175⟩,⟨5380,5764,170⟩,⟨5764,6208,165⟩,⟨6208,6725,160⟩,⟨6725,7336,155⟩,⟨7336,8000,150⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1572551570760699) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2362453590808028)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1926398972192530) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2617289783073443))) (.branch (.branch (.leaf 1740269157697812) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2133020246461628) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2027009117179821) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1654230080337210) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2486522996269585)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2244730178766039)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2755125312501717))) (.branch (.branch (.leaf 1830907926722036) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2188143601246402)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2685299933286991))) (.branch (.branch (.leaf 1784998118584756) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1612860194357314) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2423673537550467)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1976046902432876) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1878030581587538) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2302819847630786)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2079321329133501) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1696689909484882) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2551046488368525)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 22) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 22*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 22) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 22) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 22 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 22) (endpointSmallBound 22)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 22 :=
  endpointSmallNumerical_le_of_runs 22 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy22

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy23
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨437,3867,200⟩,⟨3867,4071,195⟩,⟨4071,4297,190⟩,⟨4297,4550,185⟩,⟨4550,4834,180⟩,⟨4834,5156,175⟩,⟨5156,5524,170⟩,⟨5524,5949,165⟩,⟨5949,6445,160⟩,⟨6445,7031,155⟩,⟨7031,7734,150⟩,⟨7734,8000,145⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1572932075581668) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2364524567062371)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1927378926188072) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2620166905673254))) (.branch (.branch (.leaf 1740900577923360) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2134470406650439) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2028207280916784) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1654725174938145) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2488971455779631)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2246469897821989)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2758487694961191))) (.branch (.branch (.leaf 1831700013040622) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2189733595872567)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2688412253493284))) (.branch (.branch (.leaf 1785706656749087) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1613295430445553) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2425927177970273)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1977131960684256) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1878913012095009) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2304719709582897)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2080641039865454) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1697250292884631) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2553702554696403)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 23) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 23*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 23) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 23) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 23 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 23) (endpointSmallBound 23)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 23 :=
  endpointSmallNumerical_le_of_runs 23 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy23

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy24
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨438,3713,200⟩,⟨3713,3908,195⟩,⟨3908,4125,190⟩,⟨4125,4368,185⟩,⟨4368,4641,180⟩,⟨4641,4950,175⟩,⟨4950,5303,170⟩,⟨5303,5711,165⟩,⟨5711,6187,160⟩,⟨6187,6750,155⟩,⟨6750,7425,150⟩,⟨7425,8000,145⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1573329448890563) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2366691627420853)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1928403277350836) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2623179210959929))) (.branch (.branch (.leaf 1741560288432517) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2135987035922144) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2029460041201704) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1655242333161700) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2491534225787451)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2248289838635740)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2762009089978002))) (.branch (.branch (.leaf 1832527783766615) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2191396687110110)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2691671280859541))) (.branch (.branch (.leaf 1786447027252638) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1613750011589389) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2428285703248702)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1978266318763306) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1879835308474914) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2306707445468782)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2082021061834849) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1697835716140223) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2556483018139961)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 24) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 24*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 24) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 24) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 24 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 24) (endpointSmallBound 24)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 24 :=
  endpointSmallNumerical_le_of_runs 24 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy24

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy25
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨438,3570,200⟩,⟨3570,3758,195⟩,⟨3758,3966,190⟩,⟨3966,4200,185⟩,⟨4200,4462,180⟩,⟨4462,4759,175⟩,⟨4759,5099,170⟩,⟨5099,5492,165⟩,⟨5492,5949,160⟩,⟨5949,6490,155⟩,⟨6490,7139,150⟩,⟨7139,7932,145⟩,⟨7932,8000,140⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1573743777367815) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2368955817913499)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1929472375450757) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2626328387189991))) (.branch (.branch (.leaf 1742248472383758) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2137570755721500) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2030767867863048) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1655781682929170) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2494212641397744)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2250190812234042)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2765691614596000))) (.branch (.branch (.leaf 1833391494677365) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2193133586009278)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2695078907793732))) (.branch (.branch (.leaf 1787219447156061) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1614224043530254) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2430750296602807)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1979450382887760) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1880797770553113) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2308783977629217)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2083461936355934) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1698446332843729) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2559389381686369)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 25) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 25*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 25) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 25) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 25 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 25) (endpointSmallBound 25)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 25 :=
  endpointSmallNumerical_le_of_runs 25 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy25

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy26
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨439,3438,200⟩,⟨3438,3618,195⟩,⟨3618,3819,190⟩,⟨3819,4044,185⟩,⟨4044,4297,180⟩,⟨4297,4583,175⟩,⟨4583,4911,170⟩,⟨4911,5288,165⟩,⟨5288,5729,160⟩,⟨5729,6250,155⟩,⟨6250,6875,150⟩,⟨6875,7638,145⟩,⟨7638,8000,140⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1574175151666795) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2371318238225859)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1930586587201147) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2629616211771977))) (.branch (.branch (.leaf 1742965321562836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2139222218464767) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2032131253813085) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1656343358104532) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2497008107197218)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2252173670648378)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2769537499301288))) (.branch (.branch (.leaf 1834291413766986) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2194945039312838)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2698637127368958))) (.branch (.branch (.leaf 1788024143816267) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1614717636888422) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2433322202381668)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1980684579093201) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1881800712577996) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2310950275373855)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2084964231529187) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1699082303771905) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2562423227113928)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 26) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 26*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 26) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 26) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 26 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 26) (endpointSmallBound 26)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 26 :=
  endpointSmallNumerical_le_of_runs 26 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy26

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy27
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨440,3315,200⟩,⟨3315,3489,195⟩,⟨3489,3683,190⟩,⟨3683,3900,185⟩,⟨3900,4143,180⟩,⟨4143,4420,175⟩,⟨4420,4735,170⟩,⟨4735,5099,165⟩,⟨5099,5524,160⟩,⟨5524,6026,155⟩,⟨6026,6629,150⟩,⟨6629,7366,145⟩,⟨7366,8000,140⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1574623666467560) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2373780043152267)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1931746296604259) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2633044553990358))) (.branch (.branch (.leaf 1743711036530454) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2140942108275122) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2033550715557175) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1656927498586457) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2499922099259093)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2254239307956961)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2773549091686329))) (.branch (.branch (.leaf 1835227821476180) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2196831830332565)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2702348036487090))) (.branch (.branch (.leaf 1788861355069627) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1615230907234208) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2436002727778045)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1981969353652584) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1882844463501782) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2313207356215875)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2086528542854316) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1699743797002900) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2565586217331663)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 27) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 27*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 27) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 27) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 27 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 27) (endpointSmallBound 27)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 27 :=
  endpointSmallNumerical_le_of_runs 27 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy27

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy28
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨440,3201,200⟩,⟨3201,3369,195⟩,⟨3369,3556,190⟩,⟨3556,3765,185⟩,⟨3765,4001,180⟩,⟨4001,4267,175⟩,⟨4267,4572,170⟩,⟨4572,4924,165⟩,⟨4924,5334,160⟩,⟨5334,5819,155⟩,⟨5819,6401,150⟩,⟨6401,7112,145⟩,⟨7112,8000,140⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1575089420534672) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2376342444139893)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1932951905314588) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2636615377900630))) (.branch (.branch (.leaf 1744485826776785) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2142731141758874) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2035026793730475) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1657534250404415) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2502956167269291)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2256388661387347)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2777728860348507))) (.branch (.branch (.leaf 1836201010931823) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2198794779877458)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2706213839242782))) (.branch (.branch (.leaf 1789731329426726) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1615763975163281) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2438793244641216)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1983305173520033) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1883929367277577) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2315556287178450)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2088155493877659) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1700430988039595) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2568880098865071)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 28) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 28*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 28) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 28) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 28 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 28) (endpointSmallBound 28)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 28 :=
  endpointSmallNumerical_le_of_runs 28 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy28

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy29
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨441,3094,200⟩,⟨3094,3257,195⟩,⟨3257,3438,190⟩,⟨3438,3640,185⟩,⟨3640,3867,180⟩,⟨3867,4125,175⟩,⟨4125,4420,170⟩,⟨4420,4759,165⟩,⟨4759,5156,160⟩,⟨5156,5625,155⟩,⟨5625,6187,150⟩,⟨6187,6875,145⟩,⟨6875,7734,140⟩,⟨7734,8000,135⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1575572516777878) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2379006710920757)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1934203833022855) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2640330745404362))) (.branch (.branch (.leaf 1745289910884267) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2144590068825935) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2036560053664599) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1658163765819947) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2506111936781020)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2258622712484173)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2782079399034038))) (.branch (.branch (.leaf 1837211288200735) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2200834747233718)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2710236850498729))) (.branch (.branch (.leaf 1790634326275322) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1616316966374593) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2441695191398987)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1984692526798151) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1885055783172076) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2317998186177877)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2089845736875476) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1701144059937295) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2572306704491650)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 29) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 29*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 29) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 29) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 29 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 29) (endpointSmallBound 29)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 29 :=
  endpointSmallNumerical_le_of_runs 29 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy29

