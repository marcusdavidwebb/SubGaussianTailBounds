import SingularValueBounds.KL.Certificates.EndpointMeanEntropyAssembly
import SingularValueBounds.KL.Certificates.IntegerRoundedLogEvaluation
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer entropy certificates, independently checked by Lean's kernel. -/
namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy10
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨432,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1569274917320087) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2344783525360989)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1917997020598138) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2592805692882089))) (.branch (.branch (.leaf 1734843308984975) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2120616243434922) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2016748272434955) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1649971109847305) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2465659163541761)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2229867729514357)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2726550498200413))) (.branch (.branch (.leaf 1824108988946443) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2174551833992808)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2658832188069378))) (.branch (.branch (.leaf 1778912933433697) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1609114175518874) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2404457296669022)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1966749203976656) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1870460444981188) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2286599472275276)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2068026312989497) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1691871876728748) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2528428498039240)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 10) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 10*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 10) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 10) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 10 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 10) (endpointSmallBound 10)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 10 :=
  endpointSmallNumerical_le_of_runs 10 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy10

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy11
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨432,6111,200⟩,⟨6111,8000,195⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1569458379262194) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2345765202488968)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1918465719660222) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2594162923801913))) (.branch (.branch (.leaf 1735146561864981) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2121306812266797) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2017320104268627) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1650209361880681) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2466817007481387)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2230694307705741)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2728132676434776))) (.branch (.branch (.leaf 1824488629246619) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2175308138513426)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2660298543605405))) (.branch (.branch (.leaf 1779252879059181) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1609323825627215) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2405524293436273)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1967267617640903) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1870882945950569) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2287501094016186)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2068655461894481) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1692141281805167) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2529682991260477)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 11) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 11*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 11) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 11) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 11 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 11) (endpointSmallBound 11)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 11 :=
  endpointSmallNumerical_le_of_runs 11 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy11

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy12
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨432,6111,200⟩,⟨6111,7515,195⟩,⟨7515,8000,185⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1569657962832838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2346834170390639)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1918975837687081) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2595641240853982))) (.branch (.branch (.leaf 1735476536025655) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2122058591894492) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2017942544614685) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1650468578500342) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2468077976056408)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2231594267381176)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2729856251548949))) (.branch (.branch (.leaf 1824901769419708) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2176131532841303)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2661895832374123))) (.branch (.branch (.leaf 1779622800366723) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1609551911000649) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2406686245061885)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1967831877646366) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1871342755931305) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2288482823322715)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2069340334459193) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1692434409072649) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2531049310512025)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 12) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 12*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 12) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 12) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 12 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 12) (endpointSmallBound 12)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 12 :=
  endpointSmallNumerical_le_of_runs 12 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy12

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy13
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨433,6111,200⟩,⟨6111,6978,195⟩,⟨6978,7799,185⟩,⟨7799,8000,180⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1569873710416647) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2347990917661260)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1919527541993888) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2597241422739669))) (.branch (.branch (.leaf 1735833320071317) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2122871876137349) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2018615816922490) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1650748821926093) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2469442689002071)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2232567989694122)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2731722193724846))) (.branch (.branch (.leaf 1825348532514060) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2177022352154962)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2663624924433940))) (.branch (.branch (.leaf 1780022802071244) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1609798483209210) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2407943702504125)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1968442177751039) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1871840018756656) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2289545092342135)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2070081187376941) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1692751333035795) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2532528151256790)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 13) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 13*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 13) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 13) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 13 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 13) (endpointSmallBound 13)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 13 :=
  endpointSmallNumerical_le_of_runs 13 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy13

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy14
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨433,6111,200⟩,⟨6111,6513,195⟩,⟨6513,7279,185⟩,⟨7279,7734,180⟩,⟨7734,8000,175⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1570105667905007) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2349235974699179)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1920121013961310) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2598964315404724))) (.branch (.branch (.leaf 1736217009991891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2123746983728805) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2019340163506878) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1651050159543767) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2470911819327132)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2233615888264187)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2733731557320084))) (.branch (.branch (.leaf 1825829051877741) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2177980960119944)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2665486765155233))) (.branch (.branch (.leaf 1780452997634225) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1610063598094973) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2409297263970487)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1969098728036256) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1872374890324691) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2290688370113036)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2070878299059666) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1693092134396988) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2534120268873309)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 14) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 14*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 14) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 14) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 14 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 14) (endpointSmallBound 14)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 14 :=
  endpointSmallNumerical_le_of_runs 14 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy14

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy15
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨433,5801,200⟩,⟨5801,6106,195⟩,⟨6106,6430,190⟩,⟨6430,6824,185⟩,⟨6824,7251,180⟩,⟨7251,8000,170⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1570353884718910) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2350569914354766)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1920756449194965) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2600810833220876))) (.branch (.branch (.leaf 1736627709233357) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2124684258653727) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2020115845781392) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1651372663947471) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2472486094187382)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2234738409644419)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2735885482435872))) (.branch (.branch (.leaf 1826343471266886) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2179007749285050)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2667482376580326))) (.branch (.branch (.leaf 1780913509351855) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1610347315807076) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2410747575672187)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1969801755102300) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1872947538732041) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2291913163118198)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2071731969920106) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1693456900111196) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2535826479679699)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 15) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 15*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 15) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 15) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 15 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 15) (endpointSmallBound 15)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 15 :=
  endpointSmallNumerical_le_of_runs 15 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy15

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy16
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨434,5459,200⟩,⟨5459,5747,195⟩,⟨5747,6066,190⟩,⟨6066,6423,185⟩,⟨6423,6824,180⟩,⟨6824,6978,175⟩,⟨6978,7799,170⟩,⟨7799,8000,165⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1570618413840103) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2351993352632814)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1921434057699839) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2602781960273185))) (.branch (.branch (.leaf 1737065528772035) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2125684070507959) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2020943144513628) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1651716412988755) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2474166295843669)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2235936033831733)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2738185196624616))) (.branch (.branch (.leaf 1826891944961660) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2180103141510485)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2669612858910230))) (.branch (.branch (.leaf 1781404468448251) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1610649700838151) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2412295332645968)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1970551502276030) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1873558144413456) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2293220015882164)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2072642522673663) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1693845723448204) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2537647662042178)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 16) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 16*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 16) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 16) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 16 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 16) (endpointSmallBound 16)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 16 :=
  endpointSmallNumerical_le_of_runs 16 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy16

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy17
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨434,5156,200⟩,⟨5156,5427,195⟩,⟨5427,5729,190⟩,⟨5729,6066,185⟩,⟨6066,6445,180⟩,⟨6445,6875,175⟩,⟨6875,7366,170⟩,⟨7366,7932,165⟩,⟨7932,8000,160⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1570899311840732) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2353506949451176)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1922154064068214) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2604878751747690))) (.branch (.branch (.leaf 1737530587198675) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2126746814890357) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2021822360096432) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1652081489827149) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2475953262696855)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2237209274813616)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2740632016743910))) (.branch (.branch (.leaf 1827474637891336) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2181267588433555)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2671879392108768))) (.branch (.branch (.leaf 1781926015176858) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1610970822065770) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2413941279640567)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1971348229840330) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1874206900298314) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2294609511617229)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2073610302667811) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1694258704055567) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2539584757575374)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 17) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 17*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 17) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 17) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 17 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 17) (endpointSmallBound 17)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 17 :=
  endpointSmallNumerical_le_of_runs 17 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy17

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy18
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨435,4885,200⟩,⟨4885,5142,195⟩,⟨5142,5427,190⟩,⟨5427,5747,185⟩,⟨5747,6106,180⟩,⟨6106,6513,175⟩,⟨6513,6978,170⟩,⟨6978,7515,165⟩,⟨7515,8000,160⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1571196638916303) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2355111409457199)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1922916707679464) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2607102335435021))) (.branch (.branch (.leaf 1738023010802831) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2127872913823089) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2022753812843165) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1652467982984514) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2477847890401274)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2238558681160315)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2743227350952196))) (.branch (.branch (.leaf 1828091725767197) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2182501571968605)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2674283237639812))) (.branch (.branch (.leaf 1782478298929704) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1611310752792999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2415686212073098)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1972192215275983) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1874894011973842) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2296082272922124)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2074635678232843) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1694695948029493) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2541638772439055)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 18) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 18*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 18) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 18) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 18 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 18) (endpointSmallBound 18)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 18 :=
  endpointSmallNumerical_le_of_runs 18 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy18

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy19
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨435,4641,200⟩,⟨4641,4885,195⟩,⟨4885,5156,190⟩,⟨5156,5459,185⟩,⟨5459,5801,180⟩,⟨5801,6187,175⟩,⟨6187,6629,170⟩,⟨6629,7139,165⟩,⟨7139,7734,160⟩,⟨7734,8000,155⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1571510458921985) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2356807482906680)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1923722242917037) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2609453913344563))) (.branch (.branch (.leaf 1738542933668119) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2129062816203136) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2023737843302121) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1652875986404930) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2479851133063015)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2239984836658457)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2745972700862366))) (.branch (.branch (.leaf 1828743395229197) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2183805604841167)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2676825740332553))) (.branch (.branch (.leaf 1783061478352827) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1611669570796640) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2417530977056321)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1973083753524117) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1875619697862160) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2297638962526293)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2075719041061199) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1695157567987984) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2543810778731072)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 19) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 19*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 19) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 19) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 19 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 19) (endpointSmallBound 19)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 19 :=
  endpointSmallNumerical_le_of_runs 19 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy19

