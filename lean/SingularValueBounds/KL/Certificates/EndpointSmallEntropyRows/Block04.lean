import SingularValueBounds.KL.Certificates.EndpointMeanEntropyAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanSmall
import SingularValueBounds.KL.Certificates.RoundedLogTwo

/-! Exact integer entropy certificates, independently checked by Lean's kernel. -/
namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy40
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨450,2264,200⟩,⟨2264,2383,195⟩,⟨2383,2515,190⟩,⟨2515,2663,185⟩,⟨2663,2830,180⟩,⟨2830,3018,175⟩,⟨3018,3234,170⟩,⟨3234,3483,165⟩,⟨3483,3773,160⟩,⟨3773,4116,155⟩,⟨4116,4527,150⟩,⟨4527,5030,145⟩,⟨5030,5659,140⟩,⟨5659,6467,135⟩,⟨6467,7545,130⟩,⟨7545,8000,125⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1582064944900559) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2415463999976874)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1951171498610110) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2691438181575278))) (.branch (.branch (.leaf 1756140403115209) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2169901905735596) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2057388276456453) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1666640962079585) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2549406489564094)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2289116475302711)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2842087951421654))) (.branch (.branch (.leaf 1850873491320040) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2228645250050815)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2765651329231498))) (.branch (.branch (.leaf 1802832547536506) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1623756131825403) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2481455766991415)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2003516999224636) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1900305312301284) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2351370470979012)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2112833360443829) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1710756341816141) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2619378971901157)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 40) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 40*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 40) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 40) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 40 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 40) (endpointSmallBound 40)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 40 :=
  endpointSmallNumerical_le_of_runs 40 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy40

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy41
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨451,2210,200⟩,⟨2210,2326,195⟩,⟨2326,2456,190⟩,⟨2456,2600,185⟩,⟨2600,2762,180⟩,⟨2762,2947,175⟩,⟨2947,3157,170⟩,⟨3157,3400,165⟩,⟨3400,3683,160⟩,⟨3683,4018,155⟩,⟨4018,4420,150⟩,⟨4420,4911,145⟩,⟨4911,5524,140⟩,⟨5524,6313,135⟩,⟨6313,7366,130⟩,⟨7366,8000,125⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1582765778283379) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2419473598067913)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1953019173042000) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2697089627719938))) (.branch (.branch (.leaf 1757316632173798) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2172671506901284) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2059661720671379) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1667557946019415) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2554180814883911)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2292461499315136)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2848742526196585))) (.branch (.branch (.leaf 1852357811824303) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2231692061395108)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2771787680171281))) (.branch (.branch (.leaf 1804156331905958) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1624559989041390) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2485834475069659)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2005569278533121) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1901963973057263) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2355035978044308)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2115345552197646) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1711797216778413) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2624576991425334)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 41) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 41*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 41) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 41) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 41 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 41) (endpointSmallBound 41)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 41 :=
  endpointSmallNumerical_le_of_runs 41 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy41

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy42
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨452,2159,200⟩,⟨2159,2272,195⟩,⟨2272,2398,190⟩,⟨2398,2539,185⟩,⟨2539,2698,180⟩,⟨2698,2878,175⟩,⟨2878,3084,170⟩,⟨3084,3321,165⟩,⟨3321,3597,160⟩,⟨3597,3924,155⟩,⟨3924,4317,150⟩,⟨4317,4796,145⟩,⟨4796,5396,140⟩,⟨5396,6167,135⟩,⟨6167,7194,130⟩,⟨7194,8000,125⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1583485701817230) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2423607812220863)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1954920478522464) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2702923119681480))) (.branch (.branch (.leaf 1758525914068829) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2175524246842194) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2062002262892970) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1668500295643755) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2559106184168771)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2295908680651651)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2855615413681757))) (.branch (.branch (.leaf 1853884517547924) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2234831121125837)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2778123505363900))) (.branch (.branch (.leaf 1805517613750851) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1625385911092677) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2490350481109917)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2007681623809942) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1903670384522616) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2358814410380574)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2117932516649487) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1712867110706294) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2629940943058748)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 42) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 42*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 42) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 42) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 42 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 42) (endpointSmallBound 42)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 42 :=
  endpointSmallNumerical_le_of_runs 42 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy42

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy43
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨453,2110,200⟩,⟨2110,2221,195⟩,⟨2221,2344,190⟩,⟨2344,2482,185⟩,⟨2482,2637,180⟩,⟨2637,2813,175⟩,⟨2813,3013,170⟩,⟨3013,3245,165⟩,⟨3245,3516,160⟩,⟨3516,3835,155⟩,⟨3835,4219,150⟩,⟨4219,4687,145⟩,⟨4687,5273,140⟩,⟨5273,6026,135⟩,⟨6026,7031,130⟩,⟨7031,8000,125⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1584224884519517) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2427868963139572)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1956876140398305) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2708942540126792))) (.branch (.branch (.leaf 1759768616838353) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2178461457551561) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2064410893476025) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1669468264115314) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2564185612635304)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2299459787558615)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2862711573747106))) (.branch (.branch (.leaf 1855454130521772) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2238063966278268)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2784663197298200))) (.branch (.branch (.leaf 1806916832624635) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1626234105689413) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2495006433513377)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2009854884326162) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1905425163502839) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2362707796430166)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2120595404347890) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1713966329873546) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2635474251975878)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 43) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 43*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 43) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 43) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 43 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 43) (endpointSmallBound 43)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 43 :=
  endpointSmallNumerical_le_of_runs 43 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy43

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy44
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨454,2063,200⟩,⟨2063,2171,195⟩,⟨2171,2292,190⟩,⟨2292,2427,185⟩,⟨2427,2578,180⟩,⟨2578,2750,175⟩,⟨2750,2947,170⟩,⟨2947,3173,165⟩,⟨3173,3438,160⟩,⟨3438,3750,155⟩,⟨3750,4125,150⟩,⟨4125,4583,145⟩,⟨4583,5156,140⟩,⟨5156,5893,135⟩,⟨5893,6875,130⟩,⟨6875,8000,125⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1584983500849116) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2432259469077049)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1958886910749271) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2715151945756139))) (.branch (.branch (.leaf 1761045121203511) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2181484523475453) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2066888640508897) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1670462113029924) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2569422246396200)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2303116660232727)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2870036195747949))) (.branch (.branch (.leaf 1857067191383251) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2241392195416077)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2791411348503812))) (.branch (.branch (.leaf 1808354443486095) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1627104787344230) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2499805093817533)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2012089941178597) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1907228949159624) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2366718248527600)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2123335410409224) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1715095190931403) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2641180494446444)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 44) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 44*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 44) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 44) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 44 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 44) (endpointSmallBound 44)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 44 :=
  endpointSmallNumerical_le_of_runs 44 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy44

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy45
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨455,2018,200⟩,⟨2018,2124,195⟩,⟨2124,2242,190⟩,⟨2242,2374,185⟩,⟨2374,2522,180⟩,⟨2522,2690,175⟩,⟨2690,2882,170⟩,⟨2882,3104,165⟩,⟨3104,3363,160⟩,⟨3363,3668,155⟩,⟨3668,4035,150⟩,⟨4035,4484,145⟩,⟨4484,5044,140⟩,⟨5044,5764,135⟩,⟨5764,6725,130⟩,⟨6725,8000,125⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1585761730823985) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2436781849790109)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1960953569218991) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2721555575191311))) (.branch (.branch (.leaf 1762355820902806) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2184594883390294) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2069436571074851) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1671482112619173) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2574819368079309)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2306881213566880)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2877594709481050))) (.branch (.branch (.leaf 1858724259910399) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2244817470906707)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2798372760859099))) (.branch (.branch (.leaf 1809830917123520) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1627998177527065) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2504749341418207)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2014387708316304) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1909082403679023) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2370847966201355)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2126153776060294) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1716254021169605) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2647063404502998)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 45) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 45*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 45) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 45) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 45 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 45) (endpointSmallBound 45)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 45 :=
  endpointSmallNumerical_le_of_runs 45 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy45

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy46
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨456,1975,200⟩,⟨1975,2079,195⟩,⟨2079,2194,190⟩,⟨2194,2323,185⟩,⟨2323,2469,180⟩,⟨2469,2633,175⟩,⟨2633,2821,170⟩,⟨2821,3038,165⟩,⟨3038,3291,160⟩,⟨3291,3590,155⟩,⟨3590,3949,150⟩,⟨3949,4388,145⟩,⟨4388,4937,140⟩,⟨4937,5642,135⟩,⟨5642,6582,130⟩,⟨6582,7898,125⟩,⟨7898,8000,120⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1586559760143396) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2441438730721890)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1963076923885186) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2728157857355556))) (.branch (.branch (.leaf 1763701123040659) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2187794032379537) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2072055792577618) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1672528541960996) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2580380402783512)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2310755440047547)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2885392796848509))) (.branch (.branch (.leaf 1860425915580622) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2248341521319079)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2805552455490293))) (.branch (.branch (.leaf 1811346740597876) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1628914504826865) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2509842178568424)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2016749133617412) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1910986212970871) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2375099239661007)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2129051790260221) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1717443158788745) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2653126881015320)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 46) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 46*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 46) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 46) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 46 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 46) (endpointSmallBound 46)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 46 :=
  endpointSmallNumerical_le_of_runs 46 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy46

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy47
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨457,1934,200⟩,⟨1934,2036,195⟩,⟨2036,2149,190⟩,⟨2149,2275,185⟩,⟨2275,2417,180⟩,⟨2417,2578,175⟩,⟨2578,2762,170⟩,⟨2762,2975,165⟩,⟨2975,3223,160⟩,⟨3223,3516,155⟩,⟨3516,3867,150⟩,⟨3867,4297,145⟩,⟨4297,4834,140⟩,⟨4834,5524,135⟩,⟨5524,6445,130⟩,⟨6445,7734,125⟩,⟨7734,8000,120⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1587377780315146) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2446232847425014)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1965257812172418) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2734963420378248))) (.branch (.branch (.leaf 1765081448451648) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2191083523914764) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2074747454132849) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1673601689199136) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2586108924392389)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2314741412812022)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2893436404282267))) (.branch (.branch (.leaf 1862172758154890) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2251966143951639)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2812955683303347))) (.branch (.branch (.leaf 1812902417705686) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1629854005119349) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2515086735671297)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2019175200019529) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1912941087401636) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2379474453481339)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2132030791406799) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1718662953184338) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2659374995199484)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 47) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 47*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 47) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 47) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 47 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 47) (endpointSmallBound 47)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 47 :=
  endpointSmallNumerical_le_of_runs 47 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy47

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy48
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨458,1894,200⟩,⟨1894,1994,195⟩,⟨1994,2105,190⟩,⟨2105,2229,185⟩,⟨2229,2368,180⟩,⟨2368,2526,175⟩,⟨2526,2706,170⟩,⟨2706,2914,165⟩,⟨2914,3157,160⟩,⟨3157,3444,155⟩,⟨3444,3788,150⟩,⟨3788,4209,145⟩,⟨4209,4735,140⟩,⟨4735,5412,135⟩,⟨5412,6313,130⟩,⟨6313,7576,125⟩,⟨7576,8000,120⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1588215988787703) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2451167050242029)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1967497101809007) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2741977101061262))) (.branch (.branch (.leaf 1766497232080733) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2194464972047683) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2077512748031422) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1674701851771848) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2592008662270717)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2318841288876313)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2901731755984847))) (.branch (.branch (.leaf 1863965408289572) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2255693207497083)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2820587936193572))) (.branch (.branch (.leaf 1814498469463078) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1630816921742062) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2520486276887402)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2021666926705855) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1914947762561773) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2383976090495703)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2135092169131192) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1719913765242858) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2665811998590783)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 48) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 48*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 48) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 48) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 48 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 48) (endpointSmallBound 48)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 48 :=
  endpointSmallNumerical_le_of_runs 48 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy48

namespace SingularValueBounds.KL.Certificates.EndpointSmallEntropy49
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨459,1857,200⟩,⟨1857,1954,195⟩,⟨1954,2063,190⟩,⟨2063,2184,185⟩,⟨2184,2321,180⟩,⟨2321,2475,175⟩,⟨2475,2652,170⟩,⟨2652,2856,165⟩,⟨2856,3094,160⟩,⟨3094,3375,155⟩,⟨3375,3713,150⟩,⟨3713,4125,145⟩,⟨4125,4641,140⟩,⟨4641,5303,135⟩,⟨5303,6187,130⟩,⟨6187,7425,125⟩,⟨7425,8000,120⟩]
private noncomputable def prefactorData : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 1589074589087746) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2456244309258760)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1969795691830385) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2749203954947272))) (.branch (.branch (.leaf 1767948923379892) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2197940053718891) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2080352911276661) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1675829336650227) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2598083508368424)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2323057312542263)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2910285368047008))) (.branch (.branch (.leaf 1865804508175924) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 2259524654853343)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 2828454958983233))) (.branch (.branch (.leaf 1816135434611376) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 1631803505676052) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2526044206075986)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2024225370350562) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 1917007000069195) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 2388606735912085)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2138237366186450) (.leaf 0)))) (.branch (.branch (.branch (.leaf 1721195967650630) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 2672442331512732)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactors (q : ℕ) : ℤ := prefactorData.get (q-90)

private theorem cover : EndpointRunsCover (endpointSmallCutoff 49) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 ∧ (r.rate-90)%5=0 := by decide +kernel
private theorem margins : ∀ r ∈ runs,
    (((r.stop-1:ℕ):ℚ)/200)*endpointSmallK 49*((r.rate:ℚ)/100-1) ≤ 58/25 := by decide +kernel
private theorem prefactorValues : ∀ r ∈ runs,
    endpointSmallPrefactorQ (endpointSmallK 49) ((r.rate:ℚ)/100) = fixedQ (prefactors r.rate) := by
  simp only [endpointSmallPrefactorQ,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int, expUpperRoundedQ_eq_integer]
  decide +kernel
private theorem totalBound : endpointEntropyByRuns (endpointSmallCutoff 49) prefactors runs+
    440/roundingScale ≤ endpointSmallTarget 49 := by decide +kernel

theorem numerical : entropyGridBoundQ (endpointSmallCutoff 49) (endpointSmallBound 49)
    (endpointDecayQ 90 8000) ≤ endpointSmallTarget 49 :=
  endpointSmallNumerical_le_of_runs 49 runs prefactors cover domains margins prefactorValues totalBound
end SingularValueBounds.KL.Certificates.EndpointSmallEntropy49

