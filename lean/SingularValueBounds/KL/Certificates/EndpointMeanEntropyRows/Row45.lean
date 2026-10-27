import SingularValueBounds.KL.Certificates.EndpointMeanEntropyAssembly
import SingularValueBounds.KL.Certificates.EndpointPrefactorEvaluation

-- Elaborate the finite corner checks sequentially.
set_option Elab.async false

/-! Exact integer entropy certificates, independently checked by Lean's kernel.
Each corner is checked separately. Adjacent boxes reuse their shared vertices after
checking that the previous rate table contains the same prefactor values. -/
namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨953,960,126⟩,⟨960,1003,127⟩,⟨1003,1049,128⟩,⟨1049,1100,129⟩,⟨1100,1157,130⟩,⟨1157,1220,131⟩,⟨1220,1291,132⟩,⟨1291,1372,133⟩,⟨1372,1464,134⟩,⟨1464,1535,135⟩,⟨1535,1553,135⟩,⟨1553,1562,135⟩,⟨1562,1566,135⟩,⟨1566,1571,135⟩,⟨1571,1607,135⟩,⟨1607,1655,134⟩,⟨1655,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2789005706794772) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3312086287273619) (.leaf 0))) (.branch (.branch (.leaf 2440105165972225) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3020411374317988) (.leaf 0))) (.branch (.branch (.leaf 2303757274603540) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3696592303397625) (.leaf 0))) (.branch (.branch (.leaf 2599369074180581) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2898551903983445) (.leaf 0))) (.branch (.branch (.leaf 2242514356790082) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3489803424728761) (.leaf 0))) (.branch (.branch (.leaf 2516475372112310) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3157135348086703) (.leaf 0))) (.branch (.branch (.leaf 2369428633604468) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2689797129066954) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2842374478510931) (.leaf 0))) (.branch (.branch (.leaf 2213398286932189) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3397755442564059) (.leaf 0))) (.branch (.branch (.leaf 2477530415122909) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3086727639007901) (.leaf 0))) (.branch (.branch (.leaf 2336005681479854) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3813573859366829) (.leaf 0))) (.branch (.branch (.leaf 2643569698159205) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2957798801732941) (.leaf 0))) (.branch (.branch (.leaf 2272614590579405) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3589077588475432) (.leaf 0))) (.branch (.branch (.leaf 2557048402175216) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3232081824711024) (.leaf 0))) (.branch (.branch (.leaf 2404101146524478) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2738214893065295) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2818607133879920) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3358471066023575) (.leaf 0))) (.branch (.branch (.leaf 2460145334114305) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3057101361997020) (.leaf 0))) (.branch (.branch (.leaf 2320466508736320) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3756924021352465) (.leaf 0))) (.branch (.branch (.leaf 2623596132504776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2931439111352512) (.leaf 0))) (.branch (.branch (.leaf 2257807560005680) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3542477930062482) (.leaf 0))) (.branch (.branch (.leaf 2538484610179762) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3198268893212346) (.leaf 0))) (.branch (.branch (.leaf 2387712036100205) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2716535977796961) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2873560618080967) (.leaf 0))) (.branch (.branch (.leaf 2228036287890402) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3447137544122578) (.leaf 0))) (.branch (.branch (.leaf 2498526480964566) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3125550083815152) (.leaf 0))) (.branch (.branch (.leaf 2353480812283150) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3878390385808195) (.leaf 0))) (.branch (.branch (.leaf 2669012666064513) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2992515866984895) (.leaf 0))) (.branch (.branch (.leaf 2288597398300343) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3645383997828403) (.leaf 0))) (.branch (.branch (.leaf 2580132864463175) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3275727415226691) (.leaf 0))) (.branch (.branch (.leaf 2423238388774451) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2766337079297464) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2888506060313743) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3524079987806392) (.leaf 0))) (.branch (.branch (.leaf 2493757160824323) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3162264828961116) (.leaf 0))) (.branch (.branch (.leaf 2344400917268199) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4036611548268802) (.leaf 0))) (.branch (.branch (.leaf 2671535575078575) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3016777629828259) (.leaf 0))) (.branch (.branch (.leaf 2278090121528421) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3755361619786381) (.leaf 0))) (.branch (.branch (.leaf 2578533828054240) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3329331431575161) (.leaf 0))) (.branch (.branch (.leaf 2416030032197569) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2774234971100775) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2950712703527825) (.leaf 0))) (.branch (.branch (.leaf 2246722846825314) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3634451986391641) (.leaf 0))) (.branch (.branch (.leaf 2535196814497780) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3242769167448706) (.leaf 0))) (.branch (.branch (.leaf 2379505478826907) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4202246451868000) (.leaf 0))) (.branch (.branch (.leaf 2721566851309421) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3087128935633614) (.leaf 0))) (.branch (.branch (.leaf 2310623863788048) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3888642518429330) (.leaf 0))) (.branch (.branch (.leaf 2623922529947567) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3422772713238193) (.leaf 0))) (.branch (.branch (.leaf 2454076431085756) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2829787492956487) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2921763686992995) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3579068905501076) (.leaf 0))) (.branch (.branch (.leaf 2515627200979459) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3204411053684163) (.leaf 0))) (.branch (.branch (.leaf 2362454058028846) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4111671604688215) (.leaf 0))) (.branch (.branch (.leaf 2698311337502300) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3054105714404106) (.leaf 0))) (.branch (.branch (.leaf 2294543026014913) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3819151683174322) (.leaf 0))) (.branch (.branch (.leaf 2602695739458070) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3377260694754115) (.leaf 0))) (.branch (.branch (.leaf 2435877707543589) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2804013606220896) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2985923009183275) (.leaf 0))) (.branch (.branch (.leaf 2262439763381664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3693586296188137) (.leaf 0))) (.branch (.branch (.leaf 2558176113032445) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3287669554948958) (.leaf 0))) (.branch (.branch (.leaf 2398429669443210) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4284216401482795) (.leaf 0))) (.branch (.branch (.leaf 2749790528478761) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3126760791072618) (.leaf 0))) (.branch (.branch (.leaf 2327854432747091) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3957698455896460) (.leaf 0))) (.branch (.branch (.leaf 2649347324765992) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3474047703065367) (.leaf 0))) (.branch (.branch (.leaf 2474904422885821) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2861239682585718) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 21) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 21 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 21 (0 : Fin 4)) (endpointMeanCornerA 45 21 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 21 (1 : Fin 4)) (endpointMeanCornerA 45 21 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 21 (2 : Fin 4)) (endpointMeanCornerA 45 21 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 21 (3 : Fin 4)) (endpointMeanCornerA 45 21 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 21 h) (endpointMeanCornerA 45 21 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 21) (prefactors h) runs ≤
      endpointMeanCorner 45 21 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 21 h ≤ endpointMeanCorner 45 21 h :=
  endpointMeanNumericCorner_le_of_runs 45 21 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨960,987,126⟩,⟨987,1031,127⟩,⟨1031,1079,128⟩,⟨1079,1132,129⟩,⟨1132,1191,130⟩,⟨1191,1257,131⟩,⟨1257,1330,132⟩,⟨1330,1414,133⟩,⟨1414,1509,134⟩,⟨1509,1607,135⟩,⟨1607,1655,134⟩,⟨1655,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2818607133879920) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3358471066023575) (.leaf 0))) (.branch (.branch (.leaf 2460145334114305) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3057101361997020) (.leaf 0))) (.branch (.branch (.leaf 2320466508736320) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3756924021352465) (.leaf 0))) (.branch (.branch (.leaf 2623596132504776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2931439111352512) (.leaf 0))) (.branch (.branch (.leaf 2257807560005680) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3542477930062482) (.leaf 0))) (.branch (.branch (.leaf 2538484610179762) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3198268893212346) (.leaf 0))) (.branch (.branch (.leaf 2387712036100205) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2716535977796961) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2873560618080967) (.leaf 0))) (.branch (.branch (.leaf 2228036287890402) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3447137544122578) (.leaf 0))) (.branch (.branch (.leaf 2498526480964566) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3125550083815152) (.leaf 0))) (.branch (.branch (.leaf 2353480812283150) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3878390385808195) (.leaf 0))) (.branch (.branch (.leaf 2669012666064513) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2992515866984895) (.leaf 0))) (.branch (.branch (.leaf 2288597398300343) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3645383997828403) (.leaf 0))) (.branch (.branch (.leaf 2580132864463175) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3275727415226691) (.leaf 0))) (.branch (.branch (.leaf 2423238388774451) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2766337079297464) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2873749184337001) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3445289424125950) (.leaf 0))) (.branch (.branch (.leaf 2497350691377892) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3125595420779166) (.leaf 0))) (.branch (.branch (.leaf 2351445957154830) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3870213443047572) (.leaf 0))) (.branch (.branch (.leaf 2668644757425262) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2992765017866260) (.leaf 0))) (.branch (.branch (.leaf 2286144333784274) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3641219213938591) (.leaf 0))) (.branch (.branch (.leaf 2579376296883115) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3275153304684496) (.leaf 0))) (.branch (.branch (.leaf 2421632171868885) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2766298503193694) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2931683936821503) (.leaf 0))) (.branch (.branch (.leaf 2255151152091847) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3539634490804943) (.leaf 0))) (.branch (.branch (.leaf 2537520863549145) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3198068795078389) (.leaf 0))) (.branch (.branch (.leaf 2385890652747218) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4000216202543045) (.leaf 0))) (.branch (.branch (.leaf 2716342429610206) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3057289546600049) (.leaf 0))) (.branch (.branch (.leaf 2318220835203921) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3751021303241161) (.leaf 0))) (.branch (.branch (.leaf 2623039247068261) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3357361536437234) (.leaf 0))) (.branch (.branch (.leaf 2458754797722892) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2818698309822963) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2921763686992995) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3579068905501076) (.leaf 0))) (.branch (.branch (.leaf 2515627200979459) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3204411053684163) (.leaf 0))) (.branch (.branch (.leaf 2362454058028846) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4111671604688215) (.leaf 0))) (.branch (.branch (.leaf 2698311337502300) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3054105714404106) (.leaf 0))) (.branch (.branch (.leaf 2294543026014913) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3819151683174322) (.leaf 0))) (.branch (.branch (.leaf 2602695739458070) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3377260694754115) (.leaf 0))) (.branch (.branch (.leaf 2435877707543589) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2804013606220896) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2985923009183275) (.leaf 0))) (.branch (.branch (.leaf 2262439763381664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3693586296188137) (.leaf 0))) (.branch (.branch (.leaf 2558176113032445) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3287669554948958) (.leaf 0))) (.branch (.branch (.leaf 2398429669443210) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4284216401482795) (.leaf 0))) (.branch (.branch (.leaf 2749790528478761) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3126760791072618) (.leaf 0))) (.branch (.branch (.leaf 2327854432747091) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3957698455896460) (.leaf 0))) (.branch (.branch (.leaf 2649347324765992) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3474047703065367) (.leaf 0))) (.branch (.branch (.leaf 2474904422885821) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2861239682585718) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2983794928158979) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3682222251824363) (.leaf 0))) (.branch (.branch (.leaf 2556261631289844) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3283221340598619) (.leaf 0))) (.branch (.branch (.leaf 2395946255404253) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4253065859125486) (.leaf 0))) (.branch (.branch (.leaf 2748148288616600) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3123813103131489) (.leaf 0))) (.branch (.branch (.leaf 2325045907599663) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3939046558986713) (.leaf 0))) (.branch (.branch (.leaf 2647626389945855) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3467019045006625) (.leaf 0))) (.branch (.branch (.leaf 2472725806715566) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2859495144109210) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3051634967443785) (.leaf 0))) (.branch (.branch (.leaf 2291568851655301) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3804619428807289) (.leaf 0))) (.branch (.branch (.leaf 2600889213765731) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3371690934939661) (.leaf 0))) (.branch (.branch (.leaf 2433550321550239) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4438823559457897) (.leaf 0))) (.branch (.branch (.leaf 2802348119702568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3200818500334764) (.leaf 0))) (.branch (.branch (.leaf 2359809637072261) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4087630680201960) (.leaf 0))) (.branch (.branch (.leaf 2696647613675369) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3570150279660746) (.leaf 0))) (.branch (.branch (.leaf 2513587335205520) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2919870610800602) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 22) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 22 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 22 (0 : Fin 4)) (endpointMeanCornerA 45 22 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 22 (0 : Fin 4) = endpointMeanCornerK 45 21 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 22 (0 : Fin 4) = endpointMeanCornerA 45 21 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 22 (1 : Fin 4)) (endpointMeanCornerA 45 22 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 22 (2 : Fin 4)) (endpointMeanCornerA 45 22 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 22 (2 : Fin 4) = endpointMeanCornerK 45 21 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 22 (2 : Fin 4) = endpointMeanCornerA 45 21 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_21.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 22 (3 : Fin 4)) (endpointMeanCornerA 45 22 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 22 h) (endpointMeanCornerA 45 22 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 22) (prefactors h) runs ≤
      endpointMeanCorner 45 22 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 22 h ≤ endpointMeanCorner 45 22 h :=
  endpointMeanNumericCorner_le_of_runs 45 22 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨969,981,125⟩,⟨981,1022,126⟩,⟨1022,1068,127⟩,⟨1068,1118,128⟩,⟨1118,1173,129⟩,⟨1173,1235,130⟩,⟨1235,1303,131⟩,⟨1303,1380,132⟩,⟨1380,1468,133⟩,⟨1468,1567,134⟩,⟨1567,1607,135⟩,⟨1607,1655,134⟩,⟨1655,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2873749184337001) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3445289424125950) (.leaf 0))) (.branch (.branch (.leaf 2497350691377892) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3125595420779166) (.leaf 0))) (.branch (.branch (.leaf 2351445957154830) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3870213443047572) (.leaf 0))) (.branch (.branch (.leaf 2668644757425262) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2992765017866260) (.leaf 0))) (.branch (.branch (.leaf 2286144333784274) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3641219213938591) (.leaf 0))) (.branch (.branch (.leaf 2579376296883115) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3275153304684496) (.leaf 0))) (.branch (.branch (.leaf 2421632171868885) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2766298503193694) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2931683936821503) (.leaf 0))) (.branch (.branch (.leaf 2255151152091847) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3539634490804943) (.leaf 0))) (.branch (.branch (.leaf 2537520863549145) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3198068795078389) (.leaf 0))) (.branch (.branch (.leaf 2385890652747218) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4000216202543045) (.leaf 0))) (.branch (.branch (.leaf 2716342429610206) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3057289546600049) (.leaf 0))) (.branch (.branch (.leaf 2318220835203921) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3751021303241161) (.leaf 0))) (.branch (.branch (.leaf 2623039247068261) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3357361536437234) (.leaf 0))) (.branch (.branch (.leaf 2458754797722892) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2818698309822963) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2929970010793785) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3534352085411359) (.leaf 0))) (.branch (.branch (.leaf 2535118714021414) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3195624082288839) (.leaf 0))) (.branch (.branch (.leaf 2382838997504403) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3986919088492497) (.leaf 0))) (.branch (.branch (.leaf 2714466892636486) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3055373866534658) (.leaf 0))) (.branch (.branch (.leaf 2314836750250224) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3742712763695816) (.leaf 0))) (.branch (.branch (.leaf 2620926695494646) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3353885969985456) (.leaf 0))) (.branch (.branch (.leaf 2456034181328019) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2816972597203579) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2990982912049032) (.leaf 0))) (.branch (.branch (.leaf 2282596000084250) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3634613405507457) (.leaf 0))) (.branch (.branch (.leaf 2577123829586709) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3272270078478451) (.leaf 0))) (.branch (.branch (.leaf 2418746809898224) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4125868743291404) (.leaf 0))) (.branch (.branch (.leaf 2764511494724524) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3123465267092302) (.leaf 0))) (.branch (.branch (.leaf 2348227715702530) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3859719806130382) (.leaf 0))) (.branch (.branch (.leaf 2666659142412795) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3441030054562135) (.leaf 0))) (.branch (.branch (.leaf 2494791756077630) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2872050633763165) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2983794928158979) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3682222251824363) (.leaf 0))) (.branch (.branch (.leaf 2556261631289844) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3283221340598619) (.leaf 0))) (.branch (.branch (.leaf 2395946255404253) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4253065859125486) (.leaf 0))) (.branch (.branch (.leaf 2748148288616600) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3123813103131489) (.leaf 0))) (.branch (.branch (.leaf 2325045907599663) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3939046558986713) (.leaf 0))) (.branch (.branch (.leaf 2647626389945855) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3467019045006625) (.leaf 0))) (.branch (.branch (.leaf 2472725806715566) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2859495144109210) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3051634967443785) (.leaf 0))) (.branch (.branch (.leaf 2291568851655301) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3804619428807289) (.leaf 0))) (.branch (.branch (.leaf 2600889213765731) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3371690934939661) (.leaf 0))) (.branch (.branch (.leaf 2433550321550239) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4438823559457897) (.leaf 0))) (.branch (.branch (.leaf 2802348119702568) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3200818500334764) (.leaf 0))) (.branch (.branch (.leaf 2359809637072261) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4087630680201960) (.leaf 0))) (.branch (.branch (.leaf 2696647613675369) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3570150279660746) (.leaf 0))) (.branch (.branch (.leaf 2513587335205520) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2919870610800602) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3047143139242045) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3788348609603602) (.leaf 0))) (.branch (.branch (.leaf 2597552421543390) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3363969912339670) (.leaf 0))) (.branch (.branch (.leaf 2429913267213076) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4399322451100869) (.leaf 0))) (.branch (.branch (.leaf 2798905712347179) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3195111504252545) (.leaf 0))) (.branch (.branch (.leaf 2355954284210838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4062705302390276) (.leaf 0))) (.branch (.branch (.leaf 2693332683672553) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3559162926661126) (.leaf 0))) (.branch (.branch (.leaf 2510131315813489) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2916074465916841) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3118793065288319) (.leaf 0))) (.branch (.branch (.leaf 2321072979210594) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3918990335489539) (.leaf 0))) (.branch (.branch (.leaf 2644315482355188) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3457859608682836) (.leaf 0))) (.branch (.branch (.leaf 2469185251903631) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4599010121239233) (.leaf 0))) (.branch (.branch (.leaf 2855910260315375) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3276630275439371) (.leaf 0))) (.branch (.branch (.leaf 2392203500735020) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4221828611736325) (.leaf 0))) (.branch (.branch (.leaf 2744792381264452) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3668911341693767) (.leaf 0))) (.branch (.branch (.leaf 2552874863886034) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2979702971305220) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 23) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 23 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 23 (0 : Fin 4)) (endpointMeanCornerA 45 23 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 23 (0 : Fin 4) = endpointMeanCornerK 45 22 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 23 (0 : Fin 4) = endpointMeanCornerA 45 22 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 23 (1 : Fin 4)) (endpointMeanCornerA 45 23 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 23 (2 : Fin 4)) (endpointMeanCornerA 45 23 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 23 (2 : Fin 4) = endpointMeanCornerK 45 22 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 23 (2 : Fin 4) = endpointMeanCornerA 45 22 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_22.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 23 (3 : Fin 4)) (endpointMeanCornerA 45 23 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 23 h) (endpointMeanCornerA 45 23 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 23) (prefactors h) runs ≤
      endpointMeanCorner 45 23 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 23 h ≤ endpointMeanCorner 45 23 h :=
  endpointMeanNumericCorner_le_of_runs 45 23 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨979,1014,125⟩,⟨1014,1057,126⟩,⟨1057,1105,127⟩,⟨1105,1157,128⟩,⟨1157,1215,129⟩,⟨1215,1279,130⟩,⟨1279,1350,131⟩,⟨1350,1431,132⟩,⟨1431,1522,133⟩,⟨1522,1588,134⟩,⟨1588,1621,134⟩,⟨1621,1655,134⟩,⟨1655,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2929970010793785) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3534352085411359) (.leaf 0))) (.branch (.branch (.leaf 2535118714021414) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3195624082288839) (.leaf 0))) (.branch (.branch (.leaf 2382838997504403) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3986919088492497) (.leaf 0))) (.branch (.branch (.leaf 2714466892636486) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3055373866534658) (.leaf 0))) (.branch (.branch (.leaf 2314836750250224) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3742712763695816) (.leaf 0))) (.branch (.branch (.leaf 2620926695494646) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3353885969985456) (.leaf 0))) (.branch (.branch (.leaf 2456034181328019) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2816972597203579) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2990982912049032) (.leaf 0))) (.branch (.branch (.leaf 2282596000084250) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3634613405507457) (.leaf 0))) (.branch (.branch (.leaf 2577123829586709) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3272270078478451) (.leaf 0))) (.branch (.branch (.leaf 2418746809898224) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2764511494724524) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3123465267092302) (.leaf 0))) (.branch (.branch (.leaf 2348227715702530) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3859719806130382) (.leaf 0))) (.branch (.branch (.leaf 2666659142412795) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3441030054562135) (.leaf 0))) (.branch (.branch (.leaf 2494791756077630) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2872050633763165) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2987290717972487) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3625717066374089) (.leaf 0))) (.branch (.branch (.leaf 2573457911365921) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3267221729150949) (.leaf 0))) (.branch (.branch (.leaf 2414651151454862) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4107143973348670) (.leaf 0))) (.branch (.branch (.leaf 2761075819746284) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3119292496595237) (.leaf 0))) (.branch (.branch (.leaf 2343889272922282) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3847035294636836) (.leaf 0))) (.branch (.branch (.leaf 2663146417006774) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3434511319997244) (.leaf 0))) (.branch (.branch (.leaf 2490924910035504) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2868574958282529) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3051481323688810) (.leaf 0))) (.branch (.branch (.leaf 2310374847720368) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3732140886809576) (.leaf 0))) (.branch (.branch (.leaf 2617344877209927) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3348192972891599) (.leaf 0))) (.branch (.branch (.leaf 2452055429973918) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2813534744793094) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3191073375952069) (.leaf 0))) (.branch (.branch (.leaf 2378623003061944) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3971568215025240) (.leaf 0))) (.branch (.branch (.leaf 2711004415874326) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3526783668631947) (.leaf 0))) (.branch (.branch (.leaf 2531356893317330) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2926412810535045) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3047143139242045) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3788348609603602) (.leaf 0))) (.branch (.branch (.leaf 2597552421543390) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3363969912339670) (.leaf 0))) (.branch (.branch (.leaf 2429913267213076) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4399322451100869) (.leaf 0))) (.branch (.branch (.leaf 2798905712347179) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3195111504252545) (.leaf 0))) (.branch (.branch (.leaf 2355954284210838) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4062705302390276) (.leaf 0))) (.branch (.branch (.leaf 2693332683672553) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3559162926661126) (.leaf 0))) (.branch (.branch (.leaf 2510131315813489) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2916074465916841) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3118793065288319) (.leaf 0))) (.branch (.branch (.leaf 2321072979210594) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3918990335489539) (.leaf 0))) (.branch (.branch (.leaf 2644315482355188) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3457859608682836) (.leaf 0))) (.branch (.branch (.leaf 2469185251903631) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2855910260315375) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3276630275439371) (.leaf 0))) (.branch (.branch (.leaf 2392203500735020) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4221828611736325) (.leaf 0))) (.branch (.branch (.leaf 2744792381264452) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3668911341693767) (.leaf 0))) (.branch (.branch (.leaf 2552874863886034) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2979702971305220) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3111836280504307) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3897533664833792) (.leaf 0))) (.branch (.branch (.leaf 2639510173792883) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3446704439690107) (.leaf 0))) (.branch (.branch (.leaf 2464361824836467) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4550608589150731) (.leaf 0))) (.branch (.branch (.leaf 2850600609530132) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3268037231284143) (.leaf 0))) (.branch (.branch (.leaf 2387273546362647) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4190246072723745) (.leaf 0))) (.branch (.branch (.leaf 2739828010660951) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3653755740616298) (.leaf 0))) (.branch (.branch (.leaf 2548102666909375) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2973773292915028) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3187429128274231) (.leaf 0))) (.branch (.branch (.leaf 2350956974707520) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4036799353273333) (.leaf 0))) (.branch (.branch (.leaf 2688466826351025) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3546230453525890) (.leaf 0))) (.branch (.branch (.leaf 2505341991175473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2910496150578282) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3354237661649045) (.leaf 0))) (.branch (.branch (.leaf 2425042045352764) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4360432294728449) (.leaf 0))) (.branch (.branch (.leaf 2793796704486410) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3770404430843251) (.leaf 0))) (.branch (.branch (.leaf 2592776459119240) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3040761383180168) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 24) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 24 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 24 (0 : Fin 4)) (endpointMeanCornerA 45 24 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 24 (0 : Fin 4) = endpointMeanCornerK 45 23 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 24 (0 : Fin 4) = endpointMeanCornerA 45 23 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 24 (1 : Fin 4)) (endpointMeanCornerA 45 24 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 24 (2 : Fin 4)) (endpointMeanCornerA 45 24 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 24 (2 : Fin 4) = endpointMeanCornerK 45 23 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 24 (2 : Fin 4) = endpointMeanCornerA 45 23 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_23.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 24 (3 : Fin 4)) (endpointMeanCornerA 45 24 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 24 h) (endpointMeanCornerA 45 24 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 24) (prefactors h) runs ≤
      endpointMeanCorner 45 24 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 24 h ≤ endpointMeanCorner 45 24 h :=
  endpointMeanNumericCorner_le_of_runs 45 24 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨988,1006,124⟩,⟨1006,1047,125⟩,⟨1047,1092,126⟩,⟨1092,1142,127⟩,⟨1142,1196,128⟩,⟨1196,1256,129⟩,⟨1256,1323,130⟩,⟨1323,1397,131⟩,⟨1397,1481,132⟩,⟨1481,1576,133⟩,⟨1576,1655,134⟩,⟨1655,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 2987290717972487) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3625717066374089) (.leaf 0))) (.branch (.branch (.leaf 2573457911365921) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3267221729150949) (.leaf 0))) (.branch (.branch (.leaf 2414651151454862) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4107143973348670) (.leaf 0))) (.branch (.branch (.leaf 2761075819746284) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3119292496595237) (.leaf 0))) (.branch (.branch (.leaf 2343889272922282) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3847035294636836) (.leaf 0))) (.branch (.branch (.leaf 2663146417006774) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3434511319997244) (.leaf 0))) (.branch (.branch (.leaf 2490924910035504) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2868574958282529) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3051481323688810) (.leaf 0))) (.branch (.branch (.leaf 2310374847720368) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3732140886809576) (.leaf 0))) (.branch (.branch (.leaf 2617344877209927) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3348192972891599) (.leaf 0))) (.branch (.branch (.leaf 2452055429973918) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2813534744793094) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3191073375952069) (.leaf 0))) (.branch (.branch (.leaf 2378623003061944) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3971568215025240) (.leaf 0))) (.branch (.branch (.leaf 2711004415874326) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3526783668631947) (.leaf 0))) (.branch (.branch (.leaf 2531356893317330) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2926412810535045) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3045732823479282) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3719443883267302) (.leaf 0))) (.branch (.branch (.leaf 2612376921420926) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3340423514329760) (.leaf 0))) (.branch (.branch (.leaf 2446888014393226) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4230994219697730) (.leaf 0))) (.branch (.branch (.leaf 2808485048415192) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3184548308764223) (.leaf 0))) (.branch (.branch (.leaf 2373306421338906) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3954265660388881) (.leaf 0))) (.branch (.branch (.leaf 2706046243341227) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3517074853692877) (.leaf 0))) (.branch (.branch (.leaf 2526311300798100) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2921122590775045) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3113203432661056) (.leaf 0))) (.branch (.branch (.leaf 2338491759725285) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3832285320328594) (.leaf 0))) (.branch (.branch (.leaf 2658193652788367) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3425877422970336) (.leaf 0))) (.branch (.branch (.leaf 2485822743852041) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2863427327129548) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3260144877548023) (.leaf 0))) (.branch (.branch (.leaf 2409411724792092) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4086657809083962) (.leaf 0))) (.branch (.branch (.leaf 2756087130146014) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3614674341143394) (.leaf 0))) (.branch (.branch (.leaf 2568457950742796) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2981803954633835) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3111836280504307) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3897533664833792) (.leaf 0))) (.branch (.branch (.leaf 2639510173792883) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3446704439690107) (.leaf 0))) (.branch (.branch (.leaf 2464361824836467) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4550608589150731) (.leaf 0))) (.branch (.branch (.leaf 2850600609530132) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3268037231284143) (.leaf 0))) (.branch (.branch (.leaf 2387273546362647) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4190246072723745) (.leaf 0))) (.branch (.branch (.leaf 2739828010660951) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3653755740616298) (.leaf 0))) (.branch (.branch (.leaf 2548102666909375) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2973773292915028) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3187429128274231) (.leaf 0))) (.branch (.branch (.leaf 2350956974707520) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4036799353273333) (.leaf 0))) (.branch (.branch (.leaf 2688466826351025) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3546230453525890) (.leaf 0))) (.branch (.branch (.leaf 2505341991175473) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2910496150578282) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3354237661649045) (.leaf 0))) (.branch (.branch (.leaf 2425042045352764) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4360432294728449) (.leaf 0))) (.branch (.branch (.leaf 2793796704486410) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3770404430843251) (.leaf 0))) (.branch (.branch (.leaf 2592776459119240) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3040761383180168) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3177902905825290) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4009865573089965) (.leaf 0))) (.branch (.branch (.leaf 2682145661343974) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3531473765862854) (.leaf 0))) (.branch (.branch (.leaf 2499298755085478) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4707097231863623) (.leaf 0))) (.branch (.branch (.leaf 2903250295001582) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3342627426568570) (.leaf 0))) (.branch (.branch (.leaf 2419009156228969) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4321790738709620) (.leaf 0))) (.branch (.branch (.leaf 2787125992087427) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3750862572793262) (.leaf 0))) (.branch (.branch (.leaf 2586648419629177) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3032613776162355) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3257575682351918) (.leaf 0))) (.branch (.branch (.leaf 2381225728975438) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4158149835435207) (.leaf 0))) (.branch (.branch (.leaf 2733355352120231) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3636859749290050) (.leaf 0))) (.branch (.branch (.leaf 2542028180310894) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2966125357732905) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3433683188230994) (.leaf 0))) (.branch (.branch (.leaf 2458331375203572) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4503586371094100) (.leaf 0))) (.branch (.branch (.leaf 2843675929471730) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3874705123171384) (.leaf 0))) (.branch (.branch (.leaf 2633301718804110) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3103070969986512) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 25) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 25 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 25 (0 : Fin 4)) (endpointMeanCornerA 45 25 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 25 (0 : Fin 4) = endpointMeanCornerK 45 24 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 25 (0 : Fin 4) = endpointMeanCornerA 45 24 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 25 (1 : Fin 4)) (endpointMeanCornerA 45 25 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 25 (2 : Fin 4)) (endpointMeanCornerA 45 25 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 25 (2 : Fin 4) = endpointMeanCornerK 45 24 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 25 (2 : Fin 4) = endpointMeanCornerA 45 24 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_24.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 25 (3 : Fin 4)) (endpointMeanCornerA 45 25 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 25 h) (endpointMeanCornerA 45 25 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 25) (prefactors h) runs ≤
      endpointMeanCorner 45 25 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 25 h ≤ endpointMeanCorner 45 25 h :=
  endpointMeanNumericCorner_le_of_runs 45 25 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨998,1037,124⟩,⟨1037,1080,125⟩,⟨1080,1127,126⟩,⟨1127,1179,127⟩,⟨1179,1235,128⟩,⟨1235,1298,129⟩,⟨1298,1367,130⟩,⟨1367,1444,131⟩,⟨1444,1531,132⟩,⟨1531,1629,133⟩,⟨1629,1655,134⟩,⟨1655,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3045732823479282) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3719443883267302) (.leaf 0))) (.branch (.branch (.leaf 2612376921420926) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3340423514329760) (.leaf 0))) (.branch (.branch (.leaf 2446888014393226) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4230994219697730) (.leaf 0))) (.branch (.branch (.leaf 2808485048415192) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3184548308764223) (.leaf 0))) (.branch (.branch (.leaf 2373306421338906) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3954265660388881) (.leaf 0))) (.branch (.branch (.leaf 2706046243341227) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3517074853692877) (.leaf 0))) (.branch (.branch (.leaf 2526311300798100) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2921122590775045) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3113203432661056) (.leaf 0))) (.branch (.branch (.leaf 2338491759725285) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3832285320328594) (.leaf 0))) (.branch (.branch (.leaf 2658193652788367) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3425877422970336) (.leaf 0))) (.branch (.branch (.leaf 2485822743852041) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2863427327129548) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3260144877548023) (.leaf 0))) (.branch (.branch (.leaf 2409411724792092) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4086657809083962) (.leaf 0))) (.branch (.branch (.leaf 2756087130146014) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3614674341143394) (.leaf 0))) (.branch (.branch (.leaf 2568457950742796) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2981803954633835) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3105318265881783) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3815593590872652) (.leaf 0))) (.branch (.branch (.leaf 2651884512830608) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3415265378388295) (.leaf 0))) (.branch (.branch (.leaf 2479555256407867) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4358579149715118) (.leaf 0))) (.branch (.branch (.leaf 2856708320272234) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3251169276982694) (.leaf 0))) (.branch (.branch (.leaf 2403092771761346) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4064484912506320) (.leaf 0))) (.branch (.branch (.leaf 2749637130102468) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3601623163812634) (.leaf 0))) (.branch (.branch (.leaf 2562200395052947) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2974632810517577) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3176173990610009) (.leaf 0))) (.branch (.branch (.leaf 2366950850291173) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3935116926671211) (.leaf 0))) (.branch (.branch (.leaf 2699679953242033) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3505364300159126) (.leaf 0))) (.branch (.branch (.leaf 2520055068215900) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2914204657655732) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3330711447345380) (.leaf 0))) (.branch (.branch (.leaf 2440598973478614) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4205082512586489) (.leaf 0))) (.branch (.branch (.leaf 2801919548517852) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3704755329546126) (.leaf 0))) (.branch (.branch (.leaf 2606102783115887) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3038243542353958) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3177902905825290) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4009865573089965) (.leaf 0))) (.branch (.branch (.leaf 2682145661343974) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3531473765862854) (.leaf 0))) (.branch (.branch (.leaf 2499298755085478) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4707097231863623) (.leaf 0))) (.branch (.branch (.leaf 2903250295001582) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3342627426568570) (.leaf 0))) (.branch (.branch (.leaf 2419009156228969) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4321790738709620) (.leaf 0))) (.branch (.branch (.leaf 2787125992087427) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3750862572793262) (.leaf 0))) (.branch (.branch (.leaf 2586648419629177) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3032613776162355) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3257575682351918) (.leaf 0))) (.branch (.branch (.leaf 2381225728975438) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4158149835435207) (.leaf 0))) (.branch (.branch (.leaf 2733355352120231) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3636859749290050) (.leaf 0))) (.branch (.branch (.leaf 2542028180310894) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2966125357732905) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3433683188230994) (.leaf 0))) (.branch (.branch (.leaf 2458331375203572) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4503586371094100) (.leaf 0))) (.branch (.branch (.leaf 2843675929471730) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3874705123171384) (.leaf 0))) (.branch (.branch (.leaf 2633301718804110) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3103070969986512) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3245372175304854) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4125435030703658) (.leaf 0))) (.branch (.branch (.leaf 2725469831521398) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3618327935336064) (.leaf 0))) (.branch (.branch (.leaf 2534730981553949) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4868967285616023) (.leaf 0))) (.branch (.branch (.leaf 2956872403397161) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3418920080190776) (.leaf 0))) (.branch (.branch (.leaf 2451166648595989) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4457464994903093) (.leaf 0))) (.branch (.branch (.leaf 2835240484272359) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3850550238918876) (.leaf 0))) (.branch (.branch (.leaf 2625777263082343) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3092618505008711) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3329265969278549) (.leaf 0))) (.branch (.branch (.leaf 2411884195813512) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4283148242161125) (.leaf 0))) (.branch (.branch (.leaf 2778993368166191) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3729805214112696) (.leaf 0))) (.branch (.branch (.leaf 2579251572142802) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3022817823015535) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3515010391763283) (.leaf 0))) (.branch (.branch (.leaf 2492077678360898) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4651440231379079) (.leaf 0))) (.branch (.branch (.leaf 2894445676334014) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3981891085400833) (.leaf 0))) (.branch (.branch (.leaf 2674460390855388) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3166657370103313) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 26) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 26 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 26 (0 : Fin 4)) (endpointMeanCornerA 45 26 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 26 (0 : Fin 4) = endpointMeanCornerK 45 25 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 26 (0 : Fin 4) = endpointMeanCornerA 45 25 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 26 (1 : Fin 4)) (endpointMeanCornerA 45 26 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 26 (2 : Fin 4)) (endpointMeanCornerA 45 26 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 26 (2 : Fin 4) = endpointMeanCornerK 45 25 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 26 (2 : Fin 4) = endpointMeanCornerA 45 25 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_25.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 26 (3 : Fin 4)) (endpointMeanCornerA 45 26 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 26 h) (endpointMeanCornerA 45 26 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 26) (prefactors h) runs ≤
      endpointMeanCorner 45 26 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 26 h ≤ endpointMeanCorner 45 26 h :=
  endpointMeanNumericCorner_le_of_runs 45 26 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1007,1028,123⟩,⟨1028,1069,124⟩,⟨1069,1114,125⟩,⟨1114,1162,126⟩,⟨1162,1216,127⟩,⟨1216,1274,128⟩,⟨1274,1339,129⟩,⟨1339,1411,130⟩,⟨1411,1491,131⟩,⟨1491,1581,132⟩,⟨1581,1643,133⟩,⟨1643,1674,133⟩,⟨1674,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3105318265881783) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3815593590872652) (.leaf 0))) (.branch (.branch (.leaf 2651884512830608) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3415265378388295) (.leaf 0))) (.branch (.branch (.leaf 2479555256407867) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2856708320272234) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3251169276982694) (.leaf 0))) (.branch (.branch (.leaf 2403092771761346) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4064484912506320) (.leaf 0))) (.branch (.branch (.leaf 2749637130102468) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3601623163812634) (.leaf 0))) (.branch (.branch (.leaf 2562200395052947) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2974632810517577) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3176173990610009) (.leaf 0))) (.branch (.branch (.leaf 2366950850291173) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3935116926671211) (.leaf 0))) (.branch (.branch (.leaf 2699679953242033) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3505364300159126) (.leaf 0))) (.branch (.branch (.leaf 2520055068215900) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2914204657655732) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3330711447345380) (.leaf 0))) (.branch (.branch (.leaf 2440598973478614) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4205082512586489) (.leaf 0))) (.branch (.branch (.leaf 2801919548517852) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3704755329546126) (.leaf 0))) (.branch (.branch (.leaf 2606102783115887) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3038243542353958) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3166069412944568) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3914228822272079) (.leaf 0))) (.branch (.branch (.leaf 2691989586849398) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3491784067134406) (.leaf 0))) (.branch (.branch (.leaf 2512658623285833) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2905759612897947) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3319183960408481) (.leaf 0))) (.branch (.branch (.leaf 2433252957885535) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4177776361734597) (.leaf 0))) (.branch (.branch (.leaf 2793930209375496) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3688203963157523) (.leaf 0))) (.branch (.branch (.leaf 2598599334268715) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3029123250544575) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3240418249829745) (.leaf 0))) (.branch (.branch (.leaf 2395756283679291) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4040707810671699) (.leaf 0))) (.branch (.branch (.leaf 2741813728390979) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3586695424197744) (.leaf 0))) (.branch (.branch (.leaf 2554758806735999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2965882425664976) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3402805446431921) (.leaf 0))) (.branch (.branch (.leaf 2472189907625211) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4326938971585755) (.leaf 0))) (.branch (.branch (.leaf 2848514138212518) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3797081218514107) (.leaf 0))) (.branch (.branch (.leaf 2644299360322481) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3095751418637134) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3245372175304854) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4125435030703658) (.leaf 0))) (.branch (.branch (.leaf 2725469831521398) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3618327935336064) (.leaf 0))) (.branch (.branch (.leaf 2534730981553949) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2956872403397161) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3418920080190776) (.leaf 0))) (.branch (.branch (.leaf 2451166648595989) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4457464994903093) (.leaf 0))) (.branch (.branch (.leaf 2835240484272359) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3850550238918876) (.leaf 0))) (.branch (.branch (.leaf 2625777263082343) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3092618505008711) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3329265969278549) (.leaf 0))) (.branch (.branch (.leaf 2411884195813512) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4283148242161125) (.leaf 0))) (.branch (.branch (.leaf 2778993368166191) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3729805214112696) (.leaf 0))) (.branch (.branch (.leaf 2579251572142802) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3022817823015535) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3515010391763283) (.leaf 0))) (.branch (.branch (.leaf 2492077678360898) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4651440231379079) (.leaf 0))) (.branch (.branch (.leaf 2894445676334014) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3981891085400833) (.leaf 0))) (.branch (.branch (.leaf 2674460390855388) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3166657370103313) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3314273868133717) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4244335347990736) (.leaf 0))) (.branch (.branch (.leaf 2769493808479866) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3707318223397441) (.leaf 0))) (.branch (.branch (.leaf 2570665525990592) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3011484895058604) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3496954049327381) (.leaf 0))) (.branch (.branch (.leaf 2483751631827470) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4597398481796651) (.leaf 0))) (.branch (.branch (.leaf 2884185582739456) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3952887330499221) (.leaf 0))) (.branch (.branch (.leaf 2665498017820537) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3153810515767525) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3402533962370980) (.leaf 0))) (.branch (.branch (.leaf 2442937392801447) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4411904233943469) (.leaf 0))) (.branch (.branch (.leaf 2825393388503691) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3825126041205705) (.leaf 0))) (.branch (.branch (.leaf 2617020033030278) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3080593868805466) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3598263839993118) (.leaf 0))) (.branch (.branch (.leaf 2526287227843873) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4804148170657965) (.leaf 0))) (.branch (.branch (.leaf 2946121844061548) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4092042132748729) (.leaf 0))) (.branch (.branch (.leaf 2716262375548329) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3231546747277010) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 27) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 27 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 27 (0 : Fin 4)) (endpointMeanCornerA 45 27 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 27 (0 : Fin 4) = endpointMeanCornerK 45 26 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 27 (0 : Fin 4) = endpointMeanCornerA 45 26 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 27 (1 : Fin 4)) (endpointMeanCornerA 45 27 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 27 (2 : Fin 4)) (endpointMeanCornerA 45 27 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 27 (2 : Fin 4) = endpointMeanCornerK 45 26 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 27 (2 : Fin 4) = endpointMeanCornerA 45 26 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_26.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 27 (3 : Fin 4)) (endpointMeanCornerA 45 27 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 27 h) (endpointMeanCornerA 45 27 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 27) (prefactors h) runs ≤
      endpointMeanCorner 45 27 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 27 h ≤ endpointMeanCorner 45 27 h :=
  endpointMeanNumericCorner_le_of_runs 45 27 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1016,1018,122⟩,⟨1018,1058,123⟩,⟨1058,1100,124⟩,⟨1100,1147,125⟩,⟨1147,1197,126⟩,⟨1197,1253,127⟩,⟨1253,1313,128⟩,⟨1313,1380,129⟩,⟨1380,1455,130⟩,⟨1455,1538,131⟩,⟨1538,1632,132⟩,⟨1632,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3166069412944568) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3914228822272079) (.leaf 0))) (.branch (.branch (.leaf 2691989586849398) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3491784067134406) (.leaf 0))) (.branch (.branch (.leaf 2512658623285833) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2905759612897947) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3319183960408481) (.leaf 0))) (.branch (.branch (.leaf 2433252957885535) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4177776361734597) (.leaf 0))) (.branch (.branch (.leaf 2793930209375496) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3688203963157523) (.leaf 0))) (.branch (.branch (.leaf 2598599334268715) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3029123250544575) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3240418249829745) (.leaf 0))) (.branch (.branch (.leaf 2395756283679291) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4040707810671699) (.leaf 0))) (.branch (.branch (.leaf 2741813728390979) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3586695424197744) (.leaf 0))) (.branch (.branch (.leaf 2554758806735999) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2965882425664976) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3402805446431921) (.leaf 0))) (.branch (.branch (.leaf 2472189907625211) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4326938971585755) (.leaf 0))) (.branch (.branch (.leaf 2848514138212518) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3797081218514107) (.leaf 0))) (.branch (.branch (.leaf 2644299360322481) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3095751418637134) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3228009070025791) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4015413829647778) (.leaf 0))) (.branch (.branch (.leaf 2732701179347512) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3570017149662174) (.leaf 0))) (.branch (.branch (.leaf 2546203937523443) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2955653143875816) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3388621515658961) (.leaf 0))) (.branch (.branch (.leaf 2463791671562939) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4294225640981806) (.leaf 0))) (.branch (.branch (.leaf 2838936792568734) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3776866111514857) (.leaf 0))) (.branch (.branch (.leaf 2635515361366673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3084611866899036) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3305961973390825) (.leaf 0))) (.branch (.branch (.leaf 2424912274829346) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4149132011951394) (.leaf 0))) (.branch (.branch (.leaf 2784605083341622) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3669913585123546) (.leaf 0))) (.branch (.branch (.leaf 2589940451267939) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3018476598669796) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3476459936358467) (.leaf 0))) (.branch (.branch (.leaf 2504189752506876) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4452326632780315) (.leaf 0))) (.branch (.branch (.leaf 2895883573776669) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3891707953021257) (.leaf 0))) (.branch (.branch (.leaf 2683055769059804) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3154347804050170) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3314273868133717) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4244335347990736) (.leaf 0))) (.branch (.branch (.leaf 2769493808479866) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3707318223397441) (.leaf 0))) (.branch (.branch (.leaf 2570665525990592) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3011484895058604) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3496954049327381) (.leaf 0))) (.branch (.branch (.leaf 2483751631827470) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4597398481796651) (.leaf 0))) (.branch (.branch (.leaf 2884185582739456) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3952887330499221) (.leaf 0))) (.branch (.branch (.leaf 2665498017820537) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3153810515767525) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3402533962370980) (.leaf 0))) (.branch (.branch (.leaf 2442937392801447) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4411904233943469) (.leaf 0))) (.branch (.branch (.leaf 2825393388503691) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3825126041205705) (.leaf 0))) (.branch (.branch (.leaf 2617020033030278) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3080593868805466) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3598263839993118) (.leaf 0))) (.branch (.branch (.leaf 2526287227843873) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4804148170657965) (.leaf 0))) (.branch (.branch (.leaf 2946121844061548) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4092042132748729) (.leaf 0))) (.branch (.branch (.leaf 2716262375548329) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3231546747277010) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3384638395737216) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4366662524589806) (.leaf 0))) (.branch (.branch (.leaf 2814228896060372) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3798497166415139) (.leaf 0))) (.branch (.branch (.leaf 2607109509690520) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3067106062049442) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3576769078037291) (.leaf 0))) (.branch (.branch (.leaf 2516769788842876) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4741724909695149) (.leaf 0))) (.branch (.branch (.leaf 2933975626345148) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4057944262014986) (.leaf 0))) (.branch (.branch (.leaf 2705819637826000) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3216213300559621) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3477414382605407) (.leaf 0))) (.branch (.branch (.leaf 2474390402120693) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4544530767785661) (.leaf 0))) (.branch (.branch (.leaf 2872568136090270) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3922882936553252) (.leaf 0))) (.branch (.branch (.leaf 2655341544520968) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3139474205909841) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3683489156260211) (.leaf 0))) (.branch (.branch (.leaf 2560966382783367) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4961869549550992) (.leaf 0))) (.branch (.branch (.leaf 2998720615496184) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4205240288360416) (.leaf 0))) (.branch (.branch (.leaf 2758717727900117) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3297765801386947) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 28) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 28 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 28 (0 : Fin 4)) (endpointMeanCornerA 45 28 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 28 (0 : Fin 4) = endpointMeanCornerK 45 27 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 28 (0 : Fin 4) = endpointMeanCornerA 45 27 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 28 (1 : Fin 4)) (endpointMeanCornerA 45 28 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 28 (2 : Fin 4)) (endpointMeanCornerA 45 28 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 28 (2 : Fin 4) = endpointMeanCornerK 45 27 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 28 (2 : Fin 4) = endpointMeanCornerA 45 27 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_27.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 28 (3 : Fin 4)) (endpointMeanCornerA 45 28 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 28 h) (endpointMeanCornerA 45 28 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 28) (prefactors h) runs ≤
      endpointMeanCorner 45 28 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 28 h ≤ endpointMeanCorner 45 28 h :=
  endpointMeanNumericCorner_le_of_runs 45 28 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1024,1041,122⟩,⟨1041,1082,123⟩,⟨1082,1126,124⟩,⟨1126,1173,125⟩,⟨1173,1225,126⟩,⟨1225,1282,127⟩,⟨1282,1345,128⟩,⟨1345,1414,129⟩,⟨1414,1490,130⟩,⟨1490,1576,131⟩,⟨1576,1672,132⟩,⟨1672,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3228009070025791) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4015413829647778) (.leaf 0))) (.branch (.branch (.leaf 2732701179347512) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3570017149662174) (.leaf 0))) (.branch (.branch (.leaf 2546203937523443) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2955653143875816) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3388621515658961) (.leaf 0))) (.branch (.branch (.leaf 2463791671562939) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4294225640981806) (.leaf 0))) (.branch (.branch (.leaf 2838936792568734) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3776866111514857) (.leaf 0))) (.branch (.branch (.leaf 2635515361366673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3084611866899036) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3305961973390825) (.leaf 0))) (.branch (.branch (.leaf 2424912274829346) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4149132011951394) (.leaf 0))) (.branch (.branch (.leaf 2784605083341622) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3669913585123546) (.leaf 0))) (.branch (.branch (.leaf 2589940451267939) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3018476598669796) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3476459936358467) (.leaf 0))) (.branch (.branch (.leaf 2504189752506876) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4452326632780315) (.leaf 0))) (.branch (.branch (.leaf 2895883573776669) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3891707953021257) (.leaf 0))) (.branch (.branch (.leaf 2683055769059804) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3154347804050170) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3265753002892363) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4077376076032760) (.leaf 0))) (.branch (.branch (.leaf 2757423073739130) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3617795851519662) (.leaf 0))) (.branch (.branch (.leaf 2566545712029501) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2985999542661245) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3430979384426006) (.leaf 0))) (.branch (.branch (.leaf 2482298566829761) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4365647481900523) (.leaf 0))) (.branch (.branch (.leaf 2866287998044905) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3831083212640687) (.leaf 0))) (.branch (.branch (.leaf 2657916231343970) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3118391754032785) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3345922862637243) (.leaf 0))) (.branch (.branch (.leaf 2442575909846282) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4215578067730532) (.leaf 0))) (.branch (.branch (.leaf 2810599797314228) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3720768431062343) (.leaf 0))) (.branch (.branch (.leaf 2611281566919131) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3050479725218431) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3521415686991007) (.leaf 0))) (.branch (.branch (.leaf 2523588135599727) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4529296652840170) (.leaf 0))) (.branch (.branch (.leaf 2924682512552271) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3949612193647272) (.leaf 0))) (.branch (.branch (.leaf 2706581741826294) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3190036674516039) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3384638395737216) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4366662524589806) (.leaf 0))) (.branch (.branch (.leaf 2814228896060372) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3798497166415139) (.leaf 0))) (.branch (.branch (.leaf 2607109509690520) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3067106062049442) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3576769078037291) (.leaf 0))) (.branch (.branch (.leaf 2516769788842876) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4741724909695149) (.leaf 0))) (.branch (.branch (.leaf 2933975626345148) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4057944262014986) (.leaf 0))) (.branch (.branch (.leaf 2705819637826000) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3216213300559621) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3477414382605407) (.leaf 0))) (.branch (.branch (.leaf 2474390402120693) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4544530767785661) (.leaf 0))) (.branch (.branch (.leaf 2872568136090270) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3922882936553252) (.leaf 0))) (.branch (.branch (.leaf 2655341544520968) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3139474205909841) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3683489156260211) (.leaf 0))) (.branch (.branch (.leaf 2560966382783367) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4961869549550992) (.leaf 0))) (.branch (.branch (.leaf 2998720615496184) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4205240288360416) (.leaf 0))) (.branch (.branch (.leaf 2758717727900117) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3297765801386947) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3427572165469667) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4441744692398144) (.leaf 0))) (.branch (.branch (.leaf 2841416052378319) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3854277424548217) (.leaf 0))) (.branch (.branch (.leaf 2629223430971441) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3100970662204896) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3625529876397546) (.leaf 0))) (.branch (.branch (.leaf 2536790998817636) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4830486569257668) (.leaf 0))) (.branch (.branch (.leaf 2964261283688402) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4122313935698068) (.leaf 0))) (.branch (.branch (.leaf 2730304800665133) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3254246089449834) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3523131329283212) (.leaf 0))) (.branch (.branch (.leaf 2493456256291886) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4626012806672499) (.leaf 0))) (.branch (.branch (.leaf 2901250225900603) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3982732219889508) (.leaf 0))) (.branch (.branch (.leaf 2678603279735766) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3175341231680561) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3735590225799809) (.leaf 0))) (.branch (.branch (.leaf 2582001964411668) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5058977075618131) (.leaf 0))) (.branch (.branch (.leaf 3030729568216896) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4274656762970416) (.leaf 0))) (.branch (.branch (.leaf 2784508797442197) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3338146790439269) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 29) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 29 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 29 (0 : Fin 4)) (endpointMeanCornerA 45 29 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 29 (0 : Fin 4) = endpointMeanCornerK 45 28 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 29 (0 : Fin 4) = endpointMeanCornerA 45 28 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 29 (1 : Fin 4)) (endpointMeanCornerA 45 29 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 29 (2 : Fin 4)) (endpointMeanCornerA 45 29 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 29 (2 : Fin 4) = endpointMeanCornerK 45 28 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 29 (2 : Fin 4) = endpointMeanCornerA 45 28 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_28.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 29 (3 : Fin 4)) (endpointMeanCornerA 45 29 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 29 h) (endpointMeanCornerA 45 29 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 29) (prefactors h) runs ≤
      endpointMeanCorner 45 29 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 29 h ≤ endpointMeanCorner 45 29 h :=
  endpointMeanNumericCorner_le_of_runs 45 29 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1029,1056,122⟩,⟨1056,1097,123⟩,⟨1097,1141,124⟩,⟨1141,1190,125⟩,⟨1190,1243,126⟩,⟨1243,1301,127⟩,⟨1301,1364,128⟩,⟨1364,1434,129⟩,⟨1434,1512,130⟩,⟨1512,1599,131⟩,⟨1599,1697,132⟩,⟨1697,1705,133⟩,⟨1705,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3265753002892363) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4077376076032760) (.leaf 0))) (.branch (.branch (.leaf 2757423073739130) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3617795851519662) (.leaf 0))) (.branch (.branch (.leaf 2566545712029501) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2985999542661245) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3430979384426006) (.leaf 0))) (.branch (.branch (.leaf 2482298566829761) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4365647481900523) (.leaf 0))) (.branch (.branch (.leaf 2866287998044905) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3831083212640687) (.leaf 0))) (.branch (.branch (.leaf 2657916231343970) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3118391754032785) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3345922862637243) (.leaf 0))) (.branch (.branch (.leaf 2442575909846282) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4215578067730532) (.leaf 0))) (.branch (.branch (.leaf 2810599797314228) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3720768431062343) (.leaf 0))) (.branch (.branch (.leaf 2611281566919131) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3050479725218431) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3521415686991007) (.leaf 0))) (.branch (.branch (.leaf 2523588135599727) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4529296652840170) (.leaf 0))) (.branch (.branch (.leaf 2924682512552271) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3949612193647272) (.leaf 0))) (.branch (.branch (.leaf 2706581741826294) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3190036674516039) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3291160488638095) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4119214526136832) (.leaf 0))) (.branch (.branch (.leaf 2774028462846739) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3650003036797592) (.leaf 0))) (.branch (.branch (.leaf 2580197099350402) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3006403374913243) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3459511709309917) (.leaf 0))) (.branch (.branch (.leaf 2494713663530440) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4413920770045543) (.leaf 0))) (.branch (.branch (.leaf 2884668373302695) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3867659643231097) (.leaf 0))) (.branch (.branch (.leaf 2672955822161946) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3141116944549471) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3372831445471707) (.leaf 0))) (.branch (.branch (.leaf 2454423089976198) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4260465556834720) (.leaf 0))) (.branch (.branch (.leaf 2828064280910292) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3755062565784177) (.leaf 0))) (.branch (.branch (.leaf 2625606583066822) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3072003427335588) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3551708694300552) (.leaf 0))) (.branch (.branch (.leaf 2536603801034184) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4581347824672470) (.leaf 0))) (.branch (.branch (.leaf 2944040740528664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3988692872241401) (.leaf 0))) (.branch (.branch (.leaf 2722380214548470) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3214053301894788) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3427572165469667) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4441744692398144) (.leaf 0))) (.branch (.branch (.leaf 2841416052378319) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3854277424548217) (.leaf 0))) (.branch (.branch (.leaf 2629223430971441) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3100970662204896) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3625529876397546) (.leaf 0))) (.branch (.branch (.leaf 2536790998817636) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4830486569257668) (.leaf 0))) (.branch (.branch (.leaf 2964261283688402) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4122313935698068) (.leaf 0))) (.branch (.branch (.leaf 2730304800665133) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3254246089449834) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3523131329283212) (.leaf 0))) (.branch (.branch (.leaf 2493456256291886) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4626012806672499) (.leaf 0))) (.branch (.branch (.leaf 2901250225900603) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3982732219889508) (.leaf 0))) (.branch (.branch (.leaf 2678603279735766) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3175341231680561) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3735590225799809) (.leaf 0))) (.branch (.branch (.leaf 2582001964411668) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5058977075618131) (.leaf 0))) (.branch (.branch (.leaf 3030729568216896) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4274656762970416) (.leaf 0))) (.branch (.branch (.leaf 2784508797442197) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3338146790439269) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3456496815198136) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4492515326971900) (.leaf 0))) (.branch (.branch (.leaf 2859686580692628) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3891918592853153) (.leaf 0))) (.branch (.branch (.leaf 2644070154906502) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3123754534281790) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3658405817504082) (.leaf 0))) (.branch (.branch (.leaf 2550226878108477) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4890582186479686) (.leaf 0))) (.branch (.branch (.leaf 2984625201479291) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4165793319371100) (.leaf 0))) (.branch (.branch (.leaf 2746751212529986) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3279850816332020) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3553942715071277) (.leaf 0))) (.branch (.branch (.leaf 2506248371386169) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4681144196298793) (.leaf 0))) (.branch (.branch (.leaf 2920530546314870) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4023138157572965) (.leaf 0))) (.branch (.branch (.leaf 2694224205037799) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3199479940987846) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3770733044498623) (.leaf 0))) (.branch (.branch (.leaf 2596121589604080) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5124768960527181) (.leaf 0))) (.branch (.branch (.leaf 3052258462401174) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4321569844387387) (.leaf 0))) (.branch (.branch (.leaf 2801836660088509) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3365341779431496) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 30) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 30 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 30 (0 : Fin 4)) (endpointMeanCornerA 45 30 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 30 (0 : Fin 4) = endpointMeanCornerK 45 29 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 30 (0 : Fin 4) = endpointMeanCornerA 45 29 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 30 (1 : Fin 4)) (endpointMeanCornerA 45 30 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 30 (2 : Fin 4)) (endpointMeanCornerA 45 30 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 30 (2 : Fin 4) = endpointMeanCornerK 45 29 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 30 (2 : Fin 4) = endpointMeanCornerA 45 29 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_29.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 30 (3 : Fin 4)) (endpointMeanCornerA 45 30 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 30 h) (endpointMeanCornerA 45 30 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 30) (prefactors h) runs ≤
      endpointMeanCorner 45 30 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 30 h ≤ endpointMeanCorner 45 30 h :=
  endpointMeanNumericCorner_le_of_runs 45 30 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1035,1037,121⟩,⟨1037,1076,122⟩,⟨1076,1118,123⟩,⟨1118,1164,124⟩,⟨1164,1213,125⟩,⟨1213,1267,126⟩,⟨1267,1326,127⟩,⟨1326,1391,128⟩,⟨1391,1463,129⟩,⟨1463,1543,130⟩,⟨1543,1632,131⟩,⟨1632,1695,132⟩,⟨1695,1726,132⟩,⟨1726,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3291160488638095) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4119214526136832) (.leaf 0))) (.branch (.branch (.leaf 2774028462846739) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3650003036797592) (.leaf 0))) (.branch (.branch (.leaf 2580197099350402) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3006403374913243) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3459511709309917) (.leaf 0))) (.branch (.branch (.leaf 2494713663530440) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4413920770045543) (.leaf 0))) (.branch (.branch (.leaf 2884668373302695) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3867659643231097) (.leaf 0))) (.branch (.branch (.leaf 2672955822161946) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3141116944549471) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3372831445471707) (.leaf 0))) (.branch (.branch (.leaf 2454423089976198) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4260465556834720) (.leaf 0))) (.branch (.branch (.leaf 2828064280910292) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3755062565784177) (.leaf 0))) (.branch (.branch (.leaf 2625606583066822) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3072003427335588) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3551708694300552) (.leaf 0))) (.branch (.branch (.leaf 2536603801034184) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2944040740528664) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3988692872241401) (.leaf 0))) (.branch (.branch (.leaf 2722380214548470) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3214053301894788) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3355547375176990) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4225698528767851) (.leaf 0))) (.branch (.branch (.leaf 2815980748587102) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3731780999957472) (.leaf 0))) (.branch (.branch (.leaf 2614644087767589) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3058025016033309) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3531884930655958) (.leaf 0))) (.branch (.branch (.leaf 2526023744149376) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4536952222143831) (.leaf 0))) (.branch (.branch (.leaf 2931136630345157) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3960635795447541) (.leaf 0))) (.branch (.branch (.leaf 2710928166825213) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3198657103415327) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3441053481899172) (.leaf 0))) (.branch (.branch (.leaf 2484293047274159) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4374786511658393) (.leaf 0))) (.branch (.branch (.leaf 2872201744084598) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3842187164872699) (.leaf 0))) (.branch (.branch (.leaf 2661763874018365) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3126479450501765) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3628586228548274) (.leaf 0))) (.branch (.branch (.leaf 2569437414628749) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2992998738063555) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4088094744292971) (.leaf 0))) (.branch (.branch (.leaf 2762281022269636) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3274888905452000) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3456496815198136) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4492515326971900) (.leaf 0))) (.branch (.branch (.leaf 2859686580692628) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3891918592853153) (.leaf 0))) (.branch (.branch (.leaf 2644070154906502) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3123754534281790) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3658405817504082) (.leaf 0))) (.branch (.branch (.leaf 2550226878108477) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4890582186479686) (.leaf 0))) (.branch (.branch (.leaf 2984625201479291) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4165793319371100) (.leaf 0))) (.branch (.branch (.leaf 2746751212529986) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3279850816332020) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3553942715071277) (.leaf 0))) (.branch (.branch (.leaf 2506248371386169) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4681144196298793) (.leaf 0))) (.branch (.branch (.leaf 2920530546314870) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4023138157572965) (.leaf 0))) (.branch (.branch (.leaf 2694224205037799) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3199479940987846) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3770733044498623) (.leaf 0))) (.branch (.branch (.leaf 2596121589604080) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3052258462401174) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4321569844387387) (.leaf 0))) (.branch (.branch (.leaf 2801836660088509) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3365341779431496) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3529880842964482) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4621995368184166) (.leaf 0))) (.branch (.branch (.leaf 2905878534344369) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3987637655049559) (.leaf 0))) (.branch (.branch (.leaf 2681554786280220) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3181449285756310) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3741905846740312) (.leaf 0))) (.branch (.branch (.leaf 2584128734641667) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5044112549382402) (.leaf 0))) (.branch (.branch (.leaf 3036149146338334) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4276508709634126) (.leaf 0))) (.branch (.branch (.leaf 2788301968861717) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3344747494055201) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3632155225787315) (.leaf 0))) (.branch (.branch (.leaf 2538516514488744) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4821864369777195) (.leaf 0))) (.branch (.branch (.leaf 2969293770544776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4125955552765155) (.leaf 0))) (.branch (.branch (.leaf 2733676231590424) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3260632584116711) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3860043314830774) (.leaf 0))) (.branch (.branch (.leaf 2631759383222857) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3106752150619425) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4441117424754831) (.leaf 0))) (.branch (.branch (.leaf 2845629543908214) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3434302486739346) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 31) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 31 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 31 (0 : Fin 4)) (endpointMeanCornerA 45 31 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 31 (0 : Fin 4) = endpointMeanCornerK 45 30 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 31 (0 : Fin 4) = endpointMeanCornerA 45 30 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 31 (1 : Fin 4)) (endpointMeanCornerA 45 31 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 31 (2 : Fin 4)) (endpointMeanCornerA 45 31 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 31 (2 : Fin 4) = endpointMeanCornerK 45 30 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 31 (2 : Fin 4) = endpointMeanCornerA 45 30 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_30.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 31 (3 : Fin 4)) (endpointMeanCornerA 45 31 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 31 h) (endpointMeanCornerA 45 31 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 31) (prefactors h) runs ≤
      endpointMeanCorner 45 31 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 31 h ≤ endpointMeanCorner 45 31 h :=
  endpointMeanNumericCorner_le_of_runs 45 31 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1045,1064,121⟩,⟨1064,1104,122⟩,⟨1104,1148,123⟩,⟨1148,1195,124⟩,⟨1195,1246,125⟩,⟨1246,1302,126⟩,⟨1302,1363,127⟩,⟨1363,1430,128⟩,⟨1430,1505,129⟩,⟨1505,1587,130⟩,⟨1587,1679,131⟩,⟨1679,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3355547375176990) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4225698528767851) (.leaf 0))) (.branch (.branch (.leaf 2815980748587102) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3731780999957472) (.leaf 0))) (.branch (.branch (.leaf 2614644087767589) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3058025016033309) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3531884930655958) (.leaf 0))) (.branch (.branch (.leaf 2526023744149376) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4536952222143831) (.leaf 0))) (.branch (.branch (.leaf 2931136630345157) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3960635795447541) (.leaf 0))) (.branch (.branch (.leaf 2710928166825213) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3198657103415327) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3441053481899172) (.leaf 0))) (.branch (.branch (.leaf 2484293047274159) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4374786511658393) (.leaf 0))) (.branch (.branch (.leaf 2872201744084598) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3842187164872699) (.leaf 0))) (.branch (.branch (.leaf 2661763874018365) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3126479450501765) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3628586228548274) (.leaf 0))) (.branch (.branch (.leaf 2569437414628749) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 2992998738063555) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4088094744292971) (.leaf 0))) (.branch (.branch (.leaf 2762281022269636) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3274888905452000) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3421193899819975) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4334935202507499) (.leaf 0))) (.branch (.branch (.leaf 2858567488624671) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3815391190430910) (.leaf 0))) (.branch (.branch (.leaf 2649550961598695) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3110533029838482) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3605772204737798) (.leaf 0))) (.branch (.branch (.leaf 2557726784153873) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4663412992300594) (.leaf 0))) (.branch (.branch (.leaf 2978353430593673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4055847037014753) (.leaf 0))) (.branch (.branch (.leaf 2749439951365213) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3257251304502708) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3510655440901949) (.leaf 0))) (.branch (.branch (.leaf 2514526517428823) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4492175037510959) (.leaf 0))) (.branch (.branch (.leaf 2917028058523220) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3931333220497126) (.leaf 0))) (.branch (.branch (.leaf 2698419087886995) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3181921500292008) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3707127794331435) (.leaf 0))) (.branch (.branch (.leaf 2602696024110030) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3042770883816448) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4189973801849631) (.leaf 0))) (.branch (.branch (.leaf 2802766639727628) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3336876005363668) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3529880842964482) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4621995368184166) (.leaf 0))) (.branch (.branch (.leaf 2905878534344369) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3987637655049559) (.leaf 0))) (.branch (.branch (.leaf 2681554786280220) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3181449285756310) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3741905846740312) (.leaf 0))) (.branch (.branch (.leaf 2584128734641667) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5044112549382402) (.leaf 0))) (.branch (.branch (.leaf 3036149146338334) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4276508709634126) (.leaf 0))) (.branch (.branch (.leaf 2788301968861717) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3344747494055201) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3632155225787315) (.leaf 0))) (.branch (.branch (.leaf 2538516514488744) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4821864369777195) (.leaf 0))) (.branch (.branch (.leaf 2969293770544776) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4125955552765155) (.leaf 0))) (.branch (.branch (.leaf 2733676231590424) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3260632584116711) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3860043314830774) (.leaf 0))) (.branch (.branch (.leaf 2631759383222857) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3106752150619425) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4441117424754831) (.leaf 0))) (.branch (.branch (.leaf 2845629543908214) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3434302486739346) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3604822868848333) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4755207189891799) (.leaf 0))) (.branch (.branch (.leaf 2952816617518336) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4085710861776276) (.leaf 0))) (.branch (.branch (.leaf 2719570832293833) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3240209640917412) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3827311693764473) (.leaf 0))) (.branch (.branch (.leaf 2618481271028580) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5202462700898056) (.leaf 0))) (.branch (.branch (.leaf 3088562555272306) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4390166612091428) (.leaf 0))) (.branch (.branch (.leaf 2830481273328379) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3410928248102386) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3712088978887633) (.leaf 0))) (.branch (.branch (.leaf 2571200112448541) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4966814741342511) (.leaf 0))) (.branch (.branch (.leaf 3018871179731685) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4231400602375377) (.leaf 0))) (.branch (.branch (.leaf 2773705961511677) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3322954056502409) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3951468909767625) (.leaf 0))) (.branch (.branch (.leaf 2667886388263432) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3162218745323877) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4563972049665411) (.leaf 0))) (.branch (.branch (.leaf 2890106913265768) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3504676298410464) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 32) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 32 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 32 (0 : Fin 4)) (endpointMeanCornerA 45 32 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 32 (0 : Fin 4) = endpointMeanCornerK 45 31 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 32 (0 : Fin 4) = endpointMeanCornerA 45 31 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 32 (1 : Fin 4)) (endpointMeanCornerA 45 32 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 32 (2 : Fin 4)) (endpointMeanCornerA 45 32 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 32 (2 : Fin 4) = endpointMeanCornerK 45 31 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 32 (2 : Fin 4) = endpointMeanCornerA 45 31 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_31.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 32 (3 : Fin 4)) (endpointMeanCornerA 45 32 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 32 h) (endpointMeanCornerA 45 32 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 32) (prefactors h) runs ≤
      endpointMeanCorner 45 32 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 32 h ≤ endpointMeanCorner 45 32 h :=
  endpointMeanNumericCorner_le_of_runs 45 32 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1054,1092,121⟩,⟨1092,1133,122⟩,⟨1133,1178,123⟩,⟨1178,1227,124⟩,⟨1227,1280,125⟩,⟨1280,1337,126⟩,⟨1337,1400,127⟩,⟨1400,1470,128⟩,⟨1470,1546,129⟩,⟨1546,1631,130⟩,⟨1631,1726,131⟩,⟨1726,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3421193899819975) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4334935202507499) (.leaf 0))) (.branch (.branch (.leaf 2858567488624671) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3815391190430910) (.leaf 0))) (.branch (.branch (.leaf 2649550961598695) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3110533029838482) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3605772204737798) (.leaf 0))) (.branch (.branch (.leaf 2557726784153873) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4663412992300594) (.leaf 0))) (.branch (.branch (.leaf 2978353430593673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4055847037014753) (.leaf 0))) (.branch (.branch (.leaf 2749439951365213) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3257251304502708) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3510655440901949) (.leaf 0))) (.branch (.branch (.leaf 2514526517428823) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4492175037510959) (.leaf 0))) (.branch (.branch (.leaf 2917028058523220) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3931333220497126) (.leaf 0))) (.branch (.branch (.leaf 2698419087886995) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3181921500292008) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3707127794331435) (.leaf 0))) (.branch (.branch (.leaf 2602696024110030) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3042770883816448) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4189973801849631) (.leaf 0))) (.branch (.branch (.leaf 2802766639727628) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3336876005363668) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3488124705599797) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4446995705445667) (.leaf 0))) (.branch (.branch (.leaf 2901798277961208) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3900874659092718) (.leaf 0))) (.branch (.branch (.leaf 2684923860555879) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3163942635847546) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3681205205642120) (.leaf 0))) (.branch (.branch (.leaf 2589827715408540) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4793398667637233) (.leaf 0))) (.branch (.branch (.leaf 3026330832106096) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4153347098102098) (.leaf 0))) (.branch (.branch (.leaf 2788498839132293) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3316918856152550) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3581665234081813) (.leaf 0))) (.branch (.branch (.leaf 2545127924336597) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4612713446441288) (.leaf 0))) (.branch (.branch (.leaf 2962553975094689) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4022547634296825) (.leaf 0))) (.branch (.branch (.leaf 2735579081581087) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3238346707315038) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3787369409987224) (.leaf 0))) (.branch (.branch (.leaf 2636385130593626) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3093370716685062) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4294391778638311) (.leaf 0))) (.branch (.branch (.leaf 2843845638238359) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3400036397153749) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3604822868848333) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4755207189891799) (.leaf 0))) (.branch (.branch (.leaf 2952816617518336) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4085710861776276) (.leaf 0))) (.branch (.branch (.leaf 2719570832293833) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3240209640917412) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3827311693764473) (.leaf 0))) (.branch (.branch (.leaf 2618481271028580) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5202462700898056) (.leaf 0))) (.branch (.branch (.leaf 3088562555272306) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4390166612091428) (.leaf 0))) (.branch (.branch (.leaf 2830481273328379) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3410928248102386) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3712088978887633) (.leaf 0))) (.branch (.branch (.leaf 2571200112448541) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4966814741342511) (.leaf 0))) (.branch (.branch (.leaf 3018871179731685) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4231400602375377) (.leaf 0))) (.branch (.branch (.leaf 2773705961511677) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3322954056502409) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3951468909767625) (.leaf 0))) (.branch (.branch (.leaf 2667886388263432) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3162218745323877) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4563972049665411) (.leaf 0))) (.branch (.branch (.leaf 2890106913265768) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3504676298410464) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3681355970321820) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4892258346784576) (.leaf 0))) (.branch (.branch (.leaf 3000512882297623) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4186196111599605) (.leaf 0))) (.branch (.branch (.leaf 2758125826742097) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3300055281125836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3914666857261219) (.leaf 0))) (.branch (.branch (.leaf 2653290478455293) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5365783948962319) (.leaf 0))) (.branch (.branch (.leaf 3141880783206815) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4506845230667439) (.leaf 0))) (.branch (.branch (.leaf 2873298634126509) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3478418485814345) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3793781854186081) (.leaf 0))) (.branch (.branch (.leaf 2604304514279219) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5116122475248556) (.leaf 0))) (.branch (.branch (.leaf 3069276368078097) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4339540460096139) (.leaf 0))) (.branch (.branch (.leaf 2814321854219531) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3386466698337627) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4045059931029474) (.leaf 0))) (.branch (.branch (.leaf 2704509320287874) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3218675616361604) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4690225201887568) (.leaf 0))) (.branch (.branch (.leaf 2935279466713331) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3576492170991541) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 33) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 33 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 33 (0 : Fin 4)) (endpointMeanCornerA 45 33 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 33 (0 : Fin 4) = endpointMeanCornerK 45 32 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 33 (0 : Fin 4) = endpointMeanCornerA 45 32 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 33 (1 : Fin 4)) (endpointMeanCornerA 45 33 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 33 (2 : Fin 4)) (endpointMeanCornerA 45 33 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 33 (2 : Fin 4) = endpointMeanCornerK 45 32 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 33 (2 : Fin 4) = endpointMeanCornerA 45 32 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_32.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 33 (3 : Fin 4)) (endpointMeanCornerA 45 33 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 33 h) (endpointMeanCornerA 45 33 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 33) (prefactors h) runs ≤
      endpointMeanCorner 45 33 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 33 h ≤ endpointMeanCorner 45 33 h :=
  endpointMeanNumericCorner_le_of_runs 45 33 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33

namespace SingularValueBounds.KL.Certificates.EndpointEntropyBox45_34
open SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private noncomputable def runs : List EndpointRateRun :=
[⟨1061,1070,120⟩,⟨1070,1110,121⟩,⟨1110,1152,122⟩,⟨1152,1198,123⟩,⟨1198,1248,124⟩,⟨1248,1302,125⟩,⟨1302,1360,126⟩,⟨1360,1425,127⟩,⟨1425,1496,128⟩,⟨1496,1574,129⟩,⟨1574,1660,130⟩,⟨1660,1757,131⟩,⟨1757,1758,132⟩,⟨1758,1815,131⟩,⟨1815,1875,130⟩,⟨1875,1940,129⟩,⟨1940,2009,128⟩,⟨2009,2084,127⟩,⟨2084,2164,126⟩,⟨2164,2250,125⟩,⟨2250,2344,124⟩,⟨2344,2446,123⟩,⟨2446,2557,122⟩,⟨2557,2679,121⟩,⟨2679,2813,120⟩,⟨2813,2961,119⟩,⟨2961,3125,118⟩,⟨3125,3309,117⟩,⟨3309,3516,116⟩,⟨3516,3750,115⟩,⟨3750,4018,114⟩,⟨4018,4327,113⟩,⟨4327,4687,112⟩,⟨4687,5113,111⟩,⟨5113,5625,110⟩,⟨5625,6250,109⟩,⟨6250,7031,108⟩,⟨7031,8000,107⟩]
private noncomputable def prefactor0 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3488124705599797) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4446995705445667) (.leaf 0))) (.branch (.branch (.leaf 2901798277961208) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3900874659092718) (.leaf 0))) (.branch (.branch (.leaf 2684923860555879) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3163942635847546) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3681205205642120) (.leaf 0))) (.branch (.branch (.leaf 2589827715408540) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4793398667637233) (.leaf 0))) (.branch (.branch (.leaf 3026330832106096) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4153347098102098) (.leaf 0))) (.branch (.branch (.leaf 2788498839132293) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3316918856152550) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3581665234081813) (.leaf 0))) (.branch (.branch (.leaf 2545127924336597) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4612713446441288) (.leaf 0))) (.branch (.branch (.leaf 2962553975094689) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4022547634296825) (.leaf 0))) (.branch (.branch (.leaf 2735579081581087) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3238346707315038) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3787369409987224) (.leaf 0))) (.branch (.branch (.leaf 2636385130593626) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3093370716685062) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4294391778638311) (.leaf 0))) (.branch (.branch (.leaf 2843845638238359) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3400036397153749) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor1 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3510724698549847) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4484989286992316) (.leaf 0))) (.branch (.branch (.leaf 2916353342393476) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3929792659981118) (.leaf 0))) (.branch (.branch (.leaf 2696819460984096) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3181948859761796) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3706698603834841) (.leaf 0))) (.branch (.branch (.leaf 2600617307426068) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4837527441914413) (.leaf 0))) (.branch (.branch (.leaf 3042494433805832) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4186365217166864) (.leaf 0))) (.branch (.branch (.leaf 2801641387063364) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3337049950447433) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3605652922506617) (.leaf 0))) (.branch (.branch (.leaf 2555410929394765) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4653607433868311) (.leaf 0))) (.branch (.branch (.leaf 2977886630050926) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4053420336758866) (.leaf 0))) (.branch (.branch (.leaf 2748079118160660) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3257376593538178) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3814500741427539) (.leaf 0))) (.branch (.branch (.leaf 2647711459803819) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3110423630524604) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4329772866059641) (.leaf 0))) (.branch (.branch (.leaf 2857671999719211) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3421354419010891) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor2 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3681355970321820) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4892258346784576) (.leaf 0))) (.branch (.branch (.leaf 3000512882297623) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4186196111599605) (.leaf 0))) (.branch (.branch (.leaf 2758125826742097) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3300055281125836) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3914666857261219) (.leaf 0))) (.branch (.branch (.leaf 2653290478455293) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5365783948962319) (.leaf 0))) (.branch (.branch (.leaf 3141880783206815) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4506845230667439) (.leaf 0))) (.branch (.branch (.leaf 2873298634126509) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3478418485814345) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3793781854186081) (.leaf 0))) (.branch (.branch (.leaf 2604304514279219) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5116122475248556) (.leaf 0))) (.branch (.branch (.leaf 3069276368078097) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4339540460096139) (.leaf 0))) (.branch (.branch (.leaf 2814321854219531) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3386466698337627) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4045059931029474) (.leaf 0))) (.branch (.branch (.leaf 2704509320287874) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3218675616361604) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4690225201887568) (.leaf 0))) (.branch (.branch (.leaf 2935279466713331) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3576492170991541) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactor3 : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3707226394457370) (.leaf 0))) (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4938814285825276) (.leaf 0))) (.branch (.branch (.leaf 3016582233080810) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4220237416042007) (.leaf 0))) (.branch (.branch (.leaf 2771098575368923) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3320248456262518) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3944226087389434) (.leaf 0))) (.branch (.branch (.leaf 2664996077015673) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5421355886414735) (.leaf 0))) (.branch (.branch (.leaf 3159857288770330) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4546423188814004) (.leaf 0))) (.branch (.branch (.leaf 2887714542088805) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3501210691698993) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 3821410395511303) (.leaf 0))) (.branch (.branch (.leaf 2615433761284064) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 5166882550038077) (.leaf 0))) (.branch (.branch (.leaf 3086264430686386) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4376197778749220) (.leaf 0))) (.branch (.branch (.leaf 2827992223447866) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3407906205884784) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4076746973905983) (.leaf 0))) (.branch (.branch (.leaf 2716828344260581) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3237717681538138) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))) (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 4733080989257734) (.leaf 0))) (.branch (.branch (.leaf 2950493343050058) (.leaf 0)) (.branch (.leaf 0) (.leaf 0)))) (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))) (.branch (.branch (.leaf 3600756343231851) (.leaf 0)) (.branch (.leaf 0) (.leaf 0))))))))
private noncomputable def prefactorTrees : EntropyLookup (EntropyLookup ℤ) :=
  .branch (.branch (.leaf prefactor0) (.leaf prefactor2))
    (.branch (.leaf prefactor1) (.leaf prefactor3))
private noncomputable def prefactors (h : Fin 4) (q : ℕ) : ℤ :=
  (prefactorTrees.get h.val).get (q-90)

private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 34) 8000 runs := by decide +kernel
private theorem domains : ∀ r ∈ runs,
    90 ≤ r.rate ∧ r.rate ≤ 200 ∧ r.start ≤ r.stop ∧ r.stop ≤ 8000 := by decide +kernel
private theorem rates : ∀ r ∈ runs, EndpointRateRunValid 45 34 r := by decide +kernel
private theorem prefactorValues0 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 34 (0 : Fin 4)) (endpointMeanCornerA 45 34 (0 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (0 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 34 (0 : Fin 4) = endpointMeanCornerK 45 33 (1 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 34 (0 : Fin 4) = endpointMeanCornerA 45 33 (1 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33.prefactors (1 : Fin 4) s.rate = prefactors (0 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33.prefactorValues1 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33.prefactors (1 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues1 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 34 (1 : Fin 4)) (endpointMeanCornerA 45 34 (1 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (1 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues2 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 34 (2 : Fin 4)) (endpointMeanCornerA 45 34 (2 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (2 : Fin 4) r.rate) := by
  have hk : endpointMeanCornerK 45 34 (2 : Fin 4) = endpointMeanCornerK 45 33 (3 : Fin 4) := by decide +kernel
  have ha : endpointMeanCornerA 45 34 (2 : Fin 4) = endpointMeanCornerA 45 33 (3 : Fin 4) := by decide +kernel
  have bridge : ∀ r ∈ runs, ∃ s ∈ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33.runs,
      s.rate = r.rate ∧ SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33.prefactors (3 : Fin 4) s.rate = prefactors (2 : Fin 4) r.rate := by decide +kernel
  intro r hr
  obtain ⟨s, hs, hrate, hvalue⟩ := bridge r hr
  have hp := SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33.prefactorValues3 s hs
  rw [hk, ha]
  calc
    _ = fixedQ (SingularValueBounds.KL.Certificates.EndpointEntropyBox45_33.prefactors (3 : Fin 4) s.rate) := by simpa only [hrate] using hp
    _ = _ := congrArg fixedQ hvalue

private theorem prefactorValues3 : ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 34 (3 : Fin 4)) (endpointMeanCornerA 45 34 (3 : Fin 4))
      ((r.rate:ℚ)/100) = fixedQ (prefactors (3 : Fin 4) r.rate) := by
  simp only [endpointJointPrefactorQ_eq_integer]
  decide +kernel

private theorem prefactorValues : ∀ h : Fin 4, ∀ r ∈ runs,
    endpointJointPrefactorQ (endpointMeanCornerK 45 34 h) (endpointMeanCornerA 45 34 h)
      ((r.rate:ℚ)/100) = fixedQ (prefactors h r.rate) := by
  intro h
  fin_cases h
  · exact prefactorValues0
  · exact prefactorValues1
  · exact prefactorValues2
  · exact prefactorValues3
private theorem totalBounds : ∀ h : Fin 4,
    endpointEntropyByRuns (endpointMeanCutoff 45 34) (prefactors h) runs ≤
      endpointMeanCorner 45 34 h := by decide +kernel

theorem numerical : ∀ h : Fin 4,
    endpointMeanNumericCorner 45 34 h ≤ endpointMeanCorner 45 34 h :=
  endpointMeanNumericCorner_le_of_runs 45 34 (by unfold endpointMeanActive; decide +kernel) runs prefactors
    cover domains rates prefactorValues totalBounds
end SingularValueBounds.KL.Certificates.EndpointEntropyBox45_34

namespace SingularValueBounds.KL.Certificates
theorem endpointMeanEntropyRow45 (ai : Fin 42)
    (hactive : endpointMeanActive 45 ai) (h : Fin 4) :
    endpointMeanNumericCorner 45 ai h ≤ endpointMeanCorner 45 ai h := by
  fin_cases ai
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 0) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 1) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 2) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 3) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 4) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 5) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 6) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 7) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 8) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 9) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 10) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 11) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 12) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 13) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 14) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 15) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 16) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 17) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 18) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 19) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 20) hactive)
  · exact EndpointEntropyBox45_21.numerical h
  · exact EndpointEntropyBox45_22.numerical h
  · exact EndpointEntropyBox45_23.numerical h
  · exact EndpointEntropyBox45_24.numerical h
  · exact EndpointEntropyBox45_25.numerical h
  · exact EndpointEntropyBox45_26.numerical h
  · exact EndpointEntropyBox45_27.numerical h
  · exact EndpointEntropyBox45_28.numerical h
  · exact EndpointEntropyBox45_29.numerical h
  · exact EndpointEntropyBox45_30.numerical h
  · exact EndpointEntropyBox45_31.numerical h
  · exact EndpointEntropyBox45_32.numerical h
  · exact EndpointEntropyBox45_33.numerical h
  · exact EndpointEntropyBox45_34.numerical h
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 35) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 36) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 37) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 38) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 39) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 40) hactive)
  · exact False.elim ((by unfold endpointMeanActive; decide +kernel : ¬ endpointMeanActive 45 41) hactive)
end SingularValueBounds.KL.Certificates
