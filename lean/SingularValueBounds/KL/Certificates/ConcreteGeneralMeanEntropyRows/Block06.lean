import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs
import SingularValueBounds.KL.Certificates.GeneralMeanPrefactorLogs
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block08
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block09
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 420. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0420
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5004340690) (.branch 2 (.leaf 4832554240) (.leaf 4668529413))) (.branch 5 (.branch 4 (.leaf 4511819780) (.leaf 4362010572)) (.branch 6 (.leaf 4218715921) (.leaf 4081576390)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3950256770) (.leaf 3824444095)) (.branch 10 (.leaf 3703845863) (.leaf 3588188422))) (.branch 13 (.branch 12 (.leaf 3477215514) (.leaf 3370686954)) (.branch 14 (.leaf 3268377433) (.leaf 3170075420))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3075582169) (.branch 17 (.leaf 2984710805) (.leaf 2897285492))) (.branch 20 (.branch 19 (.leaf 2813140667) (.leaf 2732120335)) (.branch 21 (.leaf 2654077427) (.leaf 2578873201)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2506376698) (.leaf 2436464227)) (.branch 25 (.leaf 2369018905) (.leaf 2303930217))) (.branch 28 (.branch 27 (.leaf 2241093619) (.leaf 2180410159)) (.branch 29 (.leaf 2121786138) (.leaf 2065132784)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2010365954) (.branch 32 (.leaf 1957405854) (.leaf 1906176785))) (.branch 35 (.branch 34 (.leaf 1856606894) (.leaf 1808627952)) (.branch 36 (.leaf 1762175144) (.leaf 1717186871)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1673604565) (.leaf 1631372519)) (.branch 40 (.leaf 1590437723) (.leaf 1550749717))) (.branch 43 (.branch 42 (.leaf 1512260443) (.leaf 1474924121)) (.branch 44 (.leaf 1438697115) (.leaf 1403537825))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1369406570) (.branch 47 (.leaf 1336265489) (.leaf 1304078444))) (.branch 50 (.branch 49 (.leaf 1272810926) (.leaf 1242429971)) (.branch 51 (.leaf 1212904082) (.leaf 1184203147)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1156298371) (.leaf 1129162210)) (.branch 55 (.leaf 1102768303) (.leaf 1077091417))) (.branch 58 (.branch 57 (.leaf 1052107385) (.leaf 1027793058)) (.branch 59 (.leaf 1004126251) (.leaf 981085695))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 958650996) (.branch 62 (.leaf 936802587) (.leaf 915521694))) (.branch 65 (.branch 64 (.leaf 894790291) (.leaf 874591071)) (.branch 66 (.leaf 854907407) (.leaf 835723322)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 817023457) (.leaf 798793046)) (.branch 70 (.leaf 781017883) (.leaf 763684300))) (.branch 73 (.branch 72 (.leaf 746779143) (.leaf 730289745)) (.branch 74 (.leaf 714203907) (.leaf 698509876))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 683196328) (.branch 77 (.leaf 668252342) (.leaf 653667390))) (.branch 80 (.branch 79 (.leaf 639431315) (.leaf 625534317)) (.branch 81 (.leaf 611966939) (.leaf 598720048)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 585784824) (.leaf 573152748)) (.branch 85 (.leaf 560815588) (.leaf 548765386))) (.branch 88 (.branch 87 (.leaf 536994449) (.leaf 525495337)) (.branch 89 (.leaf 514260850) (.leaf 503284026)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 492558123) (.branch 92 (.leaf 482076614) (.leaf 471833179))) (.branch 95 (.branch 94 (.leaf 461821697) (.leaf 452036237)) (.branch 96 (.leaf 442471050) (.leaf 433120564)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 423979377) (.leaf 415042250)) (.branch 100 (.leaf 406304100) (.leaf 397759996))) (.branch 103 (.branch 102 (.leaf 389405153) (.leaf 381234925)) (.branch 104 (.leaf 373244801) (.leaf 365430403))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 357787476) (.leaf 350311888)) (.branch 108 (.leaf 342999621) (.leaf 335846774))) (.branch 111 (.branch 110 (.leaf 328849551) (.leaf 322004265)) (.branch 112 (.leaf 315307328) (.leaf 308755251)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 302344640) (.leaf 296072193)) (.branch 116 (.leaf 289934696) (.leaf 283929021))) (.branch 119 (.branch 118 (.leaf 278052124) (.leaf 272301039)) (.branch 120 (.leaf 266672881) (.leaf 261164839)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 420).prefactor = (1192784052154809/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 420).cutoff/(generalMeanRows 420).c)).2 =
    (96222215879131/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 420).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 420).q*(generalMeanRows 420).c/2-2 = (3223/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable132.value]
  have hcontinuation : (generalMeanRows 420).q*(generalMeanRows 420).cutoff/2-2 = (16650/7843:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable158.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 420).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 420).criticalRate j.val*(generalMeanRows 420).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 420).c*(generalMeanRows 420).criticalPoint j.val)).2-
      (generalMeanRows 420).J/2-(generalMeanRows 420).error (generalMeanGrid j.val)+
      (generalMeanRows 420).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 420).c)).2-
      (generalMeanRows 420).J/2-(generalMeanRows 420).error 4 := by
  have he : (generalMeanRows 420).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 420) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 420)
    (generalMeanRows_prefactorDomain 420) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0420

/-! Kernel-checked entropy margins for general spectral rectangle 421. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0421
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4997170041) (.branch 2 (.leaf 4825651117) (.leaf 4661874365))) (.branch 5 (.branch 4 (.leaf 4505394997) (.leaf 4355799746)) (.branch 6 (.leaf 4212704119) (.leaf 4075749938)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3944603151) (.leaf 3818951849)) (.branch 10 (.leaf 3698504498) (.leaf 3582988335))) (.branch 13 (.branch 12 (.leaf 3472147916) (.leaf 3365743803)) (.branch 14 (.leaf 3263551370) (.leaf 3165359711))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3070970654) (.branch 17 (.leaf 2980197851) (.leaf 2892865944))) (.branch 20 (.branch 19 (.leaf 2808809812) (.leaf 2727873862)) (.branch 21 (.leaf 2649911394) (.leaf 2574784004)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2502361037) (.leaf 2432519086)) (.branch 25 (.leaf 2365141523) (.leaf 2300118069))) (.branch 28 (.branch 27 (.leaf 2237344390) (.leaf 2176721732)) (.branch 29 (.leaf 2118156572) (.leaf 2061560298)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2006848914) (.branch 32 (.leaf 1953942760) (.leaf 1902766256))) (.branch 35 (.branch 34 (.leaf 1853247658) (.leaf 1805318839)) (.branch 36 (.leaf 1758915071) (.leaf 1713974836)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1670439641) (.leaf 1628253842)) (.branch 40 (.leaf 1587364491) (.leaf 1547721178))) (.branch 43 (.branch 42 (.leaf 1509275896) (.leaf 1471982904)) (.branch 44 (.leaf 1435798608) (.leaf 1400681439))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1366591748) (.branch 47 (.leaf 1333491700) (.leaf 1301345180))) (.branch 50 (.branch 49 (.leaf 1270117702) (.leaf 1239776319)) (.branch 51 (.leaf 1210289550) (.leaf 1181627298)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1153760779) (.leaf 1126662461)) (.branch 55 (.leaf 1100305992) (.leaf 1074666146))) (.branch 58 (.branch 57 (.leaf 1049718764) (.leaf 1025440702)) (.branch 59 (.leaf 1001809779) (.leaf 978804731))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 956405168) (.branch 62 (.leaf 934591524) (.leaf 913345028))) (.branch 65 (.branch 64 (.leaf 892647657) (.leaf 872482103)) (.branch 66 (.leaf 852831742) (.leaf 833680596)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 815013308) (.leaf 796815111)) (.branch 70 (.leaf 779071801) (.leaf 761769710))) (.branch 73 (.branch 72 (.leaf 744895682) (.leaf 728437053)) (.branch 74 (.leaf 712381622) (.leaf 696717637))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 681433773) (.branch 77 (.leaf 666519111) (.leaf 651963121))) (.branch 80 (.branch 79 (.leaf 637755649) (.leaf 623886894)) (.branch 81 (.leaf 610347398) (.leaf 597128030)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 584219972) (.leaf 571614704)) (.branch 85 (.leaf 559303994) (.leaf 547279888))) (.branch 88 (.branch 87 (.leaf 535534692) (.leaf 524060966)) (.branch 89 (.leaf 512851516) (.leaf 501899377)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 491197810) (.branch 92 (.leaf 480740290) (.leaf 470520499))) (.branch 95 (.branch 94 (.leaf 460532318) (.leaf 450769817)) (.branch 96 (.leaf 441227250) (.leaf 431899047)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 422779809) (.leaf 413864298)) (.branch 100 (.leaf 405147435) (.leaf 396624291))) (.branch 103 (.branch 102 (.leaf 388290083) (.leaf 380140168)) (.branch 104 (.leaf 372170039) (.leaf 364375320))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 356751758) (.leaf 349295225)) (.branch 108 (.leaf 342001707) (.leaf 334867304))) (.branch 111 (.branch 110 (.leaf 327888226) (.leaf 321060786)) (.branch 112 (.leaf 314381402) (.leaf 307846586)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 301452949) (.leaf 295197191)) (.branch 116 (.leaf 289076102) (.leaf 283086557))) (.branch 119 (.branch 118 (.leaf 277225516) (.leaf 271490017)) (.branch 120 (.leaf 265877178) (.leaf 260384189)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 421).prefactor = (594491010633323/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 421).cutoff/(generalMeanRows 421).c)).2 =
    (191711830894597/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 421).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 421).q*(generalMeanRows 421).c/2-2 = (3223/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable132.value]
  have hcontinuation : (generalMeanRows 421).q*(generalMeanRows 421).cutoff/2-2 = (33254/15709:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable163.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 421).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 421).criticalRate j.val*(generalMeanRows 421).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 421).c*(generalMeanRows 421).criticalPoint j.val)).2-
      (generalMeanRows 421).J/2-(generalMeanRows 421).error (generalMeanGrid j.val)+
      (generalMeanRows 421).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 421).c)).2-
      (generalMeanRows 421).J/2-(generalMeanRows 421).error 4 := by
  have he : (generalMeanRows 421).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 421) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 421)
    (generalMeanRows_prefactorDomain 421) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0421

/-! Kernel-checked entropy margins for general spectral rectangle 422. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0422
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5005785720) (.branch 2 (.leaf 4833971078) (.leaf 4669911957))) (.branch 5 (.branch 4 (.leaf 4513162801) (.leaf 4363309631)) (.branch 6 (.leaf 4219967291) (.leaf 4082776986)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3951404087) (.leaf 3825536148)) (.branch 10 (.leaf 3704881133) (.leaf 3589165807))) (.branch 13 (.branch 12 (.leaf 3478134287) (.leaf 3371546721)) (.branch 14 (.leaf 3269178096) (.leaf 3170817144))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3076265350) (.branch 17 (.leaf 2985336044) (.leaf 2897853568))) (.branch 20 (.branch 19 (.leaf 2813652514) (.leaf 2732577021)) (.branch 21 (.leaf 2654480137) (.leaf 2579223219)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2506675386) (.leaf 2436713020)) (.branch 25 (.leaf 2369219291) (.leaf 2304083729))) (.branch 28 (.branch 27 (.leaf 2241201821) (.leaf 2180474643)) (.branch 29 (.leaf 2121808510) (.leaf 2065114658)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2010308945) (.branch 32 (.leaf 1957311575) (.leaf 1906046837))) (.branch 35 (.branch 34 (.leaf 1856442864) (.leaf 1808431410)) (.branch 36 (.leaf 1761947637) (.leaf 1716929920)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1673319665) (.leaf 1631061134)) (.branch 40 (.leaf 1590101284) (.leaf 1550389622))) (.branch 43 (.branch 42 (.leaf 1511878056) (.leaf 1474520767)) (.branch 44 (.leaf 1438274085) (.leaf 1403096370))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1368947904) (.branch 47 (.leaf 1335790788) (.leaf 1303588845))) (.branch 50 (.branch 49 (.leaf 1272307526) (.leaf 1241913832)) (.branch 51 (.leaf 1212376224) (.leaf 1183664555)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1155749992) (.leaf 1128604953)) (.branch 55 (.leaf 1102203043) (.leaf 1076518990))) (.branch 58 (.branch 57 (.leaf 1051528596) (.leaf 1027208676)) (.branch 59 (.leaf 1003537011) (.leaf 980492300))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 958054117) (.branch 62 (.leaf 936202865) (.leaf 914919737))) (.branch 65 (.branch 64 (.leaf 894186681) (.leaf 873986360)) (.branch 66 (.leaf 854302119) (.leaf 835117954)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 816418482) (.leaf 798188910)) (.branch 70 (.leaf 780415008) (.leaf 763083086))) (.branch 73 (.branch 72 (.leaf 746179966) (.leaf 729692959)) (.branch 74 (.leaf 713609847) (.leaf 697918856))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 682608641) (.branch 77 (.leaf 667668264) (.leaf 653087178))) (.branch 80 (.branch 79 (.leaf 638855211) (.leaf 624962544)) (.branch 81 (.leaf 611399705) (.leaf 598157545)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 585227232) (.leaf 572600231)) (.branch 85 (.leaf 560268297) (.leaf 548223460))) (.branch 88 (.branch 87 (.leaf 536458013) (.leaf 524964506)) (.branch 89 (.leaf 513735729) (.leaf 502764707)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 492044690) (.branch 92 (.leaf 481569140) (.leaf 471331729))) (.branch 95 (.branch 94 (.leaf 461326327) (.leaf 451546994)) (.branch 96 (.leaf 441987975) (.leaf 432643690)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 423508729) (.leaf 414577847)) (.branch 100 (.leaf 405845955) (.leaf 397308115))) (.branch 103 (.branch 102 (.leaf 388959538) (.leaf 380795572)) (.branch 104 (.leaf 372811702) (.leaf 365003543))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 357366838) (.leaf 349897449)) (.branch 108 (.leaf 342591356) (.leaf 335444653))) (.branch 111 (.branch 110 (.leaf 328453542) (.leaf 321614331)) (.branch 112 (.leaf 314923430) (.leaf 308377348)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 301972687) (.leaf 295706143)) (.branch 116 (.leaf 289574501) (.leaf 283574630))) (.branch 119 (.branch 118 (.leaf 277703484) (.leaf 271958096)) (.branch 120 (.leaf 266335579) (.leaf 260833120)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 422).prefactor = (297757989745873/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 422).cutoff/(generalMeanRows 422).c)).2 =
    (191711830894597/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 422).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 422).q*(generalMeanRows 422).c/2-2 = (3223/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable132.value]
  have hcontinuation : (generalMeanRows 422).q*(generalMeanRows 422).cutoff/2-2 = (33254/15709:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable163.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 422).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 422).criticalRate j.val*(generalMeanRows 422).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 422).c*(generalMeanRows 422).criticalPoint j.val)).2-
      (generalMeanRows 422).J/2-(generalMeanRows 422).error (generalMeanGrid j.val)+
      (generalMeanRows 422).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 422).c)).2-
      (generalMeanRows 422).J/2-(generalMeanRows 422).error 4 := by
  have he : (generalMeanRows 422).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 422) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 422)
    (generalMeanRows_prefactorDomain 422) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0422

/-! Kernel-checked entropy margins for general spectral rectangle 423. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0423
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4932186803) (.branch 2 (.leaf 4760544223) (.leaf 4596672094))) (.branch 5 (.branch 4 (.leaf 4440124799) (.leaf 4290488249)) (.branch 6 (.leaf 4147377139) (.leaf 4010432488)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3879319444) (.leaf 3753725316)) (.branch 10 (.leaf 3633357791) (.leaf 3517943338))) (.branch 13 (.branch 12 (.leaf 3407225756) (.leaf 3300964862)) (.branch 14 (.leaf 3198935292) (.leaf 3100925420))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3006736360) (.branch 17 (.leaf 2916181062) (.leaf 2829083485))) (.branch 20 (.branch 19 (.leaf 2745277829) (.leaf 2664607842)) (.branch 21 (.leaf 2586926174) (.leaf 2512093785)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2439979400) (.leaf 2370459003)) (.branch 25 (.leaf 2303415371) (.leaf 2238737644))) (.branch 28 (.branch 27 (.leaf 2176320921) (.leaf 2116065894)) (.branch 29 (.leaf 2057878501) (.leaf 2001669603)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1947354692) (.branch 32 (.leaf 1894853610) (.leaf 1844090289))) (.branch 35 (.branch 34 (.leaf 1794992516) (.leaf 1747491702)) (.branch 36 (.leaf 1701522676) (.leaf 1657023485)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1613935215) (.leaf 1572201816)) (.branch 40 (.leaf 1531769944) (.leaf 1492588806))) (.branch 43 (.branch 42 (.leaf 1454610023) (.leaf 1417787496)) (.branch 44 (.leaf 1382077282) (.leaf 1347437476))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1313828104) (.branch 47 (.leaf 1281211016) (.leaf 1249549794))) (.branch 50 (.branch 49 (.leaf 1218809658) (.leaf 1188957378)) (.branch 51 (.leaf 1159961201) (.leaf 1131790765)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1104417036) (.leaf 1077812234)) (.branch 55 (.leaf 1051949773) (.leaf 1026804202))) (.branch 58 (.branch 57 (.leaf 1002351143) (.leaf 978567244)) (.branch 59 (.leaf 955430122) (.leaf 932918322))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 911011267) (.branch 62 (.leaf 889689216) (.leaf 868933225))) (.branch 65 (.branch 64 (.leaf 848725110) (.leaf 829047407)) (.branch 66 (.leaf 809883343) (.leaf 791216798)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 773032278) (.leaf 755314887)) (.branch 70 (.leaf 738050297) (.leaf 721224721))) (.branch 73 (.branch 72 (.leaf 704824894) (.leaf 688838041)) (.branch 74 (.leaf 673251863) (.leaf 658054511))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 643234568) (.branch 77 (.leaf 628781029) (.leaf 614683283))) (.branch 80 (.branch 79 (.leaf 600931098) (.leaf 587514601)) (.branch 81 (.leaf 574424266) (.leaf 561650897)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 549185615) (.leaf 537019845)) (.branch 85 (.leaf 525145302) (.leaf 513553981))) (.branch 88 (.branch 87 (.leaf 502238144) (.leaf 491190310)) (.branch 89 (.leaf 480403242) (.leaf 469869942)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 459583637) (.branch 92 (.leaf 449537772) (.leaf 439726002))) (.branch 95 (.branch 94 (.leaf 430142182) (.leaf 420780361)) (.branch 96 (.leaf 411634774) (.leaf 402699833)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 393970124) (.leaf 385440396)) (.branch 100 (.leaf 377105561) (.leaf 368960679))) (.branch 103 (.branch 102 (.leaf 361000963) (.leaf 353221765)) (.branch 104 (.leaf 345618574) (.leaf 338187013))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 330922832) (.leaf 323821901)) (.branch 108 (.leaf 316880214) (.leaf 310093873))) (.branch 111 (.branch 110 (.leaf 303459097) (.leaf 296972205)) (.branch 112 (.leaf 290629625) (.leaf 284427880)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 278363591) (.leaf 272433473)) (.branch 116 (.leaf 266634329) (.leaf 260963049))) (.branch 119 (.branch 118 (.leaf 255416607) (.leaf 249992060)) (.branch 120 (.leaf 244686542) (.leaf 239497263)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 423).prefactor = (4765295928651677/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 423).cutoff/(generalMeanRows 423).c)).2 =
    (74865395776473/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 423).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 423).q*(generalMeanRows 423).c/2-2 = (3309/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable134.value]
  have hcontinuation : (generalMeanRows 423).q*(generalMeanRows 423).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable151.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 423).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 423).criticalRate j.val*(generalMeanRows 423).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 423).c*(generalMeanRows 423).criticalPoint j.val)).2-
      (generalMeanRows 423).J/2-(generalMeanRows 423).error (generalMeanGrid j.val)+
      (generalMeanRows 423).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 423).c)).2-
      (generalMeanRows 423).J/2-(generalMeanRows 423).error 4 := by
  have he : (generalMeanRows 423).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 423) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 423)
    (generalMeanRows_prefactorDomain 423) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0423

/-! Kernel-checked entropy margins for general spectral rectangle 424. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0424
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4940725059) (.branch 2 (.leaf 4768785344) (.leaf 4604629531))) (.branch 5 (.branch 4 (.leaf 4447811232) (.leaf 4297915642)) (.branch 6 (.leaf 4154556788) (.leaf 4017375068)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3886035051) (.leaf 3760223502)) (.branch 10 (.leaf 3639647605) (.leaf 3524033355))) (.branch 13 (.branch 12 (.leaf 3413124107) (.leaf 3306679261)) (.branch 14 (.leaf 3204473065) (.leaf 3106293525))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3011941411) (.branch 17 (.leaf 2921229351) (.leaf 2833980996))) (.branch 20 (.branch 19 (.leaf 2750030262) (.leaf 2669220625)) (.branch 21 (.leaf 2591404480) (.leaf 2516442546)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2444203322) (.leaf 2374562576)) (.branch 25 (.leaf 2307402883) (.leaf 2242613190))) (.branch 28 (.branch 27 (.leaf 2180088416) (.leaf 2119729080)) (.branch 29 (.leaf 2061440956) (.leaf 2005134753)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1950725816) (.branch 32 (.leaf 1898133848) (.leaf 1847282649))) (.branch 35 (.branch 34 (.leaf 1798099882) (.leaf 1750516838)) (.branch 36 (.leaf 1704468233) (.leaf 1659892008)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1616729146) (.leaf 1574923502)) (.branch 40 (.leaf 1534421637) (.leaf 1495172671))) (.branch 43 (.branch 42 (.leaf 1457128142) (.leaf 1420241871)) (.branch 44 (.leaf 1384469837) (.leaf 1349770066))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1316102511) (.branch 47 (.leaf 1283428959) (.leaf 1251712927))) (.branch 50 (.branch 49 (.leaf 1220919575) (.leaf 1191015618)) (.branch 51 (.leaf 1161969245) (.leaf 1133750042)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1106328925) (.leaf 1079678067)) (.branch 55 (.leaf 1053770835) (.leaf 1028581734))) (.branch 58 (.branch 57 (.leaf 1004086343) (.leaf 980261271)) (.branch 59 (.leaf 957084096) (.leaf 934533325))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 912588346) (.branch 62 (.leaf 891229383) (.leaf 870437462))) (.branch 65 (.branch 64 (.leaf 850194364) (.leaf 830482596)) (.branch 66 (.leaf 811285356) (.leaf 792586497)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 774370497) (.leaf 756622435)) (.branch 70 (.leaf 739327958) (.leaf 722473255))) (.branch 73 (.branch 72 (.leaf 706045037) (.leaf 690030509)) (.branch 74 (.leaf 674417349) (.leaf 659193689))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 644348091) (.branch 77 (.leaf 629869531) (.leaf 615747380))) (.branch 80 (.branch 79 (.leaf 601971388) (.leaf 588531665)) (.branch 81 (.leaf 575418669) (.leaf 562623188)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 550136327) (.leaf 537949496)) (.branch 85 (.leaf 526054397) (.leaf 514443010))) (.branch 88 (.branch 87 (.leaf 503107584) (.leaf 492040624)) (.branch 89 (.leaf 481234882) (.leaf 470683348)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 460379236) (.branch 92 (.leaf 450315980) (.leaf 440487225))) (.branch 95 (.branch 94 (.leaf 430886814) (.leaf 421508787)) (.branch 96 (.leaf 412347367) (.leaf 403396959)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 394652137) (.leaf 386107644)) (.branch 100 (.leaf 377758379) (.leaf 369599398))) (.branch 103 (.branch 102 (.leaf 361625903) (.leaf 353833238)) (.branch 104 (.leaf 346216885) (.leaf 338772459))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 331495702) (.leaf 324382479)) (.branch 108 (.leaf 317428774) (.leaf 310630686))) (.branch 111 (.branch 110 (.leaf 303984424) (.leaf 297486303)) (.branch 112 (.leaf 291132742) (.leaf 284920261)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 278845475) (.leaf 272905091)) (.branch 116 (.leaf 267095908) (.leaf 261414810))) (.branch 119 (.branch 118 (.leaf 255858767) (.leaf 250424829)) (.branch 120 (.leaf 245110126) (.leaf 239911864)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 424).prefactor = (11933863188181/2500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 424).cutoff/(generalMeanRows 424).c)).2 =
    (74865395776473/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 424).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 424).q*(generalMeanRows 424).c/2-2 = (3309/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable134.value]
  have hcontinuation : (generalMeanRows 424).q*(generalMeanRows 424).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable151.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 424).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 424).criticalRate j.val*(generalMeanRows 424).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 424).c*(generalMeanRows 424).criticalPoint j.val)).2-
      (generalMeanRows 424).J/2-(generalMeanRows 424).error (generalMeanGrid j.val)+
      (generalMeanRows 424).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 424).c)).2-
      (generalMeanRows 424).J/2-(generalMeanRows 424).error 4 := by
  have he : (generalMeanRows 424).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 424) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 424)
    (generalMeanRows_prefactorDomain 424) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0424

/-! Kernel-checked entropy margins for general spectral rectangle 425. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0425
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4875616412) (.branch 2 (.leaf 4703609228) (.leaf 4539420204))) (.branch 5 (.branch 4 (.leaf 4382601205) (.leaf 4232735777)) (.branch 6 (.leaf 4089436384) (.leaf 3952341942)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3821115615) (.leaf 3695442831)) (.branch 10 (.leaf 3575029501) (.leaf 3459600410))) (.branch 13 (.branch 12 (.leaf 3348897759) (.leaf 3242679847)) (.branch 14 (.leaf 3140719868) (.leaf 3042804825))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2948734527) (.branch 17 (.leaf 2858320683) (.leaf 2771386063))) (.branch 20 (.branch 19 (.leaf 2687763741) (.leaf 2607296385)) (.branch 21 (.leaf 2529835616) (.leaf 2455241412)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2383381557) (.leaf 2314131138)) (.branch 25 (.leaf 2247372074) (.leaf 2182992682))) (.branch 28 (.branch 27 (.leaf 2120887276) (.leaf 2060955794)) (.branch 29 (.leaf 2003103455) (.leaf 1947240430)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1893281548) (.branch 32 (.leaf 1841146020) (.leaf 1790757171))) (.branch 35 (.branch 34 (.leaf 1742042205) (.leaf 1694931976)) (.branch 36 (.leaf 1649360779) (.leaf 1605266150)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1562588683) (.leaf 1521271858)) (.branch 40 (.leaf 1481261878) (.leaf 1442507520))) (.branch 43 (.branch 42 (.leaf 1404959989) (.leaf 1368572789)) (.branch 44 (.leaf 1333301595) (.leaf 1299104137))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1265940092) (.branch 47 (.leaf 1233770975) (.leaf 1202560045))) (.branch 50 (.branch 49 (.leaf 1172272215) (.leaf 1142873962)) (.branch 51 (.leaf 1114333247) (.leaf 1086619441)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1059703250) (.leaf 1033556646)) (.branch 55 (.leaf 1008152809) (.leaf 983466058))) (.branch 58 (.branch 57 (.leaf 959471800) (.leaf 936146476)) (.branch 59 (.leaf 913467507) (.leaf 891413246))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 869962938) (.branch 62 (.leaf 849096670) (.leaf 828795334))) (.branch 65 (.branch 64 (.leaf 809040589) (.leaf 789814823)) (.branch 66 (.leaf 771101120) (.leaf 752883226)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 735145519) (.leaf 717872981)) (.branch 70 (.leaf 701051168) (.leaf 684666183))) (.branch 73 (.branch 72 (.leaf 668704657) (.leaf 653153718)) (.branch 74 (.leaf 638000971) (.leaf 623234481))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 608842747) (.branch 77 (.leaf 594814686) (.leaf 581139613))) (.branch 80 (.branch 79 (.leaf 567807226) (.leaf 554807587)) (.branch 81 (.leaf 542131109) (.leaf 529768538)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 517710944) (.leaf 505949700)) (.branch 85 (.leaf 494476476) (.leaf 483283223))) (.branch 88 (.branch 87 (.leaf 472362165) (.leaf 461705783)) (.branch 89 (.leaf 451306808) (.leaf 441158211)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 431253190) (.branch 92 (.leaf 421585168) (.leaf 412147774))) (.branch 95 (.branch 94 (.leaf 402934846) (.leaf 393940414)) (.branch 96 (.leaf 385158697) (.leaf 376584096)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 368211184) (.leaf 360034703)) (.branch 100 (.leaf 352049555) (.leaf 344250798))) (.branch 103 (.branch 102 (.leaf 336633640) (.leaf 329193432)) (.branch 104 (.leaf 321925662) (.leaf 314825956))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 307890066) (.leaf 301113867)) (.branch 108 (.leaf 294493358) (.leaf 288024651))) (.branch 111 (.branch 110 (.leaf 281703969) (.leaf 275527644)) (.branch 112 (.leaf 269492114) (.leaf 263593913)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 257829677) (.leaf 252196133)) (.branch 116 (.leaf 246690099) (.leaf 241308481))) (.branch 119 (.branch 118 (.leaf 236048271) (.leaf 230906542)) (.branch 120 (.leaf 225880445) (.leaf 220967212)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 425).prefactor = (1197521708827301/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 425).cutoff/(generalMeanRows 425).c)).2 =
    (73350237014781/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 425).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 425).q*(generalMeanRows 425).c/2-2 = (679/800:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable164.value]
  have hcontinuation : (generalMeanRows 425).q*(generalMeanRows 425).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable151.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 425).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 425).criticalRate j.val*(generalMeanRows 425).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 425).c*(generalMeanRows 425).criticalPoint j.val)).2-
      (generalMeanRows 425).J/2-(generalMeanRows 425).error (generalMeanGrid j.val)+
      (generalMeanRows 425).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 425).c)).2-
      (generalMeanRows 425).J/2-(generalMeanRows 425).error 4 := by
  have he : (generalMeanRows 425).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 425) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 425)
    (generalMeanRows_prefactorDomain 425) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0425

/-! Kernel-checked entropy margins for general spectral rectangle 426. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0426
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5287756796) (.branch 2 (.leaf 5118827692) (.leaf 4957416142))) (.branch 5 (.branch 4 (.leaf 4803086089) (.leaf 4655432630)) (.branch 6 (.leaf 4514079296) (.leaf 4378675620)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4248894963) (.leaf 4124432563)) (.branch 10 (.leaf 4005003771) (.leaf 3890342465))) (.branch 13 (.branch 12 (.leaf 3780199614) (.leaf 3674341974)) (.branch 14 (.leaf 3572550905) (.leaf 3474621290))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3380360553) (.branch 17 (.leaf 3289587759) (.leaf 3202132792))) (.branch 20 (.branch 19 (.leaf 3117835598) (.leaf 3036545495)) (.branch 21 (.leaf 2958120532) (.leaf 2882426902)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2809338404) (.leaf 2738735940)) (.branch 25 (.leaf 2670507054) (.leaf 2604545505))) (.branch 28 (.branch 27 (.leaf 2540750869) (.leaf 2479028173)) (.branch 29 (.leaf 2419287557) (.leaf 2361443952)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2305416790) (.branch 32 (.leaf 2251129727) (.leaf 2198510391))) (.branch 35 (.branch 34 (.leaf 2147490140) (.leaf 2098003847)) (.branch 36 (.leaf 2049989686) (.leaf 2003388942)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1958145830) (.leaf 1914207328)) (.branch 40 (.leaf 1871523016) (.leaf 1830044929))) (.branch 43 (.branch 42 (.leaf 1789727420) (.leaf 1750527027)) (.branch 44 (.leaf 1712402355) (.leaf 1675313960))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1639224240) (.branch 47 (.leaf 1604097339) (.leaf 1569899047))) (.branch 50 (.branch 49 (.leaf 1536596716) (.leaf 1504159173)) (.branch 51 (.leaf 1472556643) (.leaf 1441760676)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1411744075) (.leaf 1382480832)) (.branch 55 (.leaf 1353946067) (.leaf 1326115968))) (.branch 58 (.branch 57 (.leaf 1298967739) (.leaf 1272479544)) (.branch 59 (.leaf 1246630463) (.leaf 1221400443))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1196770256) (.branch 62 (.leaf 1172721457) (.leaf 1149236346))) (.branch 65 (.branch 64 (.leaf 1126297931) (.leaf 1103889896)) (.branch 66 (.leaf 1081996563) (.leaf 1060602866)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1039694321) (.leaf 1019256996)) (.branch 70 (.leaf 999277487) (.leaf 979742893))) (.branch 73 (.branch 72 (.leaf 960640792) (.leaf 941959219)) (.branch 74 (.leaf 923686647) (.leaf 905811962))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 888324450) (.branch 77 (.leaf 871213776) (.leaf 854469968))) (.branch 80 (.branch 79 (.leaf 838083399) (.leaf 822044774)) (.branch 81 (.leaf 806345116) (.leaf 790975751)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 775928292) (.leaf 761194634)) (.branch 85 (.leaf 746766935) (.leaf 732637609))) (.branch 88 (.branch 87 (.leaf 718799313) (.leaf 705244938)) (.branch 89 (.leaf 691967602) (.leaf 678960634)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 666217573) (.branch 92 (.leaf 653732155) (.leaf 641498305))) (.branch 95 (.branch 94 (.leaf 629510133) (.leaf 617761924)) (.branch 96 (.leaf 606248130) (.leaf 594963370)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 583902413) (.leaf 573060184)) (.branch 100 (.leaf 562431749) (.leaf 552012315))) (.branch 103 (.branch 102 (.leaf 541797222) (.leaf 531781941)) (.branch 104 (.leaf 521962065) (.leaf 512333310))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 502891506) (.leaf 493632595)) (.branch 108 (.leaf 484552627) (.leaf 475647757))) (.branch 111 (.branch 110 (.leaf 466914239) (.leaf 458348425)) (.branch 112 (.leaf 449946761) (.leaf 441705784)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 433622119) (.leaf 425692474)) (.branch 116 (.leaf 417913641) (.leaf 410282490))) (.branch 119 (.branch 118 (.leaf 402795971) (.leaf 395451104)) (.branch 120 (.leaf 388244985) (.leaf 381174778)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 426).prefactor = (4684908428220809/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 426).cutoff/(generalMeanRows 426).c)).2 =
    (106799093155119/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 426).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 426).q*(generalMeanRows 426).c/2-2 = (227/320:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable159.value]
  have hcontinuation : (generalMeanRows 426).q*(generalMeanRows 426).cutoff/2-2 = (3314/1539:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable165.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 426).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 426).criticalRate j.val*(generalMeanRows 426).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 426).c*(generalMeanRows 426).criticalPoint j.val)).2-
      (generalMeanRows 426).J/2-(generalMeanRows 426).error (generalMeanGrid j.val)+
      (generalMeanRows 426).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 426).c)).2-
      (generalMeanRows 426).J/2-(generalMeanRows 426).error 4 := by
  have he : (generalMeanRows 426).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 426) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 426)
    (generalMeanRows_prefactorDomain 426) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0426

/-! Kernel-checked entropy margins for general spectral rectangle 427. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0427
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4950790205) (.branch 2 (.leaf 4778528166) (.leaf 4614057164))) (.branch 5 (.branch 4 (.leaf 4456930919) (.leaf 4306734706)) (.branch 6 (.leaf 4163082605) (.leaf 4025615042)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3893996592) (.leaf 3767914007)) (.branch 10 (.leaf 3647074436) (.leaf 3531203828))) (.branch 13 (.branch 12 (.leaf 3420045474) (.leaf 3313358699)) (.branch 14 (.leaf 3210917662) (.leaf 3112510273))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3017937196) (.branch 17 (.leaf 2927010944) (.leaf 2839555050))) (.branch 20 (.branch 19 (.leaf 2755403302) (.leaf 2674399047)) (.branch 21 (.leaf 2596394546) (.leaf 2521250381)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2448834910) (.leaf 2379023760)) (.branch 25 (.leaf 2311699363) (.leaf 2246750524))) (.branch 28 (.branch 27 (.leaf 2184072017) (.leaf 2123564218)) (.branch 29 (.leaf 2065132759) (.leaf 2008688206)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1954145762) (.branch 32 (.leaf 1901424991) (.leaf 1850449557))) (.branch 35 (.branch 34 (.leaf 1801146984) (.leaf 1753448431)) (.branch 36 (.leaf 1707288481) (.leaf 1662604946)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1619338683) (.leaf 1577433419)) (.branch 40 (.leaf 1536835596) (.leaf 1497494214))) (.branch 43 (.branch 42 (.leaf 1459360693) (.leaf 1422388741)) (.branch 44 (.leaf 1386534227) (.leaf 1351755066))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1318011107) (.branch 47 (.leaf 1285264035) (.leaf 1253477265))) (.branch 50 (.branch 49 (.leaf 1222615861) (.leaf 1192646443)) (.branch 51 (.leaf 1163537108) (.leaf 1135257354)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1107778010) (.leaf 1081071164)) (.branch 55 (.leaf 1055110103) (.leaf 1029869253))) (.branch 58 (.branch 57 (.leaf 1005324117) (.leaf 981451229)) (.branch 59 (.leaf 958228098) (.leaf 935633159))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 913645735) (.branch 62 (.leaf 892245985) (.leaf 871414872))) (.branch 65 (.branch 64 (.leaf 851134118) (.leaf 831386171)) (.branch 66 (.leaf 812154172) (.leaf 793421921)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 775173843) (.leaf 757394967)) (.branch 70 (.leaf 740070890) (.leaf 723187755))) (.branch 73 (.branch 72 (.leaf 706732228) (.leaf 690691470)) (.branch 74 (.leaf 675053117) (.leaf 659805260))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 644936422) (.branch 77 (.leaf 630435542) (.leaf 616291955))) (.branch 80 (.branch 79 (.leaf 602495376) (.leaf 589035881)) (.branch 81 (.leaf 575903896) (.leaf 563090177)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 550585800) (.leaf 538382148)) (.branch 85 (.leaf 526470892) (.leaf 514843988))) (.branch 88 (.branch 87 (.leaf 503493659) (.leaf 492412384)) (.branch 89 (.leaf 481592894) (.leaf 471028153)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 460711356) (.branch 92 (.leaf 450635916) (.leaf 440795455))) (.branch 95 (.branch 94 (.leaf 431183800) (.leaf 421794970)) (.branch 96 (.leaf 412623173) (.leaf 403662794)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 394908392) (.leaf 386354693)) (.branch 100 (.leaf 377996584) (.leaf 369829102))) (.branch 103 (.branch 102 (.leaf 361847438) (.leaf 354046922)) (.branch 104 (.leaf 346423023) (.leaf 338971344))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 331687615) (.leaf 324567690)) (.branch 108 (.leaf 317607541) (.leaf 310803256))) (.branch 111 (.branch 110 (.leaf 304151036) (.leaf 297647185)) (.branch 112 (.leaf 291288115) (.leaf 285070334)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 278990449) (.leaf 273045161)) (.branch 116 (.leaf 267231259) (.leaf 261545621))) (.branch 119 (.branch 118 (.leaf 255985210) (.leaf 250547068)) (.branch 120 (.leaf 245228318) (.leaf 240026161)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 427).prefactor = (2387373473241211/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 427).cutoff/(generalMeanRows 427).c)).2 =
    (372866058242689/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 427).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 427).q*(generalMeanRows 427).c/2-2 = (3309/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable134.value]
  have hcontinuation : (generalMeanRows 427).q*(generalMeanRows 427).cutoff/2-2 = (33162/15755:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable166.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 427).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 427).criticalRate j.val*(generalMeanRows 427).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 427).c*(generalMeanRows 427).criticalPoint j.val)).2-
      (generalMeanRows 427).J/2-(generalMeanRows 427).error (generalMeanGrid j.val)+
      (generalMeanRows 427).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 427).c)).2-
      (generalMeanRows 427).J/2-(generalMeanRows 427).error 4 := by
  have he : (generalMeanRows 427).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 427) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 427)
    (generalMeanRows_prefactorDomain 427) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0427

/-! Kernel-checked entropy margins for general spectral rectangle 428. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0428
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4877248733) (.branch 2 (.leaf 4705215895) (.leaf 4540994902))) (.branch 5 (.branch 4 (.leaf 4384138498) (.leaf 4234231023)) (.branch 6 (.leaf 4090885660) (.leaf 3953741973)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3822463709) (.leaf 3696736825)) (.branch 10 (.leaf 3576267703) (.leaf 3460781552))) (.branch 13 (.branch 12 (.leaf 3350020954) (.leaf 3243744546)) (.branch 14 (.leaf 3141725827) (.leaf 3043752066))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2949623312) (.branch 17 (.leaf 2859151482) (.leaf 2772159532))) (.branch 20 (.branch 19 (.leaf 2688480696) (.leaf 2607957784)) (.branch 21 (.leaf 2530442537) (.leaf 2455795037)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2383883155) (.leaf 2314582051)) (.branch 25 (.leaf 2247773706) (.leaf 2183346484))) (.branch 28 (.branch 27 (.leaf 2121194739) (.leaf 2061218437)) (.branch 29 (.leaf 2003322817) (.leaf 1947418062)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1893419009) (.branch 32 (.leaf 1841244866) (.leaf 1790818952))) (.branch 35 (.branch 34 (.leaf 1742068463) (.leaf 1694924236)) (.branch 36 (.leaf 1649320548) (.leaf 1605194912)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1562487898) (.leaf 1521142959)) (.branch 40 (.leaf 1481106269) (.leaf 1442326572))) (.branch 43 (.branch 42 (.leaf 1404755043) (.leaf 1368345150)) (.branch 44 (.leaf 1333052535) (.leaf 1298834892))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1265651861) (.branch 47 (.leaf 1233464922) (.leaf 1202237296))) (.branch 50 (.branch 49 (.leaf 1171933860) (.leaf 1142521055)) (.branch 51 (.leaf 1113966805) (.leaf 1086240444)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1059312642) (.leaf 1033155337)) (.branch 55 (.leaf 1007741673) (.leaf 983045935))) (.branch 58 (.branch 57 (.leaf 959043496) (.leaf 935710764)) (.branch 59 (.leaf 913025127) (.leaf 890964908))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 869509319) (.branch 62 (.leaf 848638417) (.leaf 828333066))) (.branch 65 (.branch 64 (.leaf 808574896) (.leaf 789346266)) (.branch 66 (.leaf 770630234) (.leaf 752410520)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 734671477) (.leaf 717398061)) (.branch 70 (.leaf 700575804) (.leaf 684190789))) (.branch 73 (.branch 72 (.leaf 668229622) (.leaf 652679409)) (.branch 74 (.leaf 637527738) (.leaf 622762650))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 608372628) (.branch 77 (.leaf 594346569) (.leaf 580673770))) (.branch 80 (.branch 79 (.leaf 567343913) (.leaf 554347044)) (.branch 81 (.leaf 541673558) (.leaf 529314190)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 517259991) (.leaf 505502323)) (.branch 85 (.leaf 494032842) (.leaf 482843488))) (.branch 88 (.branch 87 (.leaf 471926469) (.leaf 461274258)) (.branch 89 (.leaf 450879574) (.leaf 440735377)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 430834856) (.branch 92 (.leaf 421171423) (.leaf 411738699))) (.branch 95 (.branch 94 (.leaf 402530513) (.leaf 393540886)) (.branch 96 (.leaf 384764031) (.leaf 376194340)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 367826379) (.leaf 359654884)) (.branch 100 (.leaf 351674751) (.leaf 343881032))) (.branch 103 (.branch 102 (.leaf 336268928) (.leaf 328833785)) (.branch 104 (.leaf 321571088) (.leaf 314476455))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 307545635) (.leaf 300774500)) (.branch 108 (.leaf 294159043) (.leaf 287695373))) (.branch 111 (.branch 110 (.leaf 281379710) (.leaf 275208384)) (.branch 112 (.leaf 269177826) (.leaf 263284571)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 257525250) (.leaf 251896588)) (.branch 116 (.leaf 246395402) (.leaf 241018594))) (.branch 119 (.branch 118 (.leaf 235763155) (.leaf 230626156)) (.branch 120 (.leaf 225604747) (.leaf 220696157)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 428).prefactor = (239152319790583/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 428).cutoff/(generalMeanRows 428).c)).2 =
    (365290264434231/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 428).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 428).q*(generalMeanRows 428).c/2-2 = (679/800:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable164.value]
  have hcontinuation : (generalMeanRows 428).q*(generalMeanRows 428).cutoff/2-2 = (33162/15755:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable166.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 428).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 428).criticalRate j.val*(generalMeanRows 428).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 428).c*(generalMeanRows 428).criticalPoint j.val)).2-
      (generalMeanRows 428).J/2-(generalMeanRows 428).error (generalMeanGrid j.val)+
      (generalMeanRows 428).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 428).c)).2-
      (generalMeanRows 428).J/2-(generalMeanRows 428).error 4 := by
  have he : (generalMeanRows 428).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 428) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 428)
    (generalMeanRows_prefactorDomain 428) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0428

/-! Kernel-checked entropy margins for general spectral rectangle 429. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0429
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4887331643) (.branch 2 (.leaf 4714976340) (.leaf 4550440014))) (.branch 5 (.branch 4 (.leaf 4393275517) (.leaf 4243067267)) (.branch 6 (.leaf 4099428497) (.leaf 3961998799)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3830441927) (.leaf 3704443819)) (.branch 10 (.leaf 3583710828) (.leaf 3467968113))) (.branch 13 (.branch 12 (.leaf 3356958192) (.leaf 3250439628)) (.branch 14 (.leaf 3148185831) (.leaf 3049983974))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2955634001) (.branch 17 (.leaf 2864947714) (.leaf 2777747951))) (.branch 20 (.branch 19 (.leaf 2693867821) (.leaf 2613150003)) (.branch 21 (.leaf 2535446104) (.leaf 2460616070)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2388527634) (.leaf 2319055815)) (.branch 25 (.leaf 2252082450) (.leaf 2187495762))) (.branch 28 (.branch 27 (.leaf 2125189961) (.leaf 2065064872)) (.branch 29 (.leaf 2007025588) (.leaf 1950982155)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1896849266) (.branch 32 (.leaf 1844545990) (.leaf 1793995512))) (.branch 35 (.branch 34 (.leaf 1745124889) (.leaf 1697864826)) (.branch 36 (.leaf 1652149467) (.leaf 1607916198)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1565105461) (.leaf 1523660585)) (.branch 40 (.leaf 1483527621) (.leaf 1444655197))) (.branch 43 (.branch 42 (.leaf 1406994368) (.leaf 1370498492)) (.branch 44 (.leaf 1335123096) (.leaf 1300825770))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1267566045) (.branch 47 (.leaf 1235305300) (.leaf 1204006657))) (.branch 50 (.branch 49 (.leaf 1173634895) (.leaf 1144156359)) (.branch 51 (.leaf 1115538883) (.leaf 1087751713)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1060765432) (.leaf 1034551893)) (.branch 55 (.leaf 1009084159) (.leaf 984336437))) (.branch 58 (.branch 57 (.leaf 960284025) (.leaf 936903254)) (.branch 59 (.leaf 914171444) (.leaf 892066846))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 870568607) (.branch 62 (.leaf 849656719) (.leaf 829311983))) (.branch 65 (.branch 64 (.leaf 809515969) (.leaf 790250979)) (.branch 66 (.leaf 771500012) (.leaf 753246736)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 735475450) (.leaf 718171060)) (.branch 70 (.leaf 701319051) (.leaf 684905455))) (.branch 73 (.branch 72 (.leaf 668916836) (.leaf 653340256)) (.branch 74 (.leaf 638163259) (.leaf 623373847))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 608960463) (.branch 77 (.leaf 594911966) (.leaf 581217619))) (.branch 80 (.branch 79 (.leaf 567867066) (.leaf 554850321)) (.branch 81 (.leaf 542157748) (.leaf 529780047)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 517708242) (.leaf 505933666)) (.branch 85 (.leaf 494447947) (.leaf 483242997))) (.branch 88 (.branch 87 (.leaf 472311001) (.leaf 461644405)) (.branch 89 (.leaf 451235905) (.leaf 441078438)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 431165172) (.branch 92 (.leaf 421489497) (.leaf 412045015))) (.branch 95 (.branch 94 (.leaf 402825534) (.leaf 393825059)) (.branch 96 (.leaf 385037781) (.leaf 376458078)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 368080499) (.leaf 359899763)) (.branch 100 (.leaf 351910751) (.leaf 344108501))) (.branch 103 (.branch 102 (.leaf 336488200) (.leaf 329045180)) (.branch 104 (.leaf 321774913) (.leaf 314673006))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 307735194) (.leaf 300957340)) (.branch 108 (.leaf 294335423) (.leaf 287865544))) (.branch 111 (.branch 110 (.leaf 281543911) (.leaf 275366845)) (.branch 112 (.leaf 269330769) (.leaf 263432207)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 257667783) (.leaf 252034214)) (.branch 116 (.leaf 246528307) (.leaf 241146958))) (.branch 119 (.branch 118 (.leaf 235887151) (.leaf 230745949)) (.branch 120 (.leaf 225720497) (.leaf 220808016)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 429).prefactor = (956856468625323/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 429).cutoff/(generalMeanRows 429).c)).2 =
    (363831474970569/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 429).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 429).q*(generalMeanRows 429).c/2-2 = (679/800:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable164.value]
  have hcontinuation : (generalMeanRows 429).q*(generalMeanRows 429).cutoff/2-2 = (16558/7889:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable155.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 429).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 429).criticalRate j.val*(generalMeanRows 429).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 429).c*(generalMeanRows 429).criticalPoint j.val)).2-
      (generalMeanRows 429).J/2-(generalMeanRows 429).error (generalMeanGrid j.val)+
      (generalMeanRows 429).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 429).c)).2-
      (generalMeanRows 429).J/2-(generalMeanRows 429).error 4 := by
  have he : (generalMeanRows 429).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 429) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 429)
    (generalMeanRows_prefactorDomain 429) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0429

/-! Kernel-checked entropy margins for general spectral rectangle 430. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0430
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5271810749) (.branch 2 (.leaf 5103382947) (.leaf 4942436662))) (.branch 5 (.branch 4 (.leaf 4788538961) (.leaf 4641287801)) (.branch 6 (.leaf 4500309324) (.leaf 4365255452)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4235801732) (.leaf 4111645399)) (.branch 10 (.leaf 3992503631) (.leaf 3878111979))) (.branch 13 (.branch 12 (.leaf 3768222939) (.leaf 3662604664)) (.branch 14 (.leaf 3561039791) (.leaf 3463324369))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3369266889) (.branch 17 (.leaf 3278687390) (.leaf 3191416644))) (.branch 20 (.branch 19 (.leaf 3107295409) (.leaf 3026173740)) (.branch 21 (.leaf 2947910362) (.leaf 2872372082)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2799433257) (.leaf 2728975298)) (.branch 25 (.leaf 2660886210) (.leaf 2595060173))) (.branch 28 (.branch 27 (.leaf 2531397143) (.leaf 2469802493)) (.branch 29 (.leaf 2410186674) (.leaf 2352464901)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2296556860) (.branch 32 (.leaf 2242386438) (.leaf 2189881470))) (.branch 35 (.branch 34 (.leaf 2138973502) (.leaf 2089597573)) (.branch 36 (.leaf 2041692008) (.leaf 1995198225)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1950060561) (.leaf 1906226100)) (.branch 40 (.leaf 1863644515) (.leaf 1822267926))) (.branch 43 (.branch 42 (.leaf 1782050761) (.leaf 1742949622)) (.branch 44 (.leaf 1704923172) (.leaf 1667932016))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1631938596) (.branch 47 (.leaf 1596907092) (.leaf 1562803328))) (.branch 50 (.branch 49 (.leaf 1529594682) (.leaf 1497250005)) (.branch 51 (.leaf 1465739540) (.leaf 1435034852)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1405108759) (.leaf 1375935263)) (.branch 55 (.leaf 1347489490) (.leaf 1319747635))) (.branch 58 (.branch 57 (.leaf 1292686906) (.leaf 1266285469)) (.branch 59 (.leaf 1240522405) (.leaf 1215377662))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1190832010) (.branch 62 (.leaf 1166867003) (.leaf 1143464938))) (.branch 65 (.branch 64 (.leaf 1120608821) (.leaf 1098282331)) (.branch 66 (.leaf 1076469788) (.leaf 1055156122)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1034326844) (.leaf 1013968019)) (.branch 70 (.leaf 994066239) (.leaf 974608599))) (.branch 73 (.branch 72 (.leaf 955582673) (.leaf 936976494)) (.branch 74 (.leaf 918778528) (.leaf 900977662))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 883563177) (.branch 77 (.leaf 866524736) (.leaf 849852365))) (.branch 80 (.branch 79 (.leaf 833536434) (.leaf 817567648)) (.branch 81 (.leaf 801937027) (.leaf 786635897)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 771655871) (.leaf 756988843)) (.branch 85 (.leaf 742626972) (.leaf 728562671))) (.branch 88 (.branch 87 (.leaf 714788599) (.leaf 701297650)) (.branch 89 (.leaf 688082939) (.leaf 675137802)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 662455776) (.branch 92 (.leaf 650030601) (.leaf 637856206))) (.branch 95 (.branch 94 (.leaf 625926704) (.leaf 614236381)) (.branch 96 (.leaf 602779696) (.leaf 591551269)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 580545876) (.leaf 569758445)) (.branch 100 (.leaf 559184046) (.leaf 548817892))) (.branch 103 (.branch 102 (.leaf 538655328) (.leaf 528691830)) (.branch 104 (.leaf 518922997) (.leaf 509344550))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 499952326) (.leaf 490742272)) (.branch 108 (.leaf 481710445) (.leaf 472853005))) (.branch 111 (.branch 110 (.leaf 464166214) (.leaf 455646430)) (.branch 112 (.leaf 447290106) (.leaf 439093786)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 431054100) (.leaf 423167765)) (.branch 116 (.leaf 415431579) (.leaf 407842420))) (.branch 119 (.branch 118 (.leaf 400397243) (.leaf 393093079)) (.branch 120 (.leaf 385927028) (.leaf 378896263)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 430).prefactor = (4655765056926483/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 430).cutoff/(generalMeanRows 430).c)).2 =
    (212138331258571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 430).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 430).q*(generalMeanRows 430).c/2-2 = (227/320:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable159.value]
  have hcontinuation : (generalMeanRows 430).q*(generalMeanRows 430).cutoff/2-2 = (6610/3087:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable161.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 430).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 430).criticalRate j.val*(generalMeanRows 430).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 430).c*(generalMeanRows 430).criticalPoint j.val)).2-
      (generalMeanRows 430).J/2-(generalMeanRows 430).error (generalMeanGrid j.val)+
      (generalMeanRows 430).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 430).c)).2-
      (generalMeanRows 430).J/2-(generalMeanRows 430).error 4 := by
  have he : (generalMeanRows 430).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 430) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 430)
    (generalMeanRows_prefactorDomain 430) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0430

/-! Kernel-checked entropy margins for general spectral rectangle 431. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0431
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5262145477) (.branch 2 (.leaf 5094029930) (.leaf 4933388891))) (.branch 5 (.branch 4 (.leaf 4779789317) (.leaf 4632829082)) (.branch 6 (.leaf 4492134277) (.leaf 4357356797)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4228172182) (.leaf 4104277684)) (.branch 10 (.leaf 3985390514) (.leaf 3871246273))) (.branch 13 (.branch 12 (.leaf 3761597523) (.leaf 3656212494)) (.branch 14 (.leaf 3554873911) (.leaf 3457377924))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3363533131) (.branch 17 (.leaf 3273159686) (.leaf 3186088483))) (.branch 20 (.branch 19 (.leaf 3102160407) (.leaf 3021225645)) (.branch 21 (.leaf 2943143056) (.leaf 2867779586)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2795009733) (.leaf 2724715049)) (.branch 25 (.leaf 2656783684) (.leaf 2591109958))) (.branch 28 (.branch 27 (.leaf 2527593974) (.leaf 2466141247)) (.branch 29 (.leaf 2406662372) (.leaf 2349072703)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2293292069) (.branch 32 (.leaf 2239244495) (.leaf 2186857954))) (.branch 35 (.branch 34 (.leaf 2136064125) (.leaf 2086798181)) (.branch 36 (.leaf 2038998577) (.leaf 1992606861)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1947567495) (.leaf 1903827684)) (.branch 40 (.leaf 1861337225) (.leaf 1820048353))) (.branch 43 (.branch 42 (.leaf 1779915611) (.leaf 1740895715)) (.branch 44 (.leaf 1702947435) (.leaf 1666031484))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1630110408) (.branch 47 (.leaf 1595148486) (.leaf 1561111640))) (.branch 50 (.branch 49 (.leaf 1527967344) (.leaf 1495684541)) (.branch 51 (.leaf 1464233564) (.leaf 1433586065)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1403714945) (.leaf 1374594288)) (.branch 55 (.leaf 1346199300) (.leaf 1318506251))) (.branch 58 (.branch 57 (.leaf 1291492424) (.leaf 1265136056)) (.branch 59 (.leaf 1239416299) (.leaf 1214313165))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1189807489) (.branch 62 (.leaf 1165880889) (.leaf 1142515722))) (.branch 65 (.branch 64 (.leaf 1119695051) (.leaf 1097402612)) (.branch 66 (.leaf 1075622778) (.leaf 1054340532)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1033541436) (.leaf 1013211602)) (.branch 70 (.leaf 993337669) (.leaf 973906778))) (.branch 73 (.branch 72 (.leaf 954906546) (.leaf 936325046)) (.branch 74 (.leaf 918150787) (.leaf 900372692))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 882980080) (.branch 77 (.leaf 865962651) (.leaf 849310463))) (.branch 80 (.branch 79 (.leaf 833013922) (.leaf 817063763)) (.branch 81 (.leaf 801451038) (.leaf 786167101)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 771203594) (.leaf 756552437)) (.branch 85 (.leaf 742205816) (.leaf 728156170))) (.branch 88 (.branch 87 (.leaf 714396181) (.leaf 700918765)) (.branch 89 (.leaf 687717063) (.leaf 674784428)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 662114420) (.branch 92 (.leaf 649700799) (.leaf 637537511))) (.branch 95 (.branch 94 (.leaf 625618687) (.leaf 613938633)) (.branch 96 (.leaf 602491823) (.leaf 591272893)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 580276635) (.leaf 569497990)) (.branch 100 (.leaf 558932044) (.leaf 548574023))) (.branch 103 (.branch 102 (.leaf 538419285) (.leaf 528463318)) (.branch 104 (.leaf 518701734) (.leaf 509130265))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 499744758) (.leaf 490541172)) (.branch 108 (.leaf 481515573) (.leaf 472664132))) (.branch 111 (.branch 110 (.leaf 463983119) (.leaf 455468902)) (.branch 112 (.leaf 447117941) (.leaf 438926789)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 430892085) (.leaf 423010552)) (.branch 116 (.leaf 415278995) (.leaf 407694301))) (.branch 119 (.branch 118 (.leaf 400253430) (.leaf 392953418)) (.branch 120 (.leaf 385791374) (.leaf 378764475)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 431).prefactor = (4654720645481781/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 431).cutoff/(generalMeanRows 431).c)).2 =
    (212867725990401/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 431).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 431).q*(generalMeanRows 431).c/2-2 = (227/320:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable159.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 431).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 431).criticalRate j.val*(generalMeanRows 431).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 431).c*(generalMeanRows 431).criticalPoint j.val)).2-
      (generalMeanRows 431).J/2-(generalMeanRows 431).error (generalMeanGrid j.val)+
      (generalMeanRows 431).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 431).c)).2-
      (generalMeanRows 431).J/2-(generalMeanRows 431).error 4 := by
  have he : (generalMeanRows 431).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 431) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 431)
    (generalMeanRows_prefactorDomain 431) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0431

/-! Kernel-checked entropy margins for general spectral rectangle 432. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0432
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4894218704) (.branch 2 (.leaf 4721587293) (.leaf 4556794907))) (.branch 5 (.branch 4 (.leaf 4399392734) (.leaf 4248963669)) (.branch 6 (.leaf 4105119548) (.leaf 3967498681)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3835763646) (.leaf 3709599305)) (.branch 10 (.leaf 3588711021) (.leaf 3472823046))) (.branch 13 (.branch 12 (.leaf 3361677066) (.leaf 3255030879)) (.branch 14 (.leaf 3152657194) (.leaf 3054342542))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2959886275) (.branch 17 (.leaf 2869099655) (.leaf 2781805025))) (.branch 20 (.branch 19 (.leaf 2697835036) (.leaf 2617031951)) (.branch 21 (.leaf 2539246996) (.leaf 2464339766)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2392177673) (.leaf 2322635442)) (.branch 25 (.leaf 2255594642) (.leaf 2190943252))) (.branch 28 (.branch 27 (.leaf 2128575255) (.leaf 2068390271)) (.branch 29 (.leaf 2010293208) (.leaf 1954193937)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1900006999) (.branch 32 (.leaf 1847651320) (.leaf 1797049954))) (.branch 35 (.branch 34 (.leaf 1748129841) (.leaf 1700821580)) (.branch 36 (.leaf 1655059218) (.leaf 1610780050)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1567924441) (.leaf 1526435646)) (.branch 40 (.leaf 1486259652) (.leaf 1447345024))) (.branch 43 (.branch 42 (.leaf 1409642768) (.leaf 1373106190)) (.branch 44 (.leaf 1337690777) (.leaf 1303354077))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1270055589) (.branch 47 (.leaf 1237756657) (.leaf 1206420378))) (.branch 50 (.branch 49 (.leaf 1176011504) (.leaf 1146496359)) (.branch 51 (.leaf 1117842757) (.leaf 1090019925)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1062998430) (.leaf 1036750113)) (.branch 55 (.leaf 1011248024) (.leaf 986466359))) (.branch 58 (.branch 57 (.leaf 962380406) (.leaf 938966490)) (.branch 59 (.leaf 916201920) (.leaf 894064944))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 872534702) (.branch 62 (.leaf 851591182) (.leaf 831215181))) (.branch 65 (.branch 64 (.leaf 811388263) (.leaf 792092729)) (.branch 66 (.leaf 773311577) (.leaf 755028469)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 737227704) (.leaf 719894186)) (.branch 70 (.leaf 703013398) (.leaf 686571373))) (.branch 73 (.branch 72 (.leaf 670554670) (.leaf 654950351)) (.branch 74 (.leaf 639745961) (.leaf 624929500))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 610489409) (.branch 77 (.leaf 596414547) (.leaf 582694175))) (.branch 80 (.branch 79 (.leaf 569317938) (.leaf 556275847)) (.branch 81 (.leaf 543558265) (.leaf 531155893)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 519059753) (.leaf 507261175)) (.branch 85 (.leaf 495751787) (.leaf 484523500))) (.branch 88 (.branch 87 (.leaf 473568497) (.leaf 462879223)) (.branch 89 (.leaf 452448371) (.leaf 442268878)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 432333909) (.branch 92 (.leaf 422636853) (.leaf 413171309))) (.branch 95 (.branch 94 (.leaf 403931083) (.leaf 394910178)) (.branch 96 (.leaf 386102785) (.leaf 377503276)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 369106200) (.leaf 360906273)) (.branch 100 (.leaf 352898374) (.leaf 345077537))) (.branch 103 (.branch 102 (.leaf 337438947) (.leaf 329977934)) (.branch 104 (.leaf 322689967) (.leaf 315570649))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 308615714) (.leaf 301821019)) (.branch 108 (.leaf 295182545) (.leaf 288696385))) (.branch 111 (.branch 110 (.leaf 282358747) (.leaf 276165948)) (.branch 112 (.leaf 270114407) (.leaf 264200647)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 258421287) (.leaf 252773041)) (.branch 116 (.leaf 247252713) (.leaf 241857198))) (.branch 119 (.branch 118 (.leaf 236583473) (.leaf 231428600)) (.branch 120 (.leaf 226389720) (.leaf 221464051)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 432).prefactor = (4799688597771513/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 432).cutoff/(generalMeanRows 432).c)).2 =
    (365290264434231/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 432).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 432).q*(generalMeanRows 432).c/2-2 = (679/800:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable164.value]
  have hcontinuation : (generalMeanRows 432).q*(generalMeanRows 432).cutoff/2-2 = (33162/15755:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable166.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 432).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 432).criticalRate j.val*(generalMeanRows 432).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 432).c*(generalMeanRows 432).criticalPoint j.val)).2-
      (generalMeanRows 432).J/2-(generalMeanRows 432).error (generalMeanGrid j.val)+
      (generalMeanRows 432).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 432).c)).2-
      (generalMeanRows 432).J/2-(generalMeanRows 432).error 4 := by
  have he : (generalMeanRows 432).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 432) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 432)
    (generalMeanRows_prefactorDomain 432) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0432

/-! Kernel-checked entropy margins for general spectral rectangle 433. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0433
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5280705626) (.branch 2 (.leaf 5111993644) (.leaf 4950775801))) (.branch 5 (.branch 4 (.leaf 4796618437) (.leaf 4649118827)) (.branch 6 (.leaf 4507902483) (.leaf 4372620741)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4242948600) (.leaf 4118582784)) (.branch 10 (.leaf 3999239994) (.leaf 3884655334))) (.branch 13 (.branch 12 (.leaf 3774580883) (.leaf 3668784404)) (.branch 14 (.leaf 3567048165) (.leaf 3469167872))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3374951694) (.branch 17 (.leaf 3284219364) (.leaf 3196801370))) (.branch 20 (.branch 19 (.leaf 3112538201) (.leaf 3031279660)) (.branch 21 (.leaf 2952884232) (.leaf 2877218499)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2804156608) (.leaf 2733579769)) (.branch 25 (.leaf 2665375798) (.leaf 2599438695))) (.branch 28 (.branch 27 (.leaf 2535668249) (.leaf 2473969674)) (.branch 29 (.leaf 2414253268) (.leaf 2356434103)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2300431731) (.branch 32 (.leaf 2246169910) (.leaf 2193576353))) (.branch 35 (.branch 34 (.leaf 2142582491) (.leaf 2093123253)) (.branch 36 (.leaf 2045136858) (.leaf 1998564629)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1953350806) (.leaf 1909442385)) (.branch 40 (.leaf 1866788954) (.leaf 1825342553))) (.branch 43 (.branch 42 (.leaf 1785057531) (.leaf 1745890418)) (.branch 44 (.leaf 1707799808) (.leaf 1670746238))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1634692089) (.branch 47 (.leaf 1599601478) (.leaf 1565440172))) (.branch 50 (.branch 49 (.leaf 1532175495) (.leaf 1499776244)) (.branch 51 (.leaf 1468212613) (.leaf 1437456119)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1407479533) (.leaf 1378256813)) (.branch 55 (.leaf 1349763045) (.leaf 1321974383))) (.branch 58 (.branch 57 (.leaf 1294867995) (.leaf 1268422013)) (.branch 59 (.leaf 1242615480) (.leaf 1217428312))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1192841245) (.branch 62 (.leaf 1168835802) (.leaf 1145394252))) (.branch 65 (.branch 64 (.leaf 1122499571) (.leaf 1100135411)) (.branch 66 (.leaf 1078286064) (.leaf 1056936437)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1036072015) (.leaf 1015678839)) (.branch 70 (.leaf 995743480) (.leaf 976253010))) (.branch 73 (.branch 72 (.leaf 957194983) (.leaf 938557410)) (.branch 74 (.leaf 920328740) (.leaf 902497839))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 885053972) (.branch 77 (.leaf 867986783) (.leaf 851286280))) (.branch 80 (.branch 79 (.leaf 834942820) (.leaf 818947091)) (.branch 81 (.leaf 803290098) (.leaf 787963150)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 772957850) (.leaf 758266075)) (.branch 85 (.leaf 743879971) (.leaf 729791940))) (.branch 88 (.branch 87 (.leaf 715994628) (.leaf 702480916)) (.branch 89 (.leaf 689243909) (.leaf 676276930)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 663573506) (.branch 92 (.leaf 651127367) (.leaf 638932431))) (.branch 95 (.branch 94 (.leaf 626982800) (.leaf 615272753)) (.branch 96 (.leaf 603796738) (.leaf 592549366)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 581525404) (.leaf 570719771)) (.branch 100 (.leaf 560127531) (.leaf 549743886))) (.branch 103 (.branch 102 (.leaf 539564176) (.leaf 529583867)) (.branch 104 (.leaf 519798551) (.leaf 510203943))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 500795872) (.leaf 491570278)) (.branch 108 (.leaf 482523212) (.leaf 473650828))) (.branch 111 (.branch 110 (.leaf 464949380) (.leaf 456415221)) (.branch 112 (.leaf 448044798) (.leaf 439834648)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 431781397) (.leaf 423881756)) (.branch 116 (.leaf 416132517) (.leaf 408530553))) (.branch 119 (.branch 118 (.leaf 401072815) (.leaf 393756326)) (.branch 120 (.leaf 386578184) (.leaf 379535556)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 433).prefactor = (4663620509236881/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 433).cutoff/(generalMeanRows 433).c)).2 =
    (212138331258571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 433).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 433).q*(generalMeanRows 433).c/2-2 = (227/320:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable159.value]
  have hcontinuation : (generalMeanRows 433).q*(generalMeanRows 433).cutoff/2-2 = (6610/3087:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable161.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 433).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 433).criticalRate j.val*(generalMeanRows 433).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 433).c*(generalMeanRows 433).criticalPoint j.val)).2-
      (generalMeanRows 433).J/2-(generalMeanRows 433).error (generalMeanGrid j.val)+
      (generalMeanRows 433).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 433).c)).2-
      (generalMeanRows 433).J/2-(generalMeanRows 433).error 4 := by
  have he : (generalMeanRows 433).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 433) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 433)
    (generalMeanRows_prefactorDomain 433) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0433

/-! Kernel-checked entropy margins for general spectral rectangle 434. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0434
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5199271467) (.branch 2 (.leaf 5030587869) (.leaf 4869421195))) (.branch 5 (.branch 4 (.leaf 4715336995) (.leaf 4567931786)) (.branch 6 (.leaf 4426830344) (.leaf 4291683293)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4162164941) (.leaf 4037971343)) (.branch 10 (.leaf 3918818551) (.leaf 3804441036))) (.branch 13 (.branch 12 (.leaf 3694590264) (.leaf 3589033399)) (.branch 14 (.leaf 3487552128) (.leaf 3389941591))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3296009404) (.branch 17 (.leaf 3205574762) (.leaf 3118467630))) (.branch 20 (.branch 19 (.leaf 3034527985) (.leaf 2953605132)) (.branch 21 (.leaf 2875557069) (.leaf 2800249906)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2727557326) (.leaf 2657360088)) (.branch 25 (.leaf 2589545570) (.leaf 2524007343))) (.branch 28 (.branch 27 (.leaf 2460644776) (.leaf 2399362676)) (.branch 29 (.leaf 2340070944) (.leaf 2282684264)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2227121810) (.branch 32 (.leaf 2173306972) (.leaf 2121167103))) (.branch 35 (.branch 34 (.leaf 2070633284) (.leaf 2021640105)) (.branch 36 (.leaf 1974125453) (.leaf 1928030326)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1883298651) (.leaf 1839877116)) (.branch 40 (.leaf 1797715012) (.leaf 1756764089))) (.branch 43 (.branch 42 (.leaf 1716978414) (.leaf 1678314242)) (.branch 44 (.leaf 1640729899) (.leaf 1604185665))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1568643666) (.branch 47 (.leaf 1534067777) (.leaf 1500423526))) (.branch 50 (.branch 49 (.leaf 1467678004) (.leaf 1435799786)) (.branch 51 (.leaf 1404758848) (.leaf 1374526495)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1345075293) (.leaf 1316379003)) (.branch 55 (.leaf 1288412516) (.leaf 1261151801))) (.branch 58 (.branch 57 (.leaf 1234573845) (.leaf 1208656604)) (.branch 59 (.leaf 1183378954) (.leaf 1158720644))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1134662253) (.branch 62 (.leaf 1111185150) (.leaf 1088271456))) (.branch 65 (.branch 64 (.leaf 1065904004) (.leaf 1044066306)) (.branch 66 (.leaf 1022742523) (.leaf 1001917430)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 981576390) (.leaf 961705324)) (.branch 70 (.leaf 942290686) (.leaf 923319437))) (.branch 73 (.branch 72 (.leaf 904779024) (.leaf 886657356)) (.branch 74 (.leaf 868942781) (.leaf 851624071))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 834690398) (.branch 77 (.leaf 818131319) (.leaf 801936759))) (.branch 80 (.branch 79 (.leaf 786096991) (.leaf 770602628)) (.branch 81 (.leaf 755444599) (.leaf 740614145)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 726102798) (.leaf 711902372)) (.branch 85 (.leaf 698004952) (.leaf 684402879))) (.branch 88 (.branch 87 (.leaf 671088745) (.leaf 658055375)) (.branch 89 (.leaf 645295827) (.leaf 632803372)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 620571496) (.branch 92 (.leaf 608593883) (.leaf 596864411))) (.branch 95 (.branch 94 (.leaf 585377144) (.leaf 574126324)) (.branch 96 (.leaf 563106367) (.leaf 552311850)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 541737512) (.leaf 531378245)) (.branch 100 (.leaf 521229085) (.leaf 511285213))) (.branch 103 (.branch 102 (.leaf 501541944) (.leaf 491994726)) (.branch 104 (.leaf 482639132) (.leaf 473470861))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 464485724) (.leaf 455679651)) (.branch 108 (.leaf 447048680) (.leaf 438588953))) (.branch 111 (.branch 110 (.leaf 430296716) (.leaf 422168314)) (.branch 112 (.leaf 414200188) (.leaf 406388869)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 398730980) (.leaf 391223229)) (.branch 116 (.leaf 383862407) (.leaf 376645386))) (.branch 119 (.branch 118 (.leaf 369569118) (.leaf 362630628)) (.branch 120 (.leaf 355827017) (.leaf 349155455)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 434).prefactor = (291968075980041/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 434).cutoff/(generalMeanRows 434).c)).2 =
    (8329282455607/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 434).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 434).q*(generalMeanRows 434).c/2-2 = (1169/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable162.value]
  have hcontinuation : (generalMeanRows 434).q*(generalMeanRows 434).cutoff/2-2 = (6610/3087:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable161.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 434).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 434).criticalRate j.val*(generalMeanRows 434).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 434).c*(generalMeanRows 434).criticalPoint j.val)).2-
      (generalMeanRows 434).J/2-(generalMeanRows 434).error (generalMeanGrid j.val)+
      (generalMeanRows 434).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 434).c)).2-
      (generalMeanRows 434).J/2-(generalMeanRows 434).error 4 := by
  have he : (generalMeanRows 434).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 434) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 434)
    (generalMeanRows_prefactorDomain 434) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0434

/-! Kernel-checked entropy margins for general spectral rectangle 435. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0435
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5130292615) (.branch 2 (.leaf 4961334947) (.leaf 4799917983))) (.branch 5 (.branch 4 (.leaf 4645607400) (.leaf 4497999756)) (.branch 6 (.leaf 4356719799) (.leaf 4221418053)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4091768669) (.leaf 3967467486)) (.branch 10 (.leaf 3848230296) (.leaf 3733791265))) (.branch 13 (.branch 12 (.leaf 3623901514) (.leaf 3518327831)) (.branch 14 (.leaf 3416851496) (.leaf 3319267216))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3225382152) (.branch 17 (.leaf 3135015027) (.leaf 3047995313))) (.branch 20 (.branch 19 (.leaf 2964162486) (.leaf 2883365336)) (.branch 21 (.leaf 2805461339) (.leaf 2730316075)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2657802695) (.leaf 2587801421)) (.branch 25 (.leaf 2520199092) (.leaf 2454888742))) (.branch 28 (.branch 27 (.leaf 2391769204) (.leaf 2330744751)) (.branch 29 (.leaf 2271724754) (.leaf 2214623372)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2159359257) (.branch 32 (.leaf 2105855286) (.leaf 2054038304))) (.branch 35 (.branch 34 (.leaf 2003838894) (.leaf 1955191150)) (.branch 36 (.leaf 1908032477) (.leaf 1862303397)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1817947372) (.leaf 1774910631)) (.branch 40 (.leaf 1733142018) (.leaf 1692592844))) (.branch 43 (.branch 42 (.leaf 1653216748) (.leaf 1614969569)) (.branch 44 (.leaf 1577809221) (.leaf 1541695588))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1506590407) (.branch 47 (.leaf 1472457174) (.leaf 1439261050))) (.branch 50 (.branch 49 (.leaf 1406968768) (.leaf 1375548554)) (.branch 51 (.leaf 1344970045) (.leaf 1315204219)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1286223322) (.leaf 1258000805)) (.branch 55 (.leaf 1230511262) (.leaf 1203730367))) (.branch 58 (.branch 57 (.leaf 1177634829) (.leaf 1152202329)) (.branch 59 (.leaf 1127411480) (.leaf 1103241776))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1079673551) (.branch 62 (.leaf 1056687935) (.leaf 1034266817))) (.branch 65 (.branch 64 (.leaf 1012392810) (.leaf 991049212)) (.branch 66 (.leaf 970219976) (.leaf 949889680)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 930043494) (.leaf 910667154)) (.branch 70 (.leaf 891746937) (.leaf 873269634))) (.branch 73 (.branch 72 (.leaf 855222528) (.leaf 837593368)) (.branch 74 (.leaf 820370353) (.leaf 803542108))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 787097667) (.branch 77 (.leaf 771026453) (.leaf 755318262))) (.branch 80 (.branch 79 (.leaf 739963247) (.leaf 724951900)) (.branch 81 (.leaf 710275043) (.leaf 695923806)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 681889620) (.leaf 668164203)) (.branch 85 (.leaf 654739545) (.leaf 641607901))) (.branch 88 (.branch 87 (.leaf 628761776) (.leaf 616193920)) (.branch 89 (.leaf 603897310) (.leaf 591865149)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 580090852) (.branch 92 (.leaf 568568040) (.leaf 557290531))) (.branch 95 (.branch 94 (.leaf 546252330) (.leaf 535447627)) (.branch 96 (.leaf 524870785) (.leaf 514516335)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 504378972) (.leaf 494453543)) (.branch 100 (.leaf 484735048) (.leaf 475218630))) (.branch 103 (.branch 102 (.leaf 465899572) (.leaf 456773290)) (.branch 104 (.leaf 447835330) (.leaf 439081362))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 430507176) (.leaf 422108678)) (.branch 108 (.leaf 413881887) (.leaf 405822928))) (.branch 111 (.branch 110 (.leaf 397928031) (.leaf 390193528)) (.branch 112 (.leaf 382615847) (.leaf 375191510)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 367917131) (.leaf 360789410)) (.branch 116 (.leaf 353805135) (.leaf 346961174))) (.branch 119 (.branch 118 (.leaf 340254475) (.leaf 333682063)) (.branch 120 (.leaf 327241040) (.leaf 320928578)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 435).prefactor = (46737042552801/10000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 435).cutoff/(generalMeanRows 435).c)).2 =
    (40580093576857/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 435).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 435).q*(generalMeanRows 435).c/2-2 = (1203/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable135.value]
  have hcontinuation : (generalMeanRows 435).q*(generalMeanRows 435).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable160.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 435).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 435).criticalRate j.val*(generalMeanRows 435).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 435).c*(generalMeanRows 435).criticalPoint j.val)).2-
      (generalMeanRows 435).J/2-(generalMeanRows 435).error (generalMeanGrid j.val)+
      (generalMeanRows 435).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 435).c)).2-
      (generalMeanRows 435).J/2-(generalMeanRows 435).error 4 := by
  have he : (generalMeanRows 435).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 435) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 435)
    (generalMeanRows_prefactorDomain 435) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0435

/-! Kernel-checked entropy margins for general spectral rectangle 436. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0436
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5060940177) (.branch 2 (.leaf 4891798494) (.leaf 4730232495))) (.branch 5 (.branch 4 (.leaf 4575806258) (.leaf 4428114831)) (.branch 6 (.leaf 4286781525) (.leaf 4151455500)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4021809611) (.leaf 3897538462)) (.branch 10 (.leaf 3778356664) (.leaf 3663997257))) (.branch 13 (.branch 12 (.leaf 3554210287) (.leaf 3448761512)) (.branch 14 (.leaf 3347431226) (.leaf 3250013190))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3156313657) (.branch 17 (.leaf 3066150482) (.leaf 2979352299))) (.branch 20 (.branch 19 (.leaf 2895757780) (.leaf 2815214942)) (.branch 21 (.leaf 2737580518) (.leaf 2662719373)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2590503966) (.leaf 2520813856)) (.branch 25 (.leaf 2453535243) (.leaf 2388560541))) (.branch 28 (.branch 27 (.leaf 2325787992) (.leaf 2265121291)) (.branch 29 (.leaf 2206469258) (.leaf 2149745515)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2094868202) (.branch 32 (.leaf 2041759695) (.leaf 1990346362))) (.branch 35 (.branch 34 (.leaf 1940558318) (.leaf 1892329212)) (.branch 36 (.leaf 1845596016) (.leaf 1800298836)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1756380727) (.leaf 1713787532)) (.branch 40 (.leaf 1672467718) (.leaf 1632372234))) (.branch 43 (.branch 42 (.leaf 1593454367) (.leaf 1555669617)) (.branch 44 (.leaf 1518975575) (.leaf 1483331806))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1448699745) (.branch 47 (.leaf 1415042594) (.leaf 1382325230))) (.branch 50 (.branch 49 (.leaf 1350514112) (.leaf 1319577203)) (.branch 51 (.leaf 1289483887) (.leaf 1260204894)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1231712236) (.leaf 1203979135)) (.branch 55 (.leaf 1176979963) (.leaf 1150690187))) (.branch 58 (.branch 57 (.leaf 1125086308) (.leaf 1100145813)) (.branch 59 (.leaf 1075847126) (.leaf 1052169558))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1029093268) (.branch 62 (.leaf 1006599219) (.leaf 984669137))) (.branch 65 (.branch 64 (.leaf 963285480) (.leaf 942431396)) (.branch 66 (.leaf 922090697) (.leaf 902247820)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 882887804) (.leaf 863996259)) (.branch 70 (.leaf 845559341) (.leaf 827563723))) (.branch 73 (.branch 72 (.leaf 809996577) (.leaf 792845547)) (.branch 74 (.leaf 776098728) (.leaf 759744649))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 743772251) (.branch 77 (.leaf 728170866) (.leaf 712930208))) (.branch 80 (.branch 79 (.leaf 698040348) (.leaf 683491703)) (.branch 81 (.leaf 669275018) (.leaf 655381357)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 641802084) (.leaf 628528854)) (.branch 85 (.leaf 615553599) (.leaf 602868517))) (.branch 88 (.branch 87 (.leaf 590466061) (.leaf 578338929)) (.branch 89 (.leaf 566480054) (.leaf 554882593)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 543539920) (.branch 92 (.leaf 532445618) (.leaf 521593467))) (.branch 95 (.branch 94 (.leaf 510977440) (.leaf 500591695)) (.branch 96 (.leaf 490430566) (.leaf 480488558)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 470760339) (.leaf 461240735)) (.branch 100 (.leaf 451924727) (.leaf 442807438))) (.branch 103 (.branch 102 (.leaf 433884133) (.leaf 425150216)) (.branch 104 (.leaf 416601218) (.leaf 408232797))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 400040736) (.leaf 392020930)) (.branch 108 (.leaf 384169393) (.leaf 376482244))) (.branch 111 (.branch 110 (.leaf 368955711) (.leaf 361586121)) (.branch 112 (.leaf 354369903) (.leaf 347303578)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 340383762) (.leaf 333607158)) (.branch 116 (.leaf 326970557) (.leaf 320470831))) (.branch 119 (.branch 118 (.leaf 314104936) (.leaf 307869904)) (.branch 120 (.leaf 301762842) (.leaf 295780932)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 436).prefactor = (2344808472719459/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 436).cutoff/(generalMeanRows 436).c)).2 =
    (49763573768177/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 436).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 436).q*(generalMeanRows 436).c/2-2 = (1237/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable167.value]
  have hcontinuation : (generalMeanRows 436).q*(generalMeanRows 436).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable160.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 436).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 436).criticalRate j.val*(generalMeanRows 436).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 436).c*(generalMeanRows 436).criticalPoint j.val)).2-
      (generalMeanRows 436).J/2-(generalMeanRows 436).error (generalMeanGrid j.val)+
      (generalMeanRows 436).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 436).c)).2-
      (generalMeanRows 436).J/2-(generalMeanRows 436).error 4 := by
  have he : (generalMeanRows 436).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 436) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 436)
    (generalMeanRows_prefactorDomain 436) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0436

/-! Kernel-checked entropy margins for general spectral rectangle 437. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0437
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5216831238) (.branch 2 (.leaf 5047577936) (.leaf 4885866946))) (.branch 5 (.branch 4 (.leaf 4731262349) (.leaf 4583359301)) (.branch 6 (.leaf 4441781310) (.leaf 4306177819)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4176222038) (.leaf 4051608995)) (.branch 10 (.leaf 3932053782) (.leaf 3817289974))) (.branch 13 (.branch 12 (.leaf 3707068197) (.leaf 3601154829)) (.branch 14 (.leaf 3499330820) (.leaf 3401390618))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3307141188) (.branch 17 (.leaf 3216401118) (.leaf 3128999794))) (.branch 20 (.branch 19 (.leaf 3044776655) (.leaf 2963580497)) (.branch 21 (.leaf 2885268838) (.leaf 2809707336)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2736769248) (.leaf 2666334929)) (.branch 25 (.leaf 2598291378) (.leaf 2532531805))) (.branch 28 (.branch 27 (.leaf 2468955241) (.leaf 2407466169)) (.branch 29 (.leaf 2347974188) (.leaf 2290393693)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2234643585) (.branch 32 (.leaf 2180646995) (.leaf 2128331031))) (.branch 35 (.branch 34 (.leaf 2077626542) (.leaf 2028467896)) (.branch 36 (.leaf 1980792770) (.leaf 1934541963)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1889659214) (.leaf 1846091029)) (.branch 40 (.leaf 1803786529) (.leaf 1762697301))) (.branch 43 (.branch 42 (.leaf 1722777255) (.leaf 1683982500)) (.branch 44 (.leaf 1646271222) (.leaf 1609603565))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1573941529) (.branch 47 (.leaf 1539248865) (.leaf 1505490985))) (.branch 50 (.branch 49 (.leaf 1472634870) (.leaf 1440648988)) (.branch 51 (.leaf 1409503213) (.leaf 1379168755)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1349618087) (.leaf 1320824879)) (.branch 55 (.leaf 1292763939) (.leaf 1265411155))) (.branch 58 (.branch 57 (.leaf 1238743436) (.leaf 1212738664)) (.branch 59 (.leaf 1187375642) (.leaf 1162634051))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1138494407) (.branch 62 (.leaf 1114938014) (.leaf 1091946932))) (.branch 65 (.branch 64 (.leaf 1069503937) (.leaf 1047592486)) (.branch 66 (.leaf 1026196685) (.leaf 1005301258)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 984891520) (.leaf 964953342)) (.branch 70 (.leaf 945473133) (.leaf 926437812))) (.branch 73 (.branch 72 (.leaf 907834782) (.leaf 889651910)) (.branch 74 (.leaf 871877507) (.leaf 854500305))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 837509441) (.branch 77 (.leaf 820894437) (.leaf 804645182))) (.branch 80 (.branch 79 (.leaf 788751918) (.leaf 773205224)) (.branch 81 (.leaf 757996002) (.leaf 743115460)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 728555103) (.leaf 714306717)) (.branch 85 (.leaf 700362361) (.leaf 686714349))) (.branch 88 (.branch 87 (.leaf 673355248) (.leaf 660277860)) (.branch 89 (.leaf 647475218) (.leaf 634940572)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 622667385) (.branch 92 (.leaf 610649319) (.leaf 598880232))) (.branch 95 (.branch 94 (.leaf 587354169) (.leaf 576065351)) (.branch 96 (.leaf 565008175) (.leaf 554177202)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 543567151) (.leaf 533172896)) (.branch 100 (.leaf 522989459) (.leaf 513012003))) (.branch 103 (.branch 102 (.leaf 503235828) (.leaf 493656365)) (.branch 104 (.leaf 484269175) (.leaf 475069938))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 466054456) (.leaf 457218642)) (.branch 108 (.leaf 448558521) (.leaf 440070222))) (.branch 111 (.branch 110 (.leaf 431749979) (.leaf 423594125)) (.branch 112 (.leaf 415599088) (.leaf 407761388)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 400077635) (.leaf 392544528)) (.branch 116 (.leaf 385158845) (.leaf 377917450))) (.branch 119 (.branch 118 (.leaf 370817283) (.leaf 363855359)) (.branch 120 (.leaf 357028770) (.leaf 350334676)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 437).prefactor = (1171816620114583/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 437).cutoff/(generalMeanRows 437).c)).2 =
    (8329282455607/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 437).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 437).q*(generalMeanRows 437).c/2-2 = (1169/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable162.value]
  have hcontinuation : (generalMeanRows 437).q*(generalMeanRows 437).cutoff/2-2 = (6610/3087:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable161.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 437).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 437).criticalRate j.val*(generalMeanRows 437).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 437).c*(generalMeanRows 437).criticalPoint j.val)).2-
      (generalMeanRows 437).J/2-(generalMeanRows 437).error (generalMeanGrid j.val)+
      (generalMeanRows 437).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 437).c)).2-
      (generalMeanRows 437).J/2-(generalMeanRows 437).error 4 := by
  have he : (generalMeanRows 437).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 437) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 437)
    (generalMeanRows_prefactorDomain 437) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0437

/-! Kernel-checked entropy margins for general spectral rectangle 438. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0438
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5234450315) (.branch 2 (.leaf 5064625385) (.leaf 4902368239))) (.branch 5 (.branch 4 (.leaf 4747241489) (.leaf 4598838920)) (.branch 6 (.leaf 4456782770) (.leaf 4320721298)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4190326611) (.leaf 4065292706)) (.branch 10 (.leaf 3945333713) (.leaf 3830182307))) (.branch 13 (.branch 12 (.leaf 3719588272) (.leaf 3613317198)) (.branch 14 (.leaf 3511149293) (.leaf 3412878313))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3318310569) (.branch 17 (.leaf 3227264037) (.leaf 3139567529))) (.branch 20 (.branch 19 (.leaf 3055059939) (.leaf 2973589552)) (.branch 21 (.leaf 2895013407) (.leaf 2819196708)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2746012282) (.leaf 2675340082)) (.branch 25 (.leaf 2607066723) (.leaf 2541085057))) (.branch 28 (.branch 27 (.leaf 2477293772) (.leaf 2415597030)) (.branch 29 (.leaf 2355904124) (.leaf 2298129160)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2242190764) (.branch 32 (.leaf 2188011808) (.leaf 2135519155))) (.branch 35 (.branch 34 (.leaf 2084643419) (.leaf 2035318746)) (.branch 36 (.leaf 1987482605) (.leaf 1941075593)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1896041259) (.leaf 1852325929)) (.branch 40 (.leaf 1809878552) (.leaf 1768650550))) (.branch 43 (.branch 42 (.leaf 1728595680) (.leaf 1689669903)) (.branch 44 (.leaf 1651831260) (.leaf 1615039764))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1579257284) (.branch 47 (.leaf 1544447450) (.leaf 1510575558))) (.branch 50 (.branch 49 (.leaf 1477608477) (.leaf 1445514567)) (.branch 51 (.leaf 1414263602) (.leaf 1383826694)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1354176222) (.leaf 1325285770)) (.branch 55 (.leaf 1297130059) (.leaf 1269684895))) (.branch 58 (.branch 57 (.leaf 1242927109) (.leaf 1216834509)) (.branch 59 (.leaf 1191385827) (.leaf 1166560676))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1142339503) (.branch 62 (.leaf 1118703552) (.leaf 1095634822))) (.branch 65 (.branch 64 (.leaf 1073116028) (.leaf 1051130575)) (.branch 66 (.leaf 1029662512) (.leaf 1008696515)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 988217845) (.leaf 968212329)) (.branch 70 (.leaf 948666329) (.leaf 929566719))) (.branch 73 (.branch 72 (.leaf 910900860) (.leaf 892656578)) (.branch 74 (.leaf 874822144) (.leaf 857386254))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 840338006) (.branch 77 (.leaf 823666887) (.leaf 807362752))) (.branch 80 (.branch 79 (.leaf 791415811) (.leaf 775816611)) (.branch 81 (.leaf 760556021) (.leaf 745625223)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 731015690) (.leaf 716719183)) (.branch 85 (.leaf 702727731) (.leaf 689033625))) (.branch 88 (.branch 87 (.leaf 675629406) (.leaf 662507851)) (.branch 89 (.leaf 649661970) (.leaf 637084990)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 624770352) (.branch 92 (.leaf 612711697) (.leaf 600902862))) (.branch 95 (.branch 94 (.leaf 589337870) (.leaf 578010927)) (.branch 96 (.leaf 566916407) (.leaf 556048853)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 545402969) (.leaf 534973609)) (.branch 100 (.leaf 524755779) (.leaf 514744625))) (.branch 103 (.branch 102 (.leaf 504935432) (.leaf 495323617)) (.branch 104 (.leaf 485904722) (.leaf 476674417))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 467628486) (.leaf 458762831)) (.branch 108 (.leaf 450073461) (.leaf 441556494))) (.branch 111 (.branch 110 (.leaf 433208151) (.leaf 425024752)) (.branch 112 (.leaf 417002712) (.leaf 409138542)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 401428839) (.leaf 393870289)) (.branch 116 (.leaf 386459663) (.leaf 379193811))) (.branch 119 (.branch 118 (.leaf 372069664) (.leaf 365084227)) (.branch 120 (.leaf 358234582) (.leaf 351517879)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 438).prefactor = (2351548515308631/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 438).cutoff/(generalMeanRows 438).c)).2 =
    (8329282455607/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 438).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 438).q*(generalMeanRows 438).c/2-2 = (1169/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable162.value]
  have hcontinuation : (generalMeanRows 438).q*(generalMeanRows 438).cutoff/2-2 = (6610/3087:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable161.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 438).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 438).criticalRate j.val*(generalMeanRows 438).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 438).c*(generalMeanRows 438).criticalPoint j.val)).2-
      (generalMeanRows 438).J/2-(generalMeanRows 438).error (generalMeanGrid j.val)+
      (generalMeanRows 438).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 438).c)).2-
      (generalMeanRows 438).J/2-(generalMeanRows 438).error 4 := by
  have he : (generalMeanRows 438).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 438) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 438)
    (generalMeanRows_prefactorDomain 438) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0438

/-! Kernel-checked entropy margins for general spectral rectangle 439. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0439
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5078171300) (.branch 2 (.leaf 4908453736) (.leaf 4746337648))) (.branch 5 (.branch 4 (.leaf 4591385632) (.leaf 4443191356)) (.branch 6 (.leaf 4301376848) (.leaf 4165590076)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4035502777) (.leaf 3910808519)) (.branch 10 (.leaf 3791220939) (.leaf 3676472170))) (.branch 13 (.branch 12 (.leaf 3566311405) (.leaf 3460503606)) (.branch 14 (.leaf 3358828318) (.leaf 3261078600))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3167060046) (.branch 17 (.leaf 3076589889) (.leaf 2989496182))) (.branch 20 (.branch 19 (.leaf 2905617046) (.leaf 2824799982)) (.branch 21 (.leaf 2746901235) (.leaf 2671785208)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2599323927) (.leaf 2529396541)) (.branch 25 (.leaf 2461888862) (.leaf 2396692940))) (.branch 28 (.branch 27 (.leaf 2333706666) (.leaf 2272833412)) (.branch 29 (.leaf 2213981684) (.leaf 2157064814)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2102000658) (.branch 32 (.leaf 2048711331) (.leaf 1997122949))) (.branch 35 (.branch 34 (.leaf 1947165391) (.leaf 1898772078)) (.branch 36 (.leaf 1851879768) (.leaf 1806428363)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1762360725) (.leaf 1719622511)) (.branch 40 (.leaf 1678162015) (.leaf 1637930016))) (.branch 43 (.branch 42 (.leaf 1598879645) (.leaf 1560966249)) (.branch 44 (.leaf 1524147273) (.leaf 1488382147))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1453632173) (.branch 47 (.leaf 1419860429) (.leaf 1387031671))) (.branch 50 (.branch 49 (.leaf 1355112245) (.leaf 1324070004)) (.branch 51 (.leaf 1293874228) (.leaf 1264495549)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1235905881) (.leaf 1208078356)) (.branch 55 (.leaf 1180987259) (.leaf 1154607974))) (.branch 58 (.branch 57 (.leaf 1128916920) (.leaf 1103891510)) (.branch 59 (.leaf 1079510092) (.leaf 1055751909))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1032597050) (.branch 62 (.leaf 1010026415) (.leaf 988021667))) (.branch 65 (.branch 64 (.leaf 966565205) (.leaf 945640119)) (.branch 66 (.leaf 925230164) (.leaf 905319728)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 885893796) (.leaf 866937931)) (.branch 70 (.leaf 848438240) (.leaf 830381352))) (.branch 73 (.branch 72 (.leaf 812754395) (.leaf 795544970)) (.branch 74 (.leaf 778741133) (.leaf 762331373))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 746304593) (.branch 77 (.leaf 730650090) (.leaf 715357542))) (.branch 80 (.branch 79 (.leaf 700416986) (.leaf 685818806)) (.branch 81 (.leaf 671553717) (.leaf 657612752)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 643987245) (.leaf 630668824)) (.branch 85 (.leaf 617649391) (.leaf 604921120))) (.branch 88 (.branch 87 (.leaf 592476437) (.leaf 580308016)) (.branch 89 (.leaf 568408764) (.leaf 556771817)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 545390526) (.branch 92 (.leaf 534258450) (.leaf 523369351))) (.branch 95 (.branch 94 (.leaf 512717179) (.leaf 502296074)) (.branch 96 (.leaf 492100349) (.leaf 482124490)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 472363149) (.leaf 462811135)) (.branch 100 (.leaf 453463408) (.leaf 444315076))) (.branch 103 (.branch 102 (.leaf 435361391) (.leaf 426597737)) (.branch 104 (.leaf 418019631) (.leaf 409622719))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 401402765) (.leaf 393355655)) (.branch 108 (.leaf 385477385) (.leaf 377764064))) (.branch 111 (.branch 110 (.leaf 370211904) (.leaf 362817223)) (.branch 112 (.leaf 355576436) (.leaf 348486052)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 341542676) (.leaf 334742999)) (.branch 116 (.leaf 328083802) (.leaf 321561947))) (.branch 119 (.branch 118 (.leaf 315174378) (.leaf 308918117)) (.branch 120 (.leaf 302790262) (.leaf 296787986)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 439).prefactor = (4705583813974087/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 439).cutoff/(generalMeanRows 439).c)).2 =
    (49763573768177/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 439).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 439).q*(generalMeanRows 439).c/2-2 = (1237/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable167.value]
  have hcontinuation : (generalMeanRows 439).q*(generalMeanRows 439).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable160.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 439).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 439).criticalRate j.val*(generalMeanRows 439).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 439).c*(generalMeanRows 439).criticalPoint j.val)).2-
      (generalMeanRows 439).J/2-(generalMeanRows 439).error (generalMeanGrid j.val)+
      (generalMeanRows 439).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 439).c)).2-
      (generalMeanRows 439).J/2-(generalMeanRows 439).error 4 := by
  have he : (generalMeanRows 439).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 439) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 439)
    (generalMeanRows_prefactorDomain 439) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0439

/-! Kernel-checked entropy margins for general spectral rectangle 440. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0440
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5095461090) (.branch 2 (.leaf 4925165684) (.leaf 4762497635))) (.branch 5 (.branch 4 (.leaf 4607018050) (.leaf 4458319213)) (.branch 6 (.leaf 4316021865) (.leaf 4179772775)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4049242565) (.leaf 3924123757)) (.branch 10 (.leaf 3804129014) (.leaf 3688989556))) (.branch 13 (.branch 12 (.leaf 3578453724) (.leaf 3472285678)) (.branch 14 (.leaf 3370264213) (.leaf 3272181684))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3177843023) (.branch 17 (.leaf 3087064840) (.leaf 2999674602))) (.branch 20 (.branch 19 (.leaf 2915509881) (.leaf 2834417657)) (.branch 21 (.leaf 2756253685) (.leaf 2680881909)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2608173917) (.leaf 2538008447)) (.branch 25 (.leaf 2470270923) (.leaf 2404853026))) (.branch 28 (.branch 27 (.leaf 2341652302) (.leaf 2280571791)) (.branch 29 (.leaf 2221519689) (.leaf 2164409032)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2109157397) (.branch 32 (.leaf 2055686635) (.leaf 2003922609))) (.branch 35 (.branch 34 (.leaf 1953794958) (.leaf 1905236879)) (.branch 36 (.leaf 1858184914) (.leaf 1812578759)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1768361083) (.leaf 1725477358)) (.branch 40 (.leaf 1683875700) (.leaf 1643506722))) (.branch 43 (.branch 42 (.leaf 1604323395) (.leaf 1566280914)) (.branch 44 (.leaf 1529336580) (.leaf 1493449683))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1458581395) (.branch 47 (.leaf 1424694667) (.leaf 1391754136))) (.branch 50 (.branch 49 (.leaf 1359726033) (.leaf 1328578102)) (.branch 51 (.leaf 1298279518) (.leaf 1268800812)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1240113804) (.leaf 1212191533)) (.branch 55 (.leaf 1185008199) (.leaf 1158539099))) (.branch 58 (.branch 57 (.leaf 1132760575) (.leaf 1107649960)) (.branch 59 (.leaf 1083185530) (.leaf 1059346457))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1036112762) (.branch 62 (.leaf 1013465280) (.leaf 991385612))) (.branch 65 (.branch 64 (.leaf 969856096) (.leaf 948859766)) (.branch 66 (.leaf 928380321) (.leaf 908402095)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 888910024) (.leaf 869889619)) (.branch 70 (.leaf 851326941) (.leaf 833208575))) (.branch 73 (.branch 72 (.leaf 815521602) (.leaf 798253584)) (.branch 74 (.leaf 781392534) (.leaf 764926904))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 748845556) (.branch 77 (.leaf 733137755) (.leaf 717793139))) (.branch 80 (.branch 79 (.leaf 702801715) (.leaf 688153832)) (.branch 81 (.leaf 673840175) (.leaf 659851744)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 646179847) (.leaf 632816079)) (.branch 85 (.leaf 619752319) (.leaf 606980712))) (.branch 88 (.branch 87 (.leaf 594493658) (.leaf 582283806)) (.branch 89 (.leaf 570344041) (.leaf 558667473)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 547247432) (.branch 92 (.leaf 536077455) (.leaf 525151281))) (.branch 95 (.branch 94 (.leaf 514462842) (.leaf 504006255)) (.branch 96 (.leaf 493775816) (.leaf 483765993)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 473971417) (.leaf 464386880)) (.branch 100 (.leaf 455007327) (.leaf 445827848))) (.branch 103 (.branch 102 (.leaf 436843678) (.leaf 428050186)) (.branch 104 (.leaf 419442874) (.leaf 411017373))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 402769432) (.leaf 394694924)) (.branch 108 (.leaf 386789831) (.leaf 379050247))) (.branch 111 (.branch 110 (.leaf 371472375) (.leaf 364052517)) (.branch 112 (.leaf 356787077) (.leaf 349672552)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 342705536) (.leaf 335882708)) (.branch 116 (.leaf 329200838) (.leaf 322656778))) (.branch 119 (.branch 118 (.leaf 316247461) (.leaf 309969899)) (.branch 120 (.leaf 303821181) (.leaf 297798468)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 440).prefactor = (4721605045348227/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 440).cutoff/(generalMeanRows 440).c)).2 =
    (49763573768177/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 440).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 440).q*(generalMeanRows 440).c/2-2 = (1237/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable167.value]
  have hcontinuation : (generalMeanRows 440).q*(generalMeanRows 440).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable160.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 440).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 440).criticalRate j.val*(generalMeanRows 440).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 440).c*(generalMeanRows 440).criticalPoint j.val)).2-
      (generalMeanRows 440).J/2-(generalMeanRows 440).error (generalMeanGrid j.val)+
      (generalMeanRows 440).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 440).c)).2-
      (generalMeanRows 440).J/2-(generalMeanRows 440).error 4 := by
  have he : (generalMeanRows 440).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 440) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 440)
    (generalMeanRows_prefactorDomain 440) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0440

/-! Kernel-checked entropy margins for general spectral rectangle 441. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0441
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5314773506) (.branch 2 (.leaf 5142773854) (.leaf 4978480202))) (.branch 5 (.branch 4 (.leaf 4821444412) (.leaf 4671250387)) (.branch 6 (.leaf 4527511272) (.leaf 4389866955)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4257981832) (.leaf 4131542797)) (.branch 10 (.leaf 4010257429) (.leaf 3893852368))) (.branch 13 (.branch 12 (.leaf 3782071825) (.leaf 3674676252)) (.branch 14 (.leaf 3571441116) (.leaf 3472155796))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3376622563) (.branch 17 (.leaf 3284655665) (.leaf 3196080469))) (.branch 20 (.branch 19 (.leaf 3110732694) (.leaf 3028457691)) (.branch 21 (.leaf 2949109790) (.leaf 2872551694)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2798653926) (.leaf 2727294308)) (.branch 25 (.leaf 2658357492) (.leaf 2591734516))) (.branch 28 (.branch 27 (.leaf 2527322401) (.leaf 2465023765)) (.branch 29 (.leaf 2404746482) (.leaf 2346403350)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2289911791) (.branch 32 (.leaf 2235193566) (.leaf 2182174516))) (.branch 35 (.branch 34 (.leaf 2130784318) (.leaf 2080956253)) (.branch 36 (.leaf 2032626996) (.leaf 1985736415)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1940227390) (.leaf 1896045634)) (.branch 40 (.leaf 1853139533) (.leaf 1811459992))) (.branch 43 (.branch 42 (.leaf 1770960298) (.leaf 1731595979)) (.branch 44 (.leaf 1693324684) (.leaf 1656106065))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1619901663) (.branch 47 (.leaf 1584674809) (.leaf 1550390528))) (.branch 50 (.branch 49 (.leaf 1517015441) (.leaf 1484517685)) (.branch 51 (.leaf 1452866830) (.leaf 1422033804)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1391990822) (.leaf 1362711317)) (.branch 55 (.leaf 1334169876) (.leaf 1306342184))) (.branch 58 (.branch 57 (.leaf 1279204965) (.leaf 1252735928)) (.branch 59 (.leaf 1226913722) (.leaf 1201717880))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1177128785) (.branch 62 (.leaf 1153127619) (.leaf 1129696329))) (.branch 65 (.branch 64 (.leaf 1106817586) (.leaf 1084474752)) (.branch 66 (.leaf 1062651846) (.leaf 1041333510)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1020504984) (.leaf 1000152072)) (.branch 70 (.leaf 980261118) (.leaf 960818982))) (.branch 73 (.branch 72 (.leaf 941813014) (.leaf 923231031)) (.branch 74 (.leaf 905061298) (.leaf 887292504))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 869913746) (.branch 77 (.leaf 852914507) (.leaf 836284644))) (.branch 80 (.branch 79 (.leaf 820014365) (.leaf 804094221)) (.branch 81 (.leaf 788515083) (.leaf 773268133)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 758344850) (.leaf 743736997)) (.branch 85 (.leaf 729436608) (.leaf 715435978))) (.branch 88 (.branch 87 (.leaf 701727650) (.leaf 688304407)) (.branch 89 (.leaf 675159263) (.leaf 662285447)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 649676405) (.branch 92 (.leaf 637325780) (.leaf 625227412))) (.branch 95 (.branch 94 (.leaf 613375328) (.leaf 601763734)) (.branch 96 (.leaf 590387008) (.leaf 579239693)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 568316492) (.leaf 557612263)) (.branch 100 (.leaf 547122010) (.leaf 536840879))) (.branch 103 (.branch 102 (.leaf 526764152) (.leaf 516887246)) (.branch 104 (.leaf 507205702) (.leaf 497715184))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 488411476) (.leaf 479290474)) (.branch 108 (.leaf 470348184) (.leaf 461580719))) (.branch 111 (.branch 110 (.leaf 452984295) (.leaf 444555226)) (.branch 112 (.leaf 436289921) (.leaf 428184884)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 420236705) (.leaf 412442062)) (.branch 116 (.leaf 404797719) (.leaf 397300517))) (.branch 119 (.branch 118 (.leaf 389947377) (.leaf 382735297)) (.branch 120 (.leaf 375661347) (.leaf 368722669)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 441).prefactor = (955968400435177/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 441).cutoff/(generalMeanRows 441).c)).2 =
    (424856363912193/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 441).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 441).q*(generalMeanRows 441).c/2-2 = (2879/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable152.value]
  have hcontinuation : (generalMeanRows 441).q*(generalMeanRows 441).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable148.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 441).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 441).criticalRate j.val*(generalMeanRows 441).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 441).c*(generalMeanRows 441).criticalPoint j.val)).2-
      (generalMeanRows 441).J/2-(generalMeanRows 441).error (generalMeanGrid j.val)+
      (generalMeanRows 441).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 441).c)).2-
      (generalMeanRows 441).J/2-(generalMeanRows 441).error 4 := by
  have he : (generalMeanRows 441).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 441) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 441)
    (generalMeanRows_prefactorDomain 441) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0441

/-! Kernel-checked entropy margins for general spectral rectangle 442. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0442
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5444665380) (.branch 2 (.leaf 5271204224) (.leaf 5105490572))) (.branch 5 (.branch 4 (.leaf 4947073288) (.leaf 4795533522)) (.branch 6 (.leaf 4650481887) (.leaf 4511555944)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4378417946) (.leaf 4250752815)) (.branch 10 (.leaf 4128266315) (.leaf 4010683411))) (.branch 13 (.branch 12 (.leaf 3897746774) (.leaf 3789215434)) (.branch 14 (.leaf 3684863551) (.leaf 3584479296))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3487863829) (.branch 17 (.leaf 3394830374) (.leaf 3305203355))) (.branch 20 (.branch 19 (.leaf 3218817622) (.leaf 3135517727)) (.branch 21 (.leaf 3055157262) (.leaf 2977598257)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2902710608) (.leaf 2830371570)) (.branch 25 (.leaf 2760465267) (.leaf 2692882258))) (.branch 28 (.branch 27 (.leaf 2627519119) (.leaf 2564278066)) (.branch 29 (.leaf 2503066603) (.leaf 2443797189)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2386386937) (.branch 32 (.leaf 2330757327) (.leaf 2276833944))) (.branch 35 (.branch 34 (.leaf 2224546230) (.leaf 2173827255)) (.branch 36 (.leaf 2124613503) (.leaf 2076844668)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2030463473) (.leaf 1985415490)) (.branch 40 (.leaf 1941648979) (.leaf 1899114733))) (.branch 43 (.branch 42 (.leaf 1857765935) (.leaf 1817558024)) (.branch 44 (.leaf 1778448570) (.leaf 1740397153))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1703365255) (.branch 47 (.leaf 1667316152) (.leaf 1632214821))) (.branch 50 (.branch 49 (.leaf 1598027844) (.leaf 1564723324)) (.branch 51 (.leaf 1532270803) (.leaf 1500641185)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1469806664) (.leaf 1439740659)) (.branch 55 (.leaf 1410417746) (.leaf 1381813600))) (.branch 58 (.branch 57 (.leaf 1353904939) (.leaf 1326669471)) (.branch 59 (.leaf 1300085840) (.leaf 1274133584))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1248793086) (.branch 62 (.leaf 1224045532) (.leaf 1199872875))) (.branch 65 (.branch 64 (.leaf 1176257793) (.leaf 1153183653)) (.branch 66 (.leaf 1130634482) (.leaf 1108594931)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1087050248) (.leaf 1065986245)) (.branch 70 (.leaf 1045389275) (.leaf 1025246208))) (.branch 73 (.branch 72 (.leaf 1005544400) (.leaf 986271679)) (.branch 74 (.leaf 967416315) (.leaf 948967007))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 930912857) (.branch 77 (.leaf 913243357) (.leaf 895948368))) (.branch 80 (.branch 79 (.leaf 879018105) (.leaf 862443122)) (.branch 81 (.leaf 846214296) (.leaf 830322810)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 814760148) (.leaf 799518073)) (.branch 85 (.leaf 784588620) (.leaf 769964084))) (.branch 88 (.branch 87 (.leaf 755637009) (.leaf 741600175)) (.branch 89 (.leaf 727846592) (.leaf 714369489)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 701162305) (.branch 92 (.leaf 688218679) (.leaf 675532445))) (.branch 95 (.branch 94 (.leaf 663097624) (.leaf 650908413)) (.branch 96 (.leaf 638959182) (.leaf 627244464)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 615758954) (.leaf 604497497)) (.branch 100 (.leaf 593455084) (.leaf 582626851))) (.branch 103 (.branch 102 (.leaf 572008066) (.leaf 561594130)) (.branch 104 (.leaf 551380571) (.leaf 541363037))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 531537295) (.leaf 521899223)) (.branch 108 (.leaf 512444812) (.leaf 503170154))) (.branch 111 (.branch 110 (.leaf 494071446) (.leaf 485144982)) (.branch 112 (.leaf 476387152) (.leaf 467794438)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 459363408) (.leaf 451090720)) (.branch 116 (.leaf 442973111) (.leaf 435007403))) (.branch 119 (.branch 118 (.leaf 427190491) (.leaf 419519349)) (.branch 120 (.leaf 411991022) (.leaf 404602627)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 442).prefactor = (4811972284467731/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 442).cutoff/(generalMeanRows 442).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 442).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 442).q*(generalMeanRows 442).c/2-2 = (2793/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable128.value]
  have hcontinuation : (generalMeanRows 442).q*(generalMeanRows 442).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable148.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 442).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 442).criticalRate j.val*(generalMeanRows 442).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 442).c*(generalMeanRows 442).criticalPoint j.val)).2-
      (generalMeanRows 442).J/2-(generalMeanRows 442).error (generalMeanGrid j.val)+
      (generalMeanRows 442).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 442).c)).2-
      (generalMeanRows 442).J/2-(generalMeanRows 442).error 4 := by
  have he : (generalMeanRows 442).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 442) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 442)
    (generalMeanRows_prefactorDomain 442) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0442

/-! Kernel-checked entropy margins for general spectral rectangle 443. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0443
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5121739184) (.branch 2 (.leaf 4948384463) (.leaf 4782847702))) (.branch 5 (.branch 4 (.leaf 4624677828) (.leaf 4473455833)) (.branch 6 (.leaf 4328791975) (.leaf 4190323284)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4057711321) (.leaf 3930640174)) (.branch 10 (.leaf 3808814647) (.leaf 3691958629))) (.branch 13 (.branch 12 (.leaf 3579813621) (.leaf 3472137390)) (.branch 14 (.leaf 3368702760) (.leaf 3269296500))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3173718311) (.branch 17 (.leaf 3081779909) (.leaf 2993304171))) (.branch 20 (.branch 19 (.leaf 2908124368) (.leaf 2826083444)) (.branch 21 (.leaf 2747033368) (.leaf 2670834527)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2597355169) (.leaf 2526470892)) (.branch 25 (.leaf 2458064167) (.leaf 2392023900))) (.branch 28 (.branch 27 (.leaf 2328245022) (.leaf 2266628113)) (.branch 29 (.leaf 2207079054) (.leaf 2149508697)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2093832562) (.branch 32 (.leaf 2039970560) (.leaf 1987846725))) (.branch 35 (.branch 34 (.leaf 1937388971) (.leaf 1888528866)) (.branch 36 (.leaf 1841201415) (.leaf 1795344861)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1750900503) (.leaf 1707812516)) (.branch 40 (.leaf 1666027792) (.leaf 1625495785))) (.branch 43 (.branch 42 (.leaf 1586168372) (.leaf 1547999712)) (.branch 44 (.leaf 1510946125) (.leaf 1474965974))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1440019553) (.branch 47 (.leaf 1406068980) (.leaf 1373078105))) (.branch 50 (.branch 49 (.leaf 1341012414) (.leaf 1309838941)) (.branch 51 (.leaf 1279526193) (.leaf 1250044065)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1221363774) (.leaf 1193457789)) (.branch 55 (.leaf 1166299765) (.leaf 1139864487))) (.branch 58 (.branch 57 (.leaf 1114127808) (.leaf 1089066597)) (.branch 59 (.leaf 1064658692) (.leaf 1040882844))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1017718681) (.branch 62 (.leaf 995146658) (.leaf 973148020))) (.branch 65 (.branch 64 (.leaf 951704763) (.leaf 930799599)) (.branch 66 (.leaf 910415920) (.leaf 890537767)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 871149798) (.leaf 852237261)) (.branch 70 (.leaf 833785966) (.leaf 815782257))) (.branch 73 (.branch 72 (.leaf 798212991) (.leaf 781065512)) (.branch 74 (.leaf 764327628) (.leaf 747987595))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 732034090) (.branch 77 (.leaf 716456199) (.leaf 701243395))) (.branch 80 (.branch 79 (.leaf 686385521) (.leaf 671872777)) (.branch 81 (.leaf 657695699) (.leaf 643845153)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 630312313) (.leaf 617088650)) (.branch 85 (.leaf 604165924) (.leaf 591536166))) (.branch 88 (.branch 87 (.leaf 579191669) (.leaf 567124981)) (.branch 89 (.leaf 555328887) (.leaf 543796406)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 532520779) (.branch 92 (.leaf 521495461) (.leaf 510714109))) (.branch 95 (.branch 94 (.leaf 500170582) (.leaf 489858923)) (.branch 96 (.leaf 479773361) (.leaf 469908297)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 460258304) (.leaf 450818113)) (.branch 100 (.leaf 441582613) (.leaf 432546844))) (.branch 103 (.branch 102 (.leaf 423705989) (.leaf 415055371)) (.branch 104 (.leaf 406590447) (.leaf 398306804))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 390200153) (.leaf 382266328)) (.branch 108 (.leaf 374501276) (.leaf 366901058))) (.branch 111 (.branch 110 (.leaf 359461842) (.leaf 352179902)) (.branch 112 (.leaf 345051614) (.leaf 338073448)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 331241971) (.leaf 324553842)) (.branch 116 (.leaf 318005807) (.leaf 311594697))) (.branch 119 (.branch 118 (.leaf 305317426) (.leaf 299170988)) (.branch 120 (.leaf 293152455) (.leaf 287258974)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 443).prefactor = (602207936767149/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 443).cutoff/(generalMeanRows 443).c)).2 =
    (395518068812987/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 443).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 443).q*(generalMeanRows 443).c/2-2 = (3137/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable130.value]
  have hcontinuation : (generalMeanRows 443).q*(generalMeanRows 443).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable146.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 443).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 443).criticalRate j.val*(generalMeanRows 443).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 443).c*(generalMeanRows 443).criticalPoint j.val)).2-
      (generalMeanRows 443).J/2-(generalMeanRows 443).error (generalMeanGrid j.val)+
      (generalMeanRows 443).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 443).c)).2-
      (generalMeanRows 443).J/2-(generalMeanRows 443).error 4 := by
  have he : (generalMeanRows 443).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 443) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 443)
    (generalMeanRows_prefactorDomain 443) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0443

/-! Kernel-checked entropy margins for general spectral rectangle 444. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0444
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5245601884) (.branch 2 (.leaf 5070633277) (.leaf 4903527028))) (.branch 5 (.branch 4 (.leaf 4743829097) (.leaf 4591117751)) (.branch 6 (.leaf 4445000742) (.leaf 4305112795)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4171113345) (.leaf 4042684524)) (.branch 10 (.leaf 3919529332) (.leaf 3801369995))) (.branch 13 (.branch 12 (.leaf 3687946476) (.leaf 3579015129)) (.branch 14 (.leaf 3474347469) (.leaf 3373729055))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3276958476) (.branch 17 (.leaf 3183846416) (.leaf 3094214803))) (.branch 20 (.branch 19 (.leaf 3007896026) (.leaf 2924732221)) (.branch 21 (.leaf 2844574604) (.leaf 2767282872)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2692724632) (.leaf 2620774894)) (.branch 25 (.leaf 2551315582) (.leaf 2484235098))) (.branch 28 (.branch 27 (.leaf 2419427910) (.leaf 2356794170)) (.branch 29 (.leaf 2296239363) (.leaf 2237673975)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2181013193) (.branch 32 (.leaf 2126176615) (.leaf 2073087991))) (.branch 35 (.branch 34 (.leaf 2021674972) (.leaf 1971868883)) (.branch 36 (.leaf 1923604506) (.leaf 1876819878)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1831456109) (.leaf 1787457201)) (.branch 40 (.leaf 1744769884) (.leaf 1703343467))) (.branch 43 (.branch 42 (.leaf 1663129689) (.leaf 1624082585)) (.branch 44 (.leaf 1586158361) (.leaf 1549315274))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1513513518) (.branch 47 (.leaf 1478715126) (.leaf 1444883862))) (.branch 50 (.branch 49 (.leaf 1411985137) (.leaf 1379985916)) (.branch 51 (.leaf 1348854638) (.leaf 1318561140)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1289076584) (.leaf 1260373385)) (.branch 55 (.leaf 1232425152) (.leaf 1205206624))) (.branch 58 (.branch 57 (.leaf 1178693611) (.leaf 1152862946)) (.branch 59 (.leaf 1127692426) (.leaf 1103160769))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1079247570) (.branch 62 (.leaf 1055933252) (.leaf 1033199030))) (.branch 65 (.branch 64 (.leaf 1011026871) (.leaf 989399458)) (.branch 66 (.leaf 968300157) (.leaf 947712983)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 927622567) (.leaf 908014132)) (.branch 70 (.leaf 888873463) (.leaf 870186880))) (.branch 73 (.branch 72 (.leaf 851941215) (.leaf 834123786)) (.branch 74 (.leaf 816722379) (.leaf 799725222))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 783120971) (.branch 77 (.leaf 766898686) (.leaf 751047813))) (.branch 80 (.branch 79 (.leaf 735558171) (.leaf 720419933)) (.branch 81 (.leaf 705623612) (.leaf 691160044)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 677020377) (.leaf 663196056)) (.branch 85 (.leaf 649678811) (.leaf 636460647))) (.branch 88 (.branch 87 (.leaf 623533827) (.leaf 610890870)) (.branch 89 (.leaf 598524531) (.leaf 586427800)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 574593886) (.branch 92 (.leaf 563016212) (.leaf 551688407))) (.branch 95 (.branch 94 (.leaf 540604293) (.leaf 529757884)) (.branch 96 (.leaf 519143374) (.leaf 508755132)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 498587695) (.leaf 488635761)) (.branch 100 (.leaf 478894184) (.leaf 469357968))) (.branch 103 (.branch 102 (.leaf 460022260) (.leaf 450882347)) (.branch 104 (.leaf 441933650) (.leaf 433171719))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 424592229) (.leaf 416190973)) (.branch 108 (.leaf 407963862) (.leaf 399906918))) (.branch 111 (.branch 110 (.leaf 392016272) (.leaf 384288159)) (.branch 112 (.leaf 376718913) (.leaf 369304967)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 362042849) (.leaf 354929176)) (.branch 116 (.leaf 347960655) (.leaf 341134076))) (.branch 119 (.branch 118 (.leaf 334446314) (.leaf 327894322)) (.branch 120 (.leaf 321475130) (.leaf 315185845)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 444).prefactor = (2425285975595011/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 444).cutoff/(generalMeanRows 444).c)).2 =
    (100817511404327/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 444).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 444).q*(generalMeanRows 444).c/2-2 = (3051/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable153.value]
  have hcontinuation : (generalMeanRows 444).q*(generalMeanRows 444).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable146.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 444).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 444).criticalRate j.val*(generalMeanRows 444).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 444).c*(generalMeanRows 444).criticalPoint j.val)).2-
      (generalMeanRows 444).J/2-(generalMeanRows 444).error (generalMeanGrid j.val)+
      (generalMeanRows 444).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 444).c)).2-
      (generalMeanRows 444).J/2-(generalMeanRows 444).error 4 := by
  have he : (generalMeanRows 444).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 444) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 444)
    (generalMeanRows_prefactorDomain 444) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0444

/-! Kernel-checked entropy margins for general spectral rectangle 445. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0445
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5481264631) (.branch 2 (.leaf 5306637462) (.leaf 5139809876))) (.branch 5 (.branch 4 (.leaf 4980327706) (.leaf 4827769284)) (.branch 6 (.leaf 4681742606) (.leaf 4541882797)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4407849840) (.leaf 4279326539)) (.branch 10 (.leaf 4156016680) (.leaf 4037643379))) (.branch 13 (.branch 12 (.leaf 3923947578) (.leaf 3814686687)) (.branch 14 (.leaf 3709633346) (.leaf 3608574304))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3511309385) (.branch 17 (.leaf 3417650555) (.leaf 3327421060))) (.branch 20 (.branch 19 (.leaf 3240454639) (.leaf 3156594798)) (.branch 21 (.leaf 3075694147) (.leaf 2997613787)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2922222741) (.leaf 2849397437)) (.branch 25 (.leaf 2779021221) (.leaf 2710983916))) (.branch 28 (.branch 27 (.leaf 2645181404) (.leaf 2581515242)) (.branch 29 (.leaf 2519892313) (.leaf 2460224488)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2402428322) (.branch 32 (.leaf 2346424767) (.leaf 2292138909))) (.branch 35 (.branch 34 (.leaf 2239499715) (.leaf 2188439806)) (.branch 36 (.leaf 2138895236) (.leaf 2090805298)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2044112327) (.leaf 1998761530)) (.branch 40 (.leaf 1954700819) (.leaf 1911880655))) (.branch 43 (.branch 42 (.leaf 1870253909) (.leaf 1829775719)) (.branch 44 (.leaf 1790403370) (.leaf 1752096170))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1714815341) (.branch 47 (.leaf 1678523915) (.leaf 1643186632))) (.branch 50 (.branch 49 (.leaf 1608769849) (.leaf 1575241455)) (.branch 51 (.leaf 1542570786) (.leaf 1510728553)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1479686762) (.leaf 1449418651)) (.branch 55 (.leaf 1419898628) (.leaf 1391102204))) (.branch 58 (.branch 57 (.leaf 1363005940) (.leaf 1335587394)) (.branch 59 (.leaf 1308825067) (.leaf 1282698359))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1257187521) (.branch 62 (.leaf 1232273614) (.leaf 1207938467))) (.branch 65 (.branch 64 (.leaf 1184164643) (.leaf 1160935398)) (.branch 66 (.leaf 1138234651) (.leaf 1116046949)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1094357442) (.leaf 1073151845)) (.branch 70 (.leaf 1052416422) (.leaf 1032137952))) (.branch 73 (.branch 72 (.leaf 1012303708) (.leaf 992901435)) (.branch 74 (.leaf 973919325) (.leaf 955345999))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 937170489) (.branch 77 (.leaf 919382214) (.leaf 901970967))) (.branch 80 (.branch 79 (.leaf 884926899) (.leaf 868240498)) (.branch 81 (.leaf 851902581) (.leaf 835904272)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 820236997) (.leaf 804892464)) (.branch 85 (.leaf 789862655) (.leaf 775139813))) (.branch 88 (.branch 87 (.leaf 760716430) (.leaf 746585240)) (.branch 89 (.leaf 732739205) (.leaf 719171508)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 705875545) (.branch 92 (.leaf 692844911) (.leaf 680073401))) (.branch 95 (.branch 94 (.leaf 667554992) (.leaf 655283845)) (.branch 96 (.leaf 643254290) (.leaf 631460826)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 619898110) (.leaf 608560952)) (.branch 100 (.leaf 597444312) (.leaf 586543291))) (.branch 103 (.branch 102 (.leaf 575853126) (.leaf 565369188)) (.branch 104 (.leaf 555086973) (.leaf 545002101))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 535110309) (.leaf 525407450)) (.branch 108 (.leaf 515889485) (.leaf 506552483))) (.branch 111 (.branch 110 (.leaf 497392613) (.leaf 488406145)) (.branch 112 (.leaf 479589445) (.leaf 470938970)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 462451267) (.leaf 454122969)) (.branch 116 (.leaf 445950794) (.leaf 437931539))) (.branch 119 (.branch 118 (.leaf 430062082) (.leaf 422339374)) (.branch 120 (.leaf 414760442) (.leaf 407322381)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 445).prefactor = (2422159273878189/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 445).cutoff/(generalMeanRows 445).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 445).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 445).q*(generalMeanRows 445).c/2-2 = (2793/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable128.value]
  have hcontinuation : (generalMeanRows 445).q*(generalMeanRows 445).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable148.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 445).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 445).criticalRate j.val*(generalMeanRows 445).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 445).c*(generalMeanRows 445).criticalPoint j.val)).2-
      (generalMeanRows 445).J/2-(generalMeanRows 445).error (generalMeanGrid j.val)+
      (generalMeanRows 445).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 445).c)).2-
      (generalMeanRows 445).J/2-(generalMeanRows 445).error 4 := by
  have he : (generalMeanRows 445).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 445) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 445)
    (generalMeanRows_prefactorDomain 445) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0445

/-! Kernel-checked entropy margins for general spectral rectangle 446. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0446
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5151065399) (.branch 2 (.leaf 4964178580) (.leaf 4785857481))) (.branch 5 (.branch 4 (.leaf 4615612474) (.leaf 4452988412)) (.branch 6 (.leaf 4297561627) (.leaf 4148937251)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4006746809) (.leaf 3870646073)) (.branch 10 (.leaf 3740313123) (.leaf 3615446594))) (.branch 13 (.branch 12 (.leaf 3495764098) (.leaf 3381000786)) (.branch 14 (.leaf 3270908050) (.leaf 3165252331))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3063814039) (.branch 17 (.leaf 2966386565) (.leaf 2872775370))) (.branch 20 (.branch 19 (.leaf 2782797160) (.leaf 2696279121)) (.branch 21 (.leaf 2613058216) (.leaf 2532980538)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2455900716) (.leaf 2381681361)) (.branch 25 (.leaf 2310192561) (.leaf 2241311402))) (.branch 28 (.branch 27 (.leaf 2174921539) (.leaf 2110912786)) (.branch 29 (.leaf 2049180738) (.leaf 1989626425)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1932155982) (.branch 32 (.leaf 1876680349) (.leaf 1823114986))) (.branch 35 (.branch 34 (.leaf 1771379607) (.leaf 1721397941)) (.branch 36 (.leaf 1673097492) (.leaf 1626409331)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1581267894) (.leaf 1537610790)) (.branch 40 (.leaf 1495378626) (.leaf 1454514843))) (.branch 43 (.branch 42 (.leaf 1414965561) (.leaf 1376679430)) (.branch 44 (.leaf 1339607496) (.leaf 1303703072))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1268921619) (.branch 47 (.leaf 1235220628) (.leaf 1202559517))) (.branch 50 (.branch 49 (.leaf 1170899530) (.leaf 1140203642)) (.branch 51 (.leaf 1110436469) (.leaf 1081564184)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1053554440) (.leaf 1026376293)) (.branch 55 (.leaf 1000000131) (.leaf 974397612))) (.branch 58 (.branch 57 (.leaf 949541594) (.leaf 925406083)) (.branch 59 (.leaf 901966171) (.leaf 879197986))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 857078643) (.branch 62 (.leaf 835586195) (.leaf 814699585))) (.branch 65 (.branch 64 (.leaf 794398610) (.leaf 774663876)) (.branch 66 (.leaf 755476764) (.leaf 736819387)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 718674565) (.leaf 701025786)) (.branch 70 (.leaf 683857176) (.leaf 667153473))) (.branch 73 (.branch 72 (.leaf 650899998) (.leaf 635082627)) (.branch 74 (.leaf 619687767) (.leaf 604702336))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 590113734) (.branch 77 (.leaf 575909826) (.leaf 562078923))) (.branch 80 (.branch 79 (.leaf 548609759) (.leaf 535491473)) (.branch 81 (.leaf 522713597) (.leaf 510266032)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 498139036) (.leaf 486323211)) (.branch 85 (.leaf 474809484) (.leaf 463589098))) (.branch 88 (.branch 87 (.leaf 452653594) (.leaf 441994806)) (.branch 89 (.leaf 431604841) (.leaf 421476074)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 411601134) (.branch 92 (.leaf 401972894) (.leaf 392584465))) (.branch 95 (.branch 94 (.leaf 383429181) (.leaf 374500595)) (.branch 96 (.leaf 365792468) (.leaf 357298760)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 349013628) (.leaf 340931409)) (.branch 100 (.leaf 333046624) (.leaf 325353961))) (.branch 103 (.branch 102 (.leaf 317848277) (.leaf 310524587)) (.branch 104 (.leaf 303378059) (.leaf 296404008))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 289597893) (.leaf 282955310)) (.branch 108 (.leaf 276471987) (.leaf 270143779))) (.branch 111 (.branch 110 (.leaf 263966666) (.leaf 257936743)) (.branch 112 (.leaf 252050223) (.leaf 246303430)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 240692791) (.leaf 235214840)) (.branch 116 (.leaf 229866209) (.leaf 224643626))) (.branch 119 (.branch 118 (.leaf 219543913) (.leaf 214563980)) (.branch 120 (.leaf 209700827) (.leaf 204951535)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 446).prefactor = (2589379920427433/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 446).cutoff/(generalMeanRows 446).c)).2 =
    (347341734459821/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 446).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 446).q*(generalMeanRows 446).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 446).q*(generalMeanRows 446).cutoff/2-2 = (1054/507:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable144.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 446).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 446).criticalRate j.val*(generalMeanRows 446).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 446).c*(generalMeanRows 446).criticalPoint j.val)).2-
      (generalMeanRows 446).J/2-(generalMeanRows 446).error (generalMeanGrid j.val)+
      (generalMeanRows 446).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 446).c)).2-
      (generalMeanRows 446).J/2-(generalMeanRows 446).error 4 := by
  have he : (generalMeanRows 446).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 446) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 446)
    (generalMeanRows_prefactorDomain 446) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0446

/-! Kernel-checked entropy margins for general spectral rectangle 447. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0447
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5372948650) (.branch 2 (.leaf 5196389674) (.leaf 5027737214))) (.branch 5 (.branch 4 (.leaf 4866534217) (.leaf 4712356178)) (.branch 6 (.leaf 4564808304) (.leaf 4423522973)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4288157464) (.leaf 4158391920)) (.branch 10 (.leaf 4033927507) (.leaf 3914484761))) (.branch 13 (.branch 12 (.leaf 3799802088) (.leaf 3689634401)) (.branch 14 (.leaf 3583751889) (.leaf 3481938887))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3383992852) (.branch 17 (.leaf 3289723426) (.leaf 3198951571))) (.branch 20 (.branch 19 (.leaf 3111508790) (.leaf 3027236396)) (.branch 21 (.leaf 2945984849) (.leaf 2867613147)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2791988253) (.leaf 2718984582)) (.branch 25 (.leaf 2648483510) (.leaf 2580372935))) (.branch 28 (.branch 27 (.leaf 2514546859) (.leaf 2450905006)) (.branch 29 (.leaf 2389352465) (.leaf 2329799362)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2272160547) (.branch 32 (.leaf 2216355313) (.leaf 2162307128))) (.branch 35 (.branch 34 (.leaf 2109943385) (.leaf 2059195170)) (.branch 36 (.leaf 2009997046) (.leaf 1962286854)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1916005519) (.leaf 1871096875)) (.branch 40 (.leaf 1827507501) (.leaf 1785186564))) (.branch 43 (.branch 42 (.leaf 1744085676) (.leaf 1704158756)) (.branch 44 (.leaf 1665361903) (.leaf 1627653276))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1590992984) (.branch 47 (.leaf 1555342976) (.leaf 1520666944))) (.branch 50 (.branch 49 (.leaf 1486930233) (.leaf 1454099745)) (.branch 51 (.leaf 1422143867) (.leaf 1391032385)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1360736413) (.leaf 1331228327)) (.branch 55 (.leaf 1302481696) (.leaf 1274471226))) (.branch 58 (.branch 57 (.leaf 1247172695) (.leaf 1220562906)) (.branch 59 (.leaf 1194619630) (.leaf 1169321562))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1144648271) (.branch 62 (.leaf 1120580160) (.leaf 1097098425))) (.branch 65 (.branch 64 (.leaf 1074185014) (.leaf 1051822592)) (.branch 66 (.leaf 1029994508) (.leaf 1008684761)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 987877967) (.leaf 967559333)) (.branch 70 (.leaf 947714629) (.leaf 928330161))) (.branch 73 (.branch 72 (.leaf 909392745) (.leaf 890889686)) (.branch 74 (.leaf 872808754) (.leaf 855138163))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 837866553) (.branch 77 (.leaf 820982968) (.leaf 804476840))) (.branch 80 (.branch 79 (.leaf 788337970) (.leaf 772556517)) (.branch 81 (.leaf 757122973) (.leaf 742028160)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 727263206) (.leaf 712819538)) (.branch 85 (.leaf 698688868) (.leaf 684863179))) (.branch 88 (.branch 87 (.leaf 671334715) (.leaf 658095974)) (.branch 89 (.leaf 645139689) (.leaf 632458828)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 620046578) (.branch 92 (.leaf 607896338) (.leaf 596001712))) (.branch 95 (.branch 94 (.leaf 584356500) (.leaf 572954689)) (.branch 96 (.leaf 561790447) (.leaf 550858117)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 540152209) (.leaf 529667393)) (.branch 100 (.leaf 519398496) (.leaf 509340493))) (.branch 103 (.branch 102 (.leaf 499488501) (.leaf 489837778)) (.branch 104 (.leaf 480383715) (.leaf 471121830))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 462047768) (.leaf 453157290)) (.branch 108 (.leaf 444446275) (.leaf 435910712))) (.branch 111 (.branch 110 (.leaf 427546700) (.leaf 419350438)) (.branch 112 (.leaf 411318229) (.leaf 403446471)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 395731658) (.leaf 388170371)) (.branch 116 (.leaf 380759282) (.leaf 373495146))) (.branch 119 (.branch 118 (.leaf 366374802) (.leaf 359395167)) (.branch 120 (.leaf 352553235) (.leaf 345846076)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 447).prefactor = (4883705199066643/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 447).cutoff/(generalMeanRows 447).c)).2 =
    (411082585354099/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 447).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 447).q*(generalMeanRows 447).c/2-2 = (593/800:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable154.value]
  have hcontinuation : (generalMeanRows 447).q*(generalMeanRows 447).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable146.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 447).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 447).criticalRate j.val*(generalMeanRows 447).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 447).c*(generalMeanRows 447).criticalPoint j.val)).2-
      (generalMeanRows 447).J/2-(generalMeanRows 447).error (generalMeanGrid j.val)+
      (generalMeanRows 447).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 447).c)).2-
      (generalMeanRows 447).J/2-(generalMeanRows 447).error 4 := by
  have he : (generalMeanRows 447).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 447) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 447)
    (generalMeanRows_prefactorDomain 447) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0447

/-! Kernel-checked entropy margins for general spectral rectangle 448. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0448
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5503886046) (.branch 2 (.leaf 5325762790) (.leaf 5155589995))) (.branch 5 (.branch 4 (.leaf 4992907540) (.leaf 4837288104)) (.branch 6 (.leaf 4688334303) (.leaf 4545676131)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4408968671) (.leaf 4277890045)) (.branch 10 (.leaf 4152139554) (.leaf 4031436017))) (.branch 13 (.branch 12 (.leaf 3915516254) (.leaf 3804133717)) (.branch 14 (.leaf 3697057247) (.leaf 3594069934))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3494968088) (.branch 17 (.leaf 3399560291) (.leaf 3307666529))) (.branch 20 (.branch 19 (.leaf 3219117404) (.leaf 3133753397)) (.branch 21 (.leaf 3051424204) (.leaf 2971988113)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2895311439) (.leaf 2821267996)) (.branch 25 (.leaf 2749738608) (.leaf 2680610666))) (.branch 28 (.branch 27 (.leaf 2613777704) (.leaf 2549139016)) (.branch 29 (.leaf 2486599297) (.leaf 2426068309)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2367460571) (.branch 32 (.leaf 2310695072) (.leaf 2255695000))) (.branch 35 (.branch 34 (.leaf 2202387491) (.leaf 2150703399)) (.branch 36 (.leaf 2100577075) (.leaf 2051946164)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2004751412) (.leaf 1958936495)) (.branch 40 (.leaf 1914447843) (.leaf 1871234491))) (.branch 43 (.branch 42 (.leaf 1829247930) (.leaf 1788441970)) (.branch 44 (.leaf 1748772611) (.leaf 1710197925))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1672677938) (.branch 47 (.leaf 1636174529) (.leaf 1600651326))) (.branch 50 (.branch 49 (.leaf 1566073614) (.leaf 1532408247)) (.branch 51 (.leaf 1499623564) (.leaf 1467689310)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1436576564) (.leaf 1406257671)) (.branch 55 (.leaf 1376706171) (.leaf 1347896744))) (.branch 58 (.branch 57 (.leaf 1319805148) (.leaf 1292408167)) (.branch 59 (.leaf 1265683555) (.leaf 1239609993))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1214167037) (.branch 62 (.leaf 1189335079) (.leaf 1165095306))) (.branch 65 (.branch 64 (.leaf 1141429657) (.leaf 1118320791)) (.branch 66 (.leaf 1095752048) (.leaf 1073707422)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1052171525) (.leaf 1031129558)) (.branch 70 (.leaf 1010567285) (.leaf 990471009))) (.branch 73 (.branch 72 (.leaf 970827540) (.leaf 951624179)) (.branch 74 (.leaf 932848690) (.leaf 914489284))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 896534594) (.branch 77 (.leaf 878973658) (.leaf 861795902))) (.branch 80 (.branch 79 (.leaf 844991122) (.leaf 828549467)) (.branch 81 (.leaf 812461424) (.leaf 796717805)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 781309729) (.leaf 766228614)) (.branch 85 (.leaf 751466161) (.leaf 737014343))) (.branch 88 (.branch 87 (.leaf 722865392) (.leaf 709011793)) (.branch 89 (.leaf 695446267) (.leaf 682161767)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 669151467) (.branch 92 (.leaf 656408749) (.leaf 643927203))) (.branch 95 (.branch 94 (.leaf 631700610) (.leaf 619722941)) (.branch 96 (.leaf 607988345) (.leaf 596491148)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 585225839) (.leaf 574187068)) (.branch 100 (.leaf 563369641) (.leaf 552768511))) (.branch 103 (.branch 102 (.leaf 542378773) (.leaf 532195663)) (.branch 104 (.leaf 522214548) (.leaf 512430921))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 502840403) (.leaf 493438729)) (.branch 108 (.leaf 484221753) (.leaf 475185438))) (.branch 111 (.branch 110 (.leaf 466325854) (.leaf 457639175)) (.branch 112 (.leaf 449121674) (.leaf 440769722)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 432579782) (.leaf 424548407)) (.branch 116 (.leaf 416672240) (.leaf 408948004))) (.branch 119 (.branch 118 (.leaf 401372509) (.leaf 393942639)) (.branch 120 (.leaf 386655359) (.leaf 379507704)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 448).prefactor = (491706477326641/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 448).cutoff/(generalMeanRows 448).c)).2 =
    (209478320892503/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 448).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 448).q*(generalMeanRows 448).c/2-2 = (2879/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable152.value]
  have hcontinuation : (generalMeanRows 448).q*(generalMeanRows 448).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable146.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 448).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 448).criticalRate j.val*(generalMeanRows 448).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 448).c*(generalMeanRows 448).criticalPoint j.val)).2-
      (generalMeanRows 448).J/2-(generalMeanRows 448).error (generalMeanGrid j.val)+
      (generalMeanRows 448).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 448).c)).2-
      (generalMeanRows 448).J/2-(generalMeanRows 448).error 4 := by
  have he : (generalMeanRows 448).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 448) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 448)
    (generalMeanRows_prefactorDomain 448) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0448

/-! Kernel-checked entropy margins for general spectral rectangle 449. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0449
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5323247767) (.branch 2 (.leaf 5153184824) (.leaf 4990689894))) (.branch 5 (.branch 4 (.leaf 4835323991) (.leaf 4686679495)) (.branch 6 (.leaf 4544377409) (.leaf 4408064915)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4277413182) (.leaf 4152115401)) (.branch 10 (.leaf 4031885013) (.leaf 3916454110))) (.branch 13 (.branch 12 (.leaf 3805571990) (.leaf 3699003843)) (.branch 14 (.leaf 3596529561) (.leaf 3497942651))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3403049243) (.branch 17 (.leaf 3311667190) (.leaf 3223625233))) (.branch 20 (.branch 19 (.leaf 3138762244) (.leaf 3056926528)) (.branch 21 (.leaf 2977975183) (.leaf 2901773504)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2828194442) (.leaf 2757118101)) (.branch 25 (.leaf 2688431269) (.leaf 2622026991))) (.branch 28 (.branch 27 (.leaf 2557804171) (.leaf 2495667198)) (.branch 29 (.leaf 2435525608) (.leaf 2377293762)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2320890550) (.branch 32 (.leaf 2266239117) (.leaf 2213266604))) (.branch 35 (.branch 34 (.leaf 2161903910) (.leaf 2112085469)) (.branch 36 (.leaf 2063749041) (.leaf 2016835516)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1971288737) (.leaf 1927055324)) (.branch 40 (.leaf 1884084518) (.leaf 1842328034))) (.branch 43 (.branch 42 (.leaf 1801739917) (.leaf 1762276414)) (.branch 44 (.leaf 1723895853) (.leaf 1686558524))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1650226573) (.branch 47 (.leaf 1614863903) (.leaf 1580436075))) (.branch 50 (.branch 49 (.leaf 1546910221) (.leaf 1514254960)) (.branch 51 (.leaf 1482440317) (.leaf 1451437650)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1421219580) (.leaf 1391759925)) (.branch 55 (.leaf 1363033637) (.leaf 1335016745))) (.branch 58 (.branch 57 (.leaf 1307686299) (.leaf 1281020318)) (.branch 59 (.leaf 1254997740) (.leaf 1229598378))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1204802875) (.branch 62 (.leaf 1180592663) (.leaf 1156949922))) (.branch 65 (.branch 64 (.leaf 1133857547) (.leaf 1111299110)) (.branch 66 (.leaf 1089258831) (.leaf 1067721542)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1046672660) (.leaf 1026098162)) (.branch 70 (.leaf 1005984552) (.leaf 986318843))) (.branch 73 (.branch 72 (.leaf 967088531) (.leaf 948281569)) (.branch 74 (.leaf 929886352) (.leaf 911891694))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 894286808) (.branch 77 (.leaf 877061289) (.leaf 860205097))) (.branch 80 (.branch 79 (.leaf 843708542) (.leaf 827562268)) (.branch 81 (.leaf 811757236) (.leaf 796284712)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 781136256) (.leaf 766303707)) (.branch 85 (.leaf 751779171) (.leaf 737555010))) (.branch 88 (.branch 87 (.leaf 723623832) (.leaf 709978482)) (.branch 89 (.leaf 696612029) (.leaf 683517760)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 670689169) (.branch 92 (.leaf 658119949) (.leaf 645803987))) (.branch 95 (.branch 94 (.leaf 633735351) (.leaf 621908289)) (.branch 96 (.leaf 610317216) (.leaf 598956713)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 587821516) (.leaf 576906515)) (.branch 100 (.leaf 566206743) (.leaf 555717374))) (.branch 103 (.branch 102 (.leaf 545433719) (.leaf 535351216)) (.branch 104 (.leaf 525465430) (.leaf 515772048))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 506266871) (.leaf 496945815)) (.branch 108 (.leaf 487804903) (.leaf 478840264))) (.branch 111 (.branch 110 (.leaf 470048127) (.leaf 461424820)) (.branch 112 (.leaf 452966765) (.leaf 444670476)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 436532553) (.leaf 428549685)) (.branch 116 (.leaf 420718641) (.leaf 413036271))) (.branch 119 (.branch 118 (.leaf 405499503) (.leaf 398105338)) (.branch 120 (.leaf 390850852) (.leaf 383733190)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 449).prefactor = (58954414151269/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 449).cutoff/(generalMeanRows 449).c)).2 =
    (106799093155119/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 449).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 449).q*(generalMeanRows 449).c/2-2 = (227/320:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable159.value]
  have hcontinuation : (generalMeanRows 449).q*(generalMeanRows 449).cutoff/2-2 = (3314/1539:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable165.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 449).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 449).criticalRate j.val*(generalMeanRows 449).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 449).c*(generalMeanRows 449).criticalPoint j.val)).2-
      (generalMeanRows 449).J/2-(generalMeanRows 449).error (generalMeanGrid j.val)+
      (generalMeanRows 449).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 449).c)).2-
      (generalMeanRows 449).J/2-(generalMeanRows 449).error 4 := by
  have he : (generalMeanRows 449).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 449) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 449)
    (generalMeanRows_prefactorDomain 449) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0449

/-! Kernel-checked entropy margins for general spectral rectangle 450. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0450
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5061824339) (.branch 2 (.leaf 4885670308) (.leaf 4717490966))) (.branch 5 (.branch 4 (.leaf 4556828984) (.leaf 4403259389)) (.branch 6 (.leaf 4256386748) (.leaf 4115842645)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3981283428) (.leaf 3852388185)) (.branch 10 (.leaf 3728856922) (.leaf 3610408917))) (.branch 13 (.branch 12 (.leaf 3496781236) (.leaf 3387727381)) (.branch 14 (.leaf 3283016068) (.leaf 3182430105))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3085765381) (.branch 17 (.leaf 2992829929) (.leaf 2903443080))) (.branch 20 (.branch 19 (.leaf 2817434677) (.leaf 2734644362)) (.branch 21 (.leaf 2654920910) (.leaf 2578121627)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2504111789) (.leaf 2432764118)) (.branch 25 (.leaf 2363958312) (.leaf 2297580596))) (.branch 28 (.branch 27 (.leaf 2233523313) (.leaf 2171684544)) (.branch 29 (.leaf 2111967754) (.leaf 2054281462)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1998538939) (.branch 32 (.leaf 1944657918) (.leaf 1892560336))) (.branch 35 (.branch 34 (.leaf 1842172077) (.leaf 1793422753)) (.branch 36 (.leaf 1746245477) (.leaf 1700576669)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1656355868) (.leaf 1613525549)) (.branch 40 (.leaf 1572030966) (.leaf 1531819991))) (.branch 43 (.branch 42 (.leaf 1492842975) (.leaf 1455052605)) (.branch 44 (.leaf 1418403784) (.leaf 1382853506))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1348360745) (.branch 47 (.leaf 1314886350) (.leaf 1282392945))) (.branch 50 (.branch 49 (.leaf 1250844835) (.leaf 1220207919)) (.branch 51 (.leaf 1190449607) (.leaf 1161538740)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1133445519) (.leaf 1106141437)) (.branch 55 (.leaf 1079599208) (.leaf 1053792711))) (.branch 58 (.branch 57 (.leaf 1028696928) (.leaf 1004287893)) (.branch 59 (.leaf 980542636) (.leaf 957439136))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 934956276) (.branch 62 (.leaf 913073796) (.leaf 891772255))) (.branch 65 (.branch 64 (.leaf 871032990) (.leaf 850838079)) (.branch 66 (.leaf 831170307) (.leaf 812013130)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 793350649) (.leaf 775167574)) (.branch 70 (.leaf 757449202) (.leaf 740181383))) (.branch 73 (.branch 72 (.leaf 723350502) (.leaf 706943451)) (.branch 74 (.leaf 690947607) (.leaf 675350808))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 660141337) (.branch 77 (.leaf 645307902) (.leaf 630839611))) (.branch 80 (.branch 79 (.leaf 616725964) (.leaf 602956828)) (.branch 81 (.leaf 589522426) (.leaf 576413322)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 563620403) (.leaf 551134868)) (.branch 85 (.leaf 538948214) (.leaf 527052228))) (.branch 88 (.branch 87 (.leaf 515438965) (.leaf 504100750)) (.branch 89 (.leaf 493030155) (.leaf 482219997)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 471663327) (.branch 92 (.leaf 461353417) (.leaf 451283754))) (.branch 95 (.branch 94 (.leaf 441448034) (.leaf 431840147)) (.branch 96 (.leaf 422454177) (.leaf 413284390)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 404325230) (.leaf 395571307)) (.branch 100 (.leaf 387017398) (.leaf 378658437))) (.branch 103 (.branch 102 (.leaf 370489508) (.leaf 362505841)) (.branch 104 (.leaf 354702808) (.leaf 347075917))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 339620803) (.leaf 332333232)) (.branch 108 (.leaf 325209089) (.leaf 318244377))) (.branch 111 (.branch 110 (.leaf 311435212) (.leaf 304777819)) (.branch 112 (.leaf 298268530) (.leaf 291903779)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 285680097) (.leaf 279594111)) (.branch 116 (.leaf 273642542) (.leaf 267822198))) (.branch 119 (.branch 118 (.leaf 262129974) (.leaf 256562849)) (.branch 120 (.leaf 251117880) (.leaf 245792206)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 450).prefactor = (4890546907568019/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 450).cutoff/(generalMeanRows 450).c)).2 =
    (74865395776473/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 450).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 450).q*(generalMeanRows 450).c/2-2 = (3309/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable134.value]
  have hcontinuation : (generalMeanRows 450).q*(generalMeanRows 450).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable151.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 450).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 450).criticalRate j.val*(generalMeanRows 450).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 450).c*(generalMeanRows 450).criticalPoint j.val)).2-
      (generalMeanRows 450).J/2-(generalMeanRows 450).error (generalMeanGrid j.val)+
      (generalMeanRows 450).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 450).c)).2-
      (generalMeanRows 450).J/2-(generalMeanRows 450).error 4 := by
  have he : (generalMeanRows 450).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 450) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 450)
    (generalMeanRows_prefactorDomain 450) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0450

/-! Kernel-checked entropy margins for general spectral rectangle 451. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0451
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5044139452) (.branch 2 (.leaf 4873114288) (.leaf 4709777463))) (.branch 5 (.branch 4 (.leaf 4553686940) (.leaf 4404432057)) (.branch 6 (.leaf 4261630787) (.leaf 4124927290)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3993989731) (.leaf 3868508313)) (.branch 10 (.leaf 3748193510) (.leaf 3632774470))) (.branch 13 (.branch 12 (.leaf 3521997571) (.leaf 3415625113)) (.branch 14 (.leaf 3313434127) (.leaf 3215215292))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3120771946) (.branch 17 (.leaf 3029919186) (.leaf 2942483036))) (.branch 20 (.branch 19 (.leaf 2858299693) (.leaf 2777214828)) (.branch 21 (.leaf 2699082947) (.leaf 2623766800)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2551136838) (.leaf 2481070711)) (.branch 25 (.leaf 2413452801) (.leaf 2348173796))) (.branch 28 (.branch 27 (.leaf 2285130290) (.leaf 2224224411)) (.branch 29 (.leaf 2165363485) (.leaf 2108459709)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2053429863) (.branch 32 (.leaf 2000195027) (.leaf 1948680331))) (.branch 35 (.branch 34 (.leaf 1898814708) (.leaf 1850530676)) (.branch 36 (.leaf 1803764130) (.leaf 1758454141)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1714542781) (.leaf 1671974946)) (.branch 40 (.leaf 1630698203) (.leaf 1590662635))) (.branch 43 (.branch 42 (.leaf 1551820703) (.leaf 1514127115)) (.branch 44 (.leaf 1477538703) (.leaf 1442014306))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1407514663) (.branch 47 (.leaf 1374002309) (.leaf 1341441481))) (.branch 50 (.branch 49 (.leaf 1309798028) (.leaf 1279039324)) (.branch 51 (.leaf 1249134189) (.leaf 1220052815)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1191766695) (.leaf 1164248555)) (.branch 55 (.leaf 1137472291) (.leaf 1111412912))) (.branch 58 (.branch 57 (.leaf 1086046481) (.leaf 1061350065)) (.branch 59 (.leaf 1037301684) (.leaf 1013880262))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 991065586) (.branch 62 (.leaf 968838263) (.leaf 947179678))) (.branch 65 (.branch 64 (.leaf 926071959) (.leaf 905497941)) (.branch 66 (.leaf 885441132) (.leaf 865885681)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 846816348) (.leaf 828218477)) (.branch 70 (.leaf 810077967) (.leaf 792381247))) (.branch 73 (.branch 72 (.leaf 775115252) (.leaf 758267402)) (.branch 74 (.leaf 741825575) (.leaf 725778093))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 710113696) (.branch 77 (.leaf 694821529) (.leaf 679891121))) (.branch 80 (.branch 79 (.leaf 665312368) (.leaf 651075521)) (.branch 81 (.leaf 637171164) (.leaf 623590206)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 610323866) (.leaf 597363658)) (.branch 85 (.leaf 584701378) (.leaf 572329097))) (.branch 88 (.branch 87 (.leaf 560239144) (.leaf 548424100)) (.branch 89 (.leaf 536876785) (.leaf 525590250)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 514557767) (.branch 92 (.leaf 503772819) (.leaf 493229095))) (.branch 95 (.branch 94 (.leaf 482920479) (.leaf 472841044)) (.branch 96 (.leaf 462985044) (.leaf 453346906)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 443921228) (.leaf 434702767)) (.branch 100 (.leaf 425686434) (.leaf 416867294))) (.branch 103 (.branch 102 (.leaf 408240553) (.leaf 399801557)) (.branch 104 (.leaf 391545785) (.leaf 383468846))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 375566474) (.leaf 367834522)) (.branch 108 (.leaf 360268961) (.leaf 352865871))) (.branch 111 (.branch 110 (.leaf 345621442) (.leaf 338531969)) (.branch 112 (.leaf 331593846) (.leaf 324803565)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 318157715) (.leaf 311652972)) (.branch 116 (.leaf 305286102) (.leaf 299053957))) (.branch 119 (.branch 118 (.leaf 292953471) (.leaf 286981657)) (.branch 120 (.leaf 281135606) (.leaf 275412485)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 451).prefactor = (4753811337606229/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 451).cutoff/(generalMeanRows 451).c)).2 =
    (78094993058069/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 451).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 451).q*(generalMeanRows 451).c/2-2 = (1271/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable168.value]
  have hcontinuation : (generalMeanRows 451).q*(generalMeanRows 451).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable160.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 451).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 451).criticalRate j.val*(generalMeanRows 451).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 451).c*(generalMeanRows 451).criticalPoint j.val)).2-
      (generalMeanRows 451).J/2-(generalMeanRows 451).error (generalMeanGrid j.val)+
      (generalMeanRows 451).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 451).c)).2-
      (generalMeanRows 451).J/2-(generalMeanRows 451).error 4 := by
  have he : (generalMeanRows 451).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 451) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 451)
    (generalMeanRows_prefactorDomain 451) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0451

/-! Kernel-checked entropy margins for general spectral rectangle 452. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0452
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5165210930) (.branch 2 (.leaf 4992584414) (.leaf 4827689664))) (.branch 5 (.branch 4 (.leaf 4670081777) (.leaf 4519347458)) (.branch 6 (.leaf 4375102255) (.leaf 4236988104)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4104671115) (.leaf 3977839602)) (.branch 10 (.leaf 3856202297) (.leaf 3739486739))) (.branch 13 (.branch 12 (.leaf 3627437824) (.leaf 3519816483)) (.branch 14 (.leaf 3416398485) (.leaf 3316973341))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3221343314) (.branch 17 (.leaf 3129322502) (.leaf 3040736013))) (.branch 20 (.branch 19 (.leaf 2955419193) (.leaf 2873216928)) (.branch 21 (.leaf 2793982999) (.leaf 2717579487)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2643876223) (.leaf 2572750285)) (.branch 25 (.leaf 2504085527) (.leaf 2437772150))) (.branch 28 (.branch 27 (.leaf 2373706294) (.leaf 2311789675)) (.branch 29 (.leaf 2251929232) (.leaf 2194036808)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2138028855) (.branch 32 (.leaf 2083826152) (.leaf 2031353547))) (.branch 35 (.branch 34 (.leaf 1980539718) (.leaf 1931316946)) (.branch 36 (.leaf 1883620905) (.leaf 1837390464)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1792567509) (.leaf 1749096765)) (.branch 40 (.leaf 1706925637) (.leaf 1666004064))) (.branch 43 (.branch 42 (.leaf 1626284370) (.leaf 1587721140)) (.branch 44 (.leaf 1550271090) (.leaf 1513892951))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1478547364) (.branch 47 (.leaf 1444196774) (.leaf 1410805332))) (.branch 50 (.branch 49 (.leaf 1378338809) (.leaf 1346764505)) (.branch 51 (.leaf 1316051175) (.leaf 1286168946)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1257089252) (.leaf 1228784765)) (.branch 55 (.leaf 1201229328) (.leaf 1174397903))) (.branch 58 (.branch 57 (.leaf 1148266506) (.leaf 1122812161)) (.branch 59 (.leaf 1098012847) (.leaf 1073847449))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1050295718) (.branch 62 (.leaf 1027338222) (.leaf 1004956315))) (.branch 65 (.branch 64 (.leaf 983132089) (.leaf 961848348)) (.branch 66 (.leaf 941088568) (.leaf 920836868)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 901077977) (.leaf 881797209)) (.branch 70 (.leaf 862980434) (.leaf 844614052))) (.branch 73 (.branch 72 (.leaf 826684969) (.leaf 809180575)) (.branch 74 (.leaf 792088721) (.leaf 775397699))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 759096220) (.branch 77 (.leaf 743173400) (.leaf 727618738))) (.branch 80 (.branch 79 (.leaf 712422101) (.leaf 697573709)) (.branch 81 (.leaf 683064118) (.leaf 668884205)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 655025158) (.leaf 641478459)) (.branch 85 (.leaf 628235874) (.leaf 615289441))) (.branch 88 (.branch 87 (.leaf 602631457) (.leaf 590254469)) (.branch 89 (.leaf 578151265) (.leaf 566314861)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 554738495) (.branch 92 (.leaf 543415616) (.leaf 532339878))) (.branch 95 (.branch 94 (.leaf 521505129) (.leaf 510905406)) (.branch 96 (.leaf 500534927) (.leaf 490388083)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 480459433) (.leaf 470743697)) (.branch 100 (.leaf 461235750) (.leaf 451930617))) (.branch 103 (.branch 102 (.leaf 442823466) (.leaf 433909603)) (.branch 104 (.leaf 425184469) (.leaf 416643634))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 408282791) (.leaf 400097753)) (.branch 108 (.leaf 392084450) (.leaf 384238923))) (.branch 111 (.branch 110 (.leaf 376557320) (.leaf 369035894)) (.branch 112 (.leaf 361671000) (.leaf 354459088)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 347396702) (.leaf 340480480)) (.branch 116 (.leaf 333707144) (.leaf 327073504))) (.branch 119 (.branch 118 (.leaf 320576453) (.leaf 314212959)) (.branch 120 (.leaf 307980074) (.leaf 301874919)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 452).prefactor = (598279663814163/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 452).cutoff/(generalMeanRows 452).c)).2 =
    (49763573768177/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 452).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 452).q*(generalMeanRows 452).c/2-2 = (1237/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable167.value]
  have hcontinuation : (generalMeanRows 452).q*(generalMeanRows 452).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable160.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 452).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 452).criticalRate j.val*(generalMeanRows 452).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 452).c*(generalMeanRows 452).criticalPoint j.val)).2-
      (generalMeanRows 452).J/2-(generalMeanRows 452).error (generalMeanGrid j.val)+
      (generalMeanRows 452).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 452).c)).2-
      (generalMeanRows 452).J/2-(generalMeanRows 452).error 4 := by
  have he : (generalMeanRows 452).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 452) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 452)
    (generalMeanRows_prefactorDomain 452) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0452

/-! Kernel-checked entropy margins for general spectral rectangle 453. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0453
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5183407221) (.branch 2 (.leaf 5005519459) (.leaf 4835653698))) (.branch 5 (.branch 4 (.leaf 4673349611) (.leaf 4518179473)) (.branch 6 (.leaf 4369745317) (.leaf 4227676391)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4091626892) (.leaf 3961273923)) (.branch 10 (.leaf 3836315658) (.leaf 3716469683))) (.branch 13 (.branch 12 (.leaf 3601471501) (.leaf 3491073169)) (.branch 14 (.leaf 3385042066) (.leaf 3283159763))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3185221006) (.branch 17 (.leaf 3091032767) (.leaf 3000413398))) (.branch 20 (.branch 19 (.leaf 2913191831) (.leaf 2829206867)) (.branch 21 (.leaf 2748306502) (.leaf 2670347317)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2595193918) (.leaf 2522718407)) (.branch 25 (.leaf 2452799903) (.leaf 2385324097))) (.branch 28 (.branch 27 (.leaf 2320182835) (.leaf 2257273740)) (.branch 29 (.leaf 2196499847) (.leaf 2137769280)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2080994940) (.branch 32 (.leaf 2026094219) (.leaf 1972988735))) (.branch 35 (.branch 34 (.leaf 1921604079) (.leaf 1871869584)) (.branch 36 (.leaf 1823718110) (.leaf 1777085840)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1731912089) (.leaf 1688139128)) (.branch 40 (.leaf 1645712017) (.leaf 1604578450))) (.branch 43 (.branch 42 (.leaf 1564688609) (.leaf 1525995025)) (.branch 44 (.leaf 1488452455) (.leaf 1452017755))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1416649770) (.branch 47 (.leaf 1382309230) (.leaf 1348958644))) (.branch 50 (.branch 49 (.leaf 1316562210) (.leaf 1285085727)) (.branch 51 (.leaf 1254496509) (.leaf 1224763307)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1195856238) (.leaf 1167746711)) (.branch 55 (.leaf 1140407364) (.leaf 1113812002))) (.branch 58 (.branch 57 (.leaf 1087935537) (.leaf 1062753933)) (.branch 59 (.leaf 1038244157) (.leaf 1014384123))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 991152655) (.branch 62 (.leaf 968529433) (.leaf 946494960))) (.branch 65 (.branch 64 (.leaf 925030515) (.leaf 904118124)) (.branch 66 (.leaf 883740517) (.leaf 863881099)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 844523919) (.leaf 825653638)) (.branch 70 (.leaf 807255501) (.leaf 789315310))) (.branch 73 (.branch 72 (.leaf 771819402) (.leaf 754754619)) (.branch 74 (.leaf 738108290) (.leaf 721868207))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 706022605) (.branch 77 (.leaf 690560143) (.leaf 675469884))) (.branch 80 (.branch 79 (.leaf 660741278) (.leaf 646364147)) (.branch 81 (.leaf 632328667) (.leaf 618625353)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 605245045) (.leaf 592178895)) (.branch 85 (.leaf 579418353) (.leaf 566955156))) (.branch 88 (.branch 87 (.leaf 554781315) (.leaf 542889102)) (.branch 89 (.leaf 531271045) (.leaf 519919911)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 508828702) (.branch 92 (.leaf 497990642) (.leaf 487399169))) (.branch 95 (.branch 94 (.leaf 477047929) (.leaf 466930765)) (.branch 96 (.leaf 457041709) (.leaf 447374980)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 437924969) (.leaf 428686239)) (.branch 100 (.leaf 419653517) (.leaf 410821685))) (.branch 103 (.branch 102 (.leaf 402185778) (.leaf 393740975)) (.branch 104 (.leaf 385482598) (.leaf 377406104))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 369507078) (.leaf 361781235)) (.branch 108 (.leaf 354224409) (.leaf 346832552))) (.branch 111 (.branch 110 (.leaf 339601730) (.leaf 332528117)) (.branch 112 (.leaf 325607994) (.leaf 318837743)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 312213845) (.leaf 305732878)) (.branch 116 (.leaf 299391509) (.leaf 293186497))) (.branch 119 (.branch 118 (.leaf 287114686) (.leaf 281173003)) (.branch 120 (.leaf 275358458) (.leaf 269668137)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 453).prefactor = (615562454343137/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 453).cutoff/(generalMeanRows 453).c)).2 =
    (76392120747487/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 453).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 453).q*(generalMeanRows 453).c/2-2 = (3223/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable132.value]
  have hcontinuation : (generalMeanRows 453).q*(generalMeanRows 453).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable151.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 453).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 453).criticalRate j.val*(generalMeanRows 453).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 453).c*(generalMeanRows 453).criticalPoint j.val)).2-
      (generalMeanRows 453).J/2-(generalMeanRows 453).error (generalMeanGrid j.val)+
      (generalMeanRows 453).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 453).c)).2-
      (generalMeanRows 453).J/2-(generalMeanRows 453).error 4 := by
  have he : (generalMeanRows 453).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 453) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 453)
    (generalMeanRows_prefactorDomain 453) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0453

/-! Kernel-checked entropy margins for general spectral rectangle 454. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0454
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5308399020) (.branch 2 (.leaf 5128796298) (.leaf 4957262615))) (.branch 5 (.branch 4 (.leaf 4793334605) (.leaf 4636581745)) (.branch 6 (.leaf 4486603496) (.leaf 4343026736)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4205503479) (.leaf 4073708815)) (.branch 10 (.leaf 3947339058) (.leaf 3826110081))) (.branch 13 (.branch 12 (.leaf 3709755801) (.leaf 3598026812)) (.branch 14 (.leaf 3490689138) (.leaf 3387523102))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3288322289) (.branch 17 (.leaf 3192892605) (.leaf 3101051406))) (.branch 20 (.branch 19 (.leaf 3012626713) (.leaf 2927456474)) (.branch 21 (.leaf 2845387901) (.leaf 2766276850)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2689987251) (.leaf 2616390583)) (.branch 25 (.leaf 2545365390) (.leaf 2476796826))) (.branch 28 (.branch 27 (.leaf 2410576244) (.leaf 2346600806)) (.branch 29 (.leaf 2284773125) (.leaf 2225000931)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2167196760) (.branch 32 (.leaf 2111277669) (.leaf 2057164960))) (.branch 35 (.branch 34 (.leaf 2004783936) (.leaf 1954063663)) (.branch 36 (.leaf 1904936752) (.leaf 1857339154)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1811209972) (.leaf 1766491278)) (.branch 40 (.leaf 1723127948) (.leaf 1681067505))) (.branch 43 (.branch 42 (.leaf 1640259974) (.leaf 1600657738)) (.branch 44 (.leaf 1562215416) (.leaf 1524889739))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1488639432) (.branch 47 (.leaf 1453425113) (.leaf 1419209190))) (.branch 50 (.branch 49 (.leaf 1385955763) (.leaf 1353630541)) (.branch 51 (.leaf 1322200753) (.leaf 1291635072)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1261903538) (.leaf 1232977490)) (.branch 55 (.leaf 1204829500) (.leaf 1177433310))) (.branch 58 (.branch 57 (.leaf 1150763771) (.leaf 1124796790)) (.branch 59 (.leaf 1099509280) (.leaf 1074879104))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1050885033) (.branch 62 (.leaf 1027506701) (.leaf 1004724563))) (.branch 65 (.branch 64 (.leaf 982519855) (.leaf 960874556)) (.branch 66 (.leaf 939771355) (.leaf 919193616)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 899125346) (.leaf 879551164)) (.branch 70 (.leaf 860456278) (.leaf 841826449))) (.branch 73 (.branch 72 (.leaf 823647976) (.leaf 805907662)) (.branch 74 (.leaf 788592798) (.leaf 771691137))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 755190877) (.branch 77 (.leaf 739080638) (.leaf 723349445))) (.branch 80 (.branch 79 (.leaf 707986710) (.leaf 692982216)) (.branch 81 (.leaf 678326101) (.leaf 664008842)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 650021238) (.leaf 636354405)) (.branch 85 (.leaf 622999751) (.leaf 609948975))) (.branch 88 (.branch 87 (.leaf 597194046) (.leaf 584727198)) (.branch 89 (.leaf 572540918) (.leaf 560627931)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 548981200) (.branch 92 (.leaf 537593905) (.leaf 526459444))) (.branch 95 (.branch 94 (.leaf 515571421) (.leaf 504923635)) (.branch 96 (.leaf 494510077) (.leaf 484324922)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 474362519) (.leaf 464617387)) (.branch 100 (.leaf 455084208) (.leaf 445757821))) (.branch 103 (.branch 102 (.leaf 436633215) (.leaf 427705528)) (.branch 104 (.leaf 418970034) (.leaf 410422146))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 402057404) (.leaf 393871478)) (.branch 108 (.leaf 385860155) (.leaf 378019342))) (.branch 111 (.branch 110 (.leaf 370345058) (.leaf 362833433)) (.branch 112 (.leaf 355480700) (.leaf 348283196)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 341237355) (.leaf 334339708)) (.branch 116 (.leaf 327586876) (.leaf 320975571))) (.branch 119 (.branch 118 (.leaf 314502590) (.leaf 308164815)) (.branch 120 (.leaf 301959207) (.leaf 295882806)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 454).prefactor = (2479344039730723/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 454).cutoff/(generalMeanRows 454).c)).2 =
    (389652949360589/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 454).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 454).q*(generalMeanRows 454).c/2-2 = (3137/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable130.value]
  have hcontinuation : (generalMeanRows 454).q*(generalMeanRows 454).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable151.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 454).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 454).criticalRate j.val*(generalMeanRows 454).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 454).c*(generalMeanRows 454).criticalPoint j.val)).2-
      (generalMeanRows 454).J/2-(generalMeanRows 454).error (generalMeanGrid j.val)+
      (generalMeanRows 454).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 454).c)).2-
      (generalMeanRows 454).J/2-(generalMeanRows 454).error 4 := by
  have he : (generalMeanRows 454).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 454) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 454)
    (generalMeanRows_prefactorDomain 454) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0454

/-! Kernel-checked entropy margins for general spectral rectangle 455. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0455
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5289655918) (.branch 2 (.leaf 5115449884) (.leaf 4949018792))) (.branch 5 (.branch 4 (.leaf 4789914829) (.leaf 4637722020)) (.branch 6 (.leaf 4492053455) (.leaf 4352548804)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4218872095) (.leaf 4090709720)) (.branch 10 (.leaf 3967768641) (.leaf 3849774768))) (.branch 13 (.branch 12 (.leaf 3736471489) (.leaf 3627618350)) (.branch 14 (.leaf 3522989835) (.leaf 3422374276))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3325572841) (.branch 17 (.leaf 3232398624) (.leaf 3142675799))) (.branch 20 (.branch 19 (.leaf 3056238856) (.leaf 2972931888)) (.branch 21 (.leaf 2892607944) (.leaf 2815128428)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2740362550) (.leaf 2668186812)) (.branch 25 (.leaf 2598484539) (.leaf 2531145440))) (.branch 28 (.branch 27 (.leaf 2466065208) (.leaf 2403145140)) (.branch 29 (.leaf 2342291793) (.leaf 2283416659)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2226435864) (.branch 32 (.leaf 2171269888) (.leaf 2117843306))) (.branch 35 (.branch 34 (.leaf 2066084541) (.leaf 2015925642)) (.branch 36 (.leaf 1967302070) (.leaf 1920152499)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1874418633) (.leaf 1830045033)) (.branch 40 (.leaf 1786978954) (.leaf 1745170193))) (.branch 43 (.branch 42 (.leaf 1704570950) (.leaf 1665135690)) (.branch 44 (.leaf 1626821024) (.leaf 1589585585))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1553389925) (.branch 47 (.leaf 1518196405) (.leaf 1483969103))) (.branch 50 (.branch 49 (.leaf 1450673719) (.leaf 1418277493)) (.branch 51 (.leaf 1386749117) (.leaf 1356058670)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1326177534) (.leaf 1297078335)) (.branch 55 (.leaf 1268734878) (.leaf 1241122084))) (.branch 58 (.branch 57 (.leaf 1214215934) (.leaf 1187993420)) (.branch 59 (.leaf 1162432488) (.leaf 1137511996))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1113211666) (.branch 62 (.leaf 1089512043) (.leaf 1066394454))) (.branch 65 (.branch 64 (.leaf 1043840970) (.leaf 1021834371)) (.branch 66 (.leaf 1000358113) (.leaf 979396293)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 958933620) (.leaf 938955389)) (.branch 70 (.leaf 919447450) (.leaf 900396183))) (.branch 73 (.branch 72 (.leaf 881788476) (.leaf 863611698)) (.branch 74 (.leaf 845853681) (.leaf 828502697))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 811547439) (.branch 77 (.leaf 794977001) (.leaf 778780864))) (.branch 80 (.branch 79 (.leaf 762948872) (.leaf 747471226)) (.branch 81 (.leaf 732338458) (.leaf 717541426)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 703071293) (.leaf 688919521)) (.branch 85 (.leaf 675077850) (.leaf 661538295))) (.branch 88 (.branch 87 (.leaf 648293129) (.leaf 635334874)) (.branch 89 (.leaf 622656292) (.leaf 610250374)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 598110330) (.branch 92 (.leaf 586229583) (.leaf 574601758))) (.branch 95 (.branch 94 (.leaf 563220675) (.leaf 552080344)) (.branch 96 (.leaf 541174951) (.leaf 530498859)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 520046596) (.leaf 509812852)) (.branch 100 (.leaf 499792469) (.leaf 489980441))) (.branch 103 (.branch 102 (.leaf 480371903) (.leaf 470962130)) (.branch 104 (.leaf 461746528) (.leaf 452720634))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 443880106) (.leaf 435220724)) (.branch 108 (.leaf 426738382) (.leaf 418429086))) (.branch 111 (.branch 110 (.leaf 410288949) (.leaf 402314188)) (.branch 112 (.leaf 394501119) (.leaf 386846159)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 379345814) (.leaf 371996684)) (.branch 116 (.leaf 364795455) (.leaf 357738898))) (.branch 119 (.branch 118 (.leaf 350823867) (.leaf 344047296)) (.branch 120 (.leaf 337406194) (.leaf 330897646)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 455).prefactor = (301180278907599/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 455).cutoff/(generalMeanRows 455).c)).2 =
    (40580093576857/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 455).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 455).q*(generalMeanRows 455).c/2-2 = (1203/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable135.value]
  have hcontinuation : (generalMeanRows 455).q*(generalMeanRows 455).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable160.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 455).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 455).criticalRate j.val*(generalMeanRows 455).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 455).c*(generalMeanRows 455).criticalPoint j.val)).2-
      (generalMeanRows 455).J/2-(generalMeanRows 455).error (generalMeanGrid j.val)+
      (generalMeanRows 455).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 455).c)).2-
      (generalMeanRows 455).J/2-(generalMeanRows 455).error 4 := by
  have he : (generalMeanRows 455).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 455) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 455)
    (generalMeanRows_prefactorDomain 455) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0455

/-! Kernel-checked entropy margins for general spectral rectangle 456. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0456
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5511484110) (.branch 2 (.leaf 5335395517) (.leaf 5167114302))) (.branch 5 (.branch 4 (.leaf 5006189749) (.leaf 4852203253)) (.branch 6 (.leaf 4704765513) (.leaf 4563514027)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4428110853) (.leaf 4298240600)) (.branch 10 (.leaf 4173608609) (.leaf 4053939325))) (.branch 13 (.branch 12 (.leaf 3938974816) (.leaf 3828473427)) (.branch 14 (.leaf 3722208569) (.leaf 3619967603))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3521550828) (.branch 17 (.leaf 3426770558) (.leaf 3335450273))) (.branch 20 (.branch 19 (.leaf 3247423845) (.leaf 3162534818)) (.branch 21 (.leaf 3080635758) (.leaf 3001587646)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2925259322) (.leaf 2851526969)) (.branch 25 (.leaf 2780273636) (.leaf 2711388802))) (.branch 28 (.branch 27 (.leaf 2644767964) (.leaf 2580312261)) (.branch 29 (.leaf 2517928122) (.leaf 2457526941)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2399024772) (.branch 32 (.leaf 2342342047) (.leaf 2287403313))) (.branch 35 (.branch 34 (.leaf 2234136989) (.leaf 2182475134)) (.branch 36 (.leaf 2132353236) (.leaf 2083710010)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2036487216) (.leaf 1990629478)) (.branch 40 (.leaf 1946084128) (.leaf 1902801049))) (.branch 43 (.branch 42 (.leaf 1860732530) (.leaf 1819833139)) (.branch 44 (.leaf 1780059590) (.leaf 1741370626))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1703726912) (.branch 47 (.leaf 1667090929) (.leaf 1631426872))) (.branch 50 (.branch 49 (.leaf 1596700567) (.leaf 1562879373)) (.branch 51 (.leaf 1529932111) (.leaf 1497828981)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1466541494) (.leaf 1436042399)) (.branch 55 (.leaf 1406305624) (.leaf 1377306214))) (.branch 58 (.branch 57 (.leaf 1349020273) (.leaf 1321424910)) (.branch 59 (.leaf 1294498190) (.leaf 1268219088))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1242567438) (.branch 62 (.leaf 1217523897) (.leaf 1193069899))) (.branch 65 (.branch 64 (.leaf 1169187621) (.leaf 1145859947)) (.branch 66 (.leaf 1123070429) (.leaf 1100803263)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1079043252) (.leaf 1057775777)) (.branch 70 (.leaf 1036986777) (.leaf 1016662715))) (.branch 73 (.branch 72 (.leaf 996790556) (.leaf 977357749)) (.branch 74 (.leaf 958352196) (.leaf 939762239))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 921576637) (.branch 77 (.leaf 903784546) (.leaf 886375504))) (.branch 80 (.branch 79 (.leaf 869339414) (.leaf 852666525)) (.branch 81 (.leaf 836347420) (.leaf 820373001)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 804734474) (.leaf 789423338)) (.branch 85 (.leaf 774431371) (.leaf 759750618))) (.branch 88 (.branch 87 (.leaf 745373380) (.leaf 731292208)) (.branch 89 (.leaf 717499885) (.leaf 703989422)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 690754046) (.branch 92 (.leaf 677787194) (.leaf 665082504))) (.branch 95 (.branch 94 (.leaf 652633803) (.leaf 640435106)) (.branch 96 (.leaf 628480605) (.leaf 616764661)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 605281802) (.leaf 594026712)) (.branch 100 (.leaf 582994228) (.leaf 572179334))) (.branch 103 (.branch 102 (.leaf 561577154) (.leaf 551182950)) (.branch 104 (.leaf 540992112) (.leaf 531000160))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 521202731) (.leaf 511595585)) (.branch 108 (.leaf 502174592) (.leaf 492935731))) (.branch 111 (.branch 110 (.leaf 483875090) (.leaf 474988857)) (.branch 112 (.leaf 466273317) (.leaf 457724855)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 449339943) (.leaf 441115146)) (.branch 116 (.leaf 433047113) (.leaf 425132578))) (.branch 119 (.branch 118 (.leaf 417368356) (.leaf 409751339)) (.branch 120 (.leaf 402278495) (.leaf 394946866)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 456).prefactor = (606469287788029/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 456).cutoff/(generalMeanRows 456).c)).2 =
    (84273090461937/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 456).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 456).q*(generalMeanRows 456).c/2-2 = (227/320:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable159.value]
  have hcontinuation : (generalMeanRows 456).q*(generalMeanRows 456).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable160.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 456).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 456).criticalRate j.val*(generalMeanRows 456).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 456).c*(generalMeanRows 456).criticalPoint j.val)).2-
      (generalMeanRows 456).J/2-(generalMeanRows 456).error (generalMeanGrid j.val)+
      (generalMeanRows 456).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 456).c)).2-
      (generalMeanRows 456).J/2-(generalMeanRows 456).error 4 := by
  have he : (generalMeanRows 456).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 456) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 456)
    (generalMeanRows_prefactorDomain 456) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0456

/-! Kernel-checked entropy margins for general spectral rectangle 457. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0457
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5275126768) (.branch 2 (.leaf 5086251574) (.leaf 4905997476))) (.branch 5 (.branch 4 (.leaf 4733871553) (.leaf 4569415631)) (.branch 6 (.leaf 4412203245) (.leaf 4261836948)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4117945884) (.leaf 3980183623)) (.branch 10 (.leaf 3848226207) (.leaf 3721770386))) (.branch 13 (.branch 12 (.leaf 3600532021) (.leaf 3484244645)) (.branch 14 (.leaf 3372658146) (.leaf 3265537568))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3162662025) (.branch 17 (.leaf 3063823703) (.leaf 2968826942))) (.branch 20 (.branch 19 (.leaf 2877487408) (.leaf 2789631313)) (.branch 21 (.leaf 2705094719) (.leaf 2623722875)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2545369626) (.leaf 2469896851)) (.branch 25 (.leaf 2397173953) (.leaf 2327077383))) (.branch 28 (.branch 27 (.leaf 2259490198) (.leaf 2194301655)) (.branch 29 (.leaf 2131406828) (.leaf 2070706259)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2012105627) (.branch 32 (.leaf 1955515443) (.leaf 1900850766))) (.branch 35 (.branch 34 (.leaf 1848030935) (.leaf 1796979321)) (.branch 36 (.leaf 1747623099) (.leaf 1699893028)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1653723246) (.leaf 1609051085)) (.branch 40 (.leaf 1565816891) (.leaf 1523963859))) (.branch 43 (.branch 42 (.leaf 1483437871) (.leaf 1444187359)) (.branch 44 (.leaf 1406163157) (.leaf 1369318379))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1333608297) (.branch 47 (.leaf 1298990221) (.leaf 1265423398))) (.branch 50 (.branch 49 (.leaf 1232868908) (.leaf 1201289568)) (.branch 51 (.leaf 1170649845) (.leaf 1140915768)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1112054852) (.leaf 1084036019)) (.branch 55 (.leaf 1056829531) (.leaf 1030406921))) (.branch 58 (.branch 57 (.leaf 1004740928) (.leaf 979805442)) (.branch 59 (.leaf 955575444) (.leaf 932026954))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 909136979) (.branch 62 (.leaf 886883469) (.leaf 865245268))) (.branch 65 (.branch 64 (.leaf 844202074) (.leaf 823734398)) (.branch 66 (.leaf 803823524) (.leaf 784451476)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 765600982) (.leaf 747255439)) (.branch 70 (.leaf 729398889) (.leaf 712015982))) (.branch 73 (.branch 72 (.leaf 695091953) (.leaf 678612593)) (.branch 74 (.leaf 662564229) (.leaf 646933694))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 631708308) (.branch 77 (.leaf 616875856) (.leaf 602424567))) (.branch 80 (.branch 79 (.leaf 588343097) (.leaf 574620507)) (.branch 81 (.leaf 561246250) (.leaf 548210150)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 535502389) (.leaf 523113492)) (.branch 85 (.leaf 511034309) (.leaf 499256008))) (.branch 88 (.branch 87 (.leaf 487770057) (.leaf 476568212)) (.branch 89 (.leaf 465642507) (.leaf 454985243)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 444588975) (.branch 92 (.leaf 434446503) (.leaf 424550865))) (.branch 95 (.branch 94 (.leaf 414895323) (.leaf 405473356)) (.branch 96 (.leaf 396278654) (.leaf 387305106)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 378546795) (.leaf 369997990)) (.branch 100 (.leaf 361653138) (.leaf 353506860))) (.branch 103 (.branch 102 (.leaf 345553941) (.leaf 337789325)) (.branch 104 (.leaf 330208112) (.leaf 322805548))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 315577023) (.leaf 308518063)) (.branch 108 (.leaf 301624330) (.leaf 294891609))) (.branch 111 (.branch 110 (.leaf 288315814) (.leaf 281892973)) (.branch 112 (.leaf 275619232) (.leaf 269490847)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 263504181) (.leaf 257655703)) (.branch 116 (.leaf 251941977) (.leaf 246359669))) (.branch 119 (.branch 118 (.leaf 240905534) (.leaf 235576420)) (.branch 120 (.leaf 230369263) (.leaf 225281080)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 457).prefactor = (5215951449869421/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 457).cutoff/(generalMeanRows 457).c)).2 =
    (355004607205391/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 457).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 457).q*(generalMeanRows 457).c/2-2 = (43/50:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable020.value]
  have hcontinuation : (generalMeanRows 457).q*(generalMeanRows 457).cutoff/2-2 = (1054/507:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable144.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 457).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 457).criticalRate j.val*(generalMeanRows 457).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 457).c*(generalMeanRows 457).criticalPoint j.val)).2-
      (generalMeanRows 457).J/2-(generalMeanRows 457).error (generalMeanGrid j.val)+
      (generalMeanRows 457).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 457).c)).2-
      (generalMeanRows 457).J/2-(generalMeanRows 457).error 4 := by
  have he : (generalMeanRows 457).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 457) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 457)
    (generalMeanRows_prefactorDomain 457) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0457

/-! Kernel-checked entropy margins for general spectral rectangle 458. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0458
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5494469886) (.branch 2 (.leaf 5303035727) (.leaf 5120270295))) (.branch 5 (.branch 4 (.leaf 4945677510) (.leaf 4778796313)) (.branch 6 (.leaf 4619197619) (.leaf 4466481587)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4320275181) (.leaf 4180229985)) (.branch 10 (.leaf 4046020227) (.leaf 3917341003))) (.branch 13 (.branch 12 (.leaf 3793906673) (.leaf 3675449396)) (.branch 14 (.leaf 3561717811) (.leaf 3452475826))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3347501520) (.branch 17 (.leaf 3246586139) (.leaf 3149533171))) (.branch 20 (.branch 19 (.leaf 3056157504) (.leaf 2966284652)) (.branch 21 (.leaf 2879750036) (.leaf 2796398334)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2716082869) (.leaf 2638665052)) (.branch 25 (.leaf 2564013864) (.leaf 2492005375))) (.branch 28 (.branch 27 (.leaf 2422522303) (.leaf 2355453599)) (.branch 29 (.leaf 2290694066) (.leaf 2228144001)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2167708867) (.branch 32 (.leaf 2109298984) (.leaf 2052829241))) (.branch 35 (.branch 34 (.leaf 1998218826) (.leaf 1945390982)) (.branch 36 (.leaf 1894272766) (.leaf 1844794837)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1796891246) (.leaf 1750499251)) (.branch 40 (.leaf 1705559132) (.leaf 1662014027))) (.branch 43 (.branch 42 (.leaf 1619809775) (.leaf 1578894763)) (.branch 44 (.leaf 1539219795) (.leaf 1500737957))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1463404494) (.branch 47 (.leaf 1427176700) (.leaf 1392013805))) (.branch 50 (.branch 49 (.leaf 1357876874) (.leaf 1324728715)) (.branch 51 (.leaf 1292533783) (.leaf 1261258101)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1230869175) (.leaf 1201335920)) (.branch 55 (.leaf 1172628591) (.leaf 1144718714))) (.branch 58 (.branch 57 (.leaf 1117579020) (.leaf 1091183391)) (.branch 59 (.leaf 1065506797) (.leaf 1040525247))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1016215739) (.branch 62 (.leaf 992556206) (.leaf 969525478))) (.branch 65 (.branch 64 (.leaf 947103237) (.leaf 925269974)) (.branch 66 (.leaf 904006952) (.leaf 883296173)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 863120339) (.leaf 843462822)) (.branch 70 (.leaf 824307631) (.leaf 805639387))) (.branch 73 (.branch 72 (.leaf 787443290) (.leaf 769705097)) (.branch 74 (.leaf 752411095) (.leaf 735548077))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 719103320) (.branch 77 (.leaf 703064564) (.leaf 687419993))) (.branch 80 (.branch 79 (.leaf 672158211) (.leaf 657268229)) (.branch 81 (.leaf 642739446) (.leaf 628561630)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 614724907) (.leaf 601219741)) (.branch 85 (.leaf 588036922) (.leaf 575167553))) (.branch 88 (.branch 87 (.leaf 562603037) (.leaf 550335065)) (.branch 89 (.leaf 538355601) (.leaf 526656875)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 515231371) (.branch 92 (.leaf 504071817) (.leaf 493171173))) (.branch 95 (.branch 94 (.leaf 482522626) (.leaf 472119578)) (.branch 96 (.leaf 461955638) (.leaf 452024616)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 442320514) (.leaf 432837517)) (.branch 100 (.leaf 423569989) (.leaf 414512466))) (.branch 103 (.branch 102 (.leaf 405659645) (.leaf 397006387)) (.branch 104 (.leaf 388547701) (.leaf 380278747))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 372194824) (.leaf 364291369)) (.branch 108 (.leaf 356563952) (.leaf 349008269))) (.branch 111 (.branch 110 (.leaf 341620139) (.leaf 334395501)) (.branch 112 (.leaf 327330406) (.leaf 320421017)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 313663604) (.leaf 307054541)) (.branch 116 (.leaf 300590299) (.leaf 294267448))) (.branch 119 (.branch 118 (.leaf 288082649) (.leaf 282032656)) (.branch 120 (.leaf 276114308) (.leaf 270324528)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 458).prefactor = (5253410152903323/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 458).cutoff/(generalMeanRows 458).c)).2 =
    (74101758748271/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 458).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 458).q*(generalMeanRows 458).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  have hcontinuation : (generalMeanRows 458).q*(generalMeanRows 458).cutoff/2-2 = (1054/507:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable144.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 458).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 458).criticalRate j.val*(generalMeanRows 458).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 458).c*(generalMeanRows 458).criticalPoint j.val)).2-
      (generalMeanRows 458).J/2-(generalMeanRows 458).error (generalMeanGrid j.val)+
      (generalMeanRows 458).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 458).c)).2-
      (generalMeanRows 458).J/2-(generalMeanRows 458).error 4 := by
  have he : (generalMeanRows 458).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 458) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 458)
    (generalMeanRows_prefactorDomain 458) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0458

/-! Kernel-checked entropy margins for general spectral rectangle 459. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0459
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5638524116) (.branch 2 (.leaf 5458865379) (.leaf 5287200857))) (.branch 5 (.branch 4 (.leaf 5123067313) (.leaf 4966034558)) (.branch 6 (.leaf 4815702571) (.leaf 4671698920)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4533676456) (.leaf 4401311238)) (.branch 10 (.leaf 4274300675) (.leaf 4152361835))) (.branch 13 (.branch 12 (.leaf 4035229926) (.leaf 3922656914)) (.branch 14 (.leaf 3814410267) (.leaf 3710271812))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3610036690) (.branch 17 (.leaf 3513512408) (.leaf 3420517962))) (.branch 20 (.branch 19 (.leaf 3330883034) (.leaf 3244447266)) (.branch 21 (.leaf 3161059576) (.leaf 3080577536)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3002866802) (.leaf 2927800582)) (.branch 25 (.leaf 2855259143) (.leaf 2785129362))) (.branch 28 (.branch 27 (.leaf 2717304304) (.leaf 2651682830)) (.branch 29 (.leaf 2588169239) (.leaf 2526672931)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2467108091) (.branch 32 (.leaf 2409393405) (.leaf 2353451783))) (.branch 35 (.branch 34 (.leaf 2299210108) (.leaf 2246599005)) (.branch 36 (.leaf 2195552613) (.leaf 2146008387)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2097906903) (.leaf 2051191677)) (.branch 40 (.leaf 2005809001) (.leaf 1961707781))) (.branch 43 (.branch 42 (.leaf 1918839395) (.leaf 1877157550)) (.branch 44 (.leaf 1836618156) (.leaf 1797179201))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1758800641) (.branch 47 (.leaf 1721444290) (.leaf 1685073720))) (.branch 50 (.branch 49 (.leaf 1649654168) (.leaf 1615152444)) (.branch 51 (.leaf 1581536851) (.leaf 1548777102)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1516844249) (.leaf 1485710615)) (.branch 55 (.leaf 1455349722) (.leaf 1425736235))) (.branch 58 (.branch 57 (.leaf 1396845899) (.leaf 1368655489)) (.branch 59 (.leaf 1341142754) (.leaf 1314286368))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1288065887) (.branch 62 (.leaf 1262461702) (.leaf 1237454999))) (.branch 65 (.branch 64 (.leaf 1213027719) (.leaf 1189162524)) (.branch 66 (.leaf 1165842758) (.leaf 1143052419)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1120776123) (.leaf 1098999076)) (.branch 70 (.leaf 1077707050) (.leaf 1056886349))) (.branch 73 (.branch 72 (.leaf 1036523792) (.leaf 1016606683)) (.branch 74 (.leaf 997122793) (.leaf 978060335))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 959407948) (.branch 77 (.leaf 941154675) (.leaf 923289944))) (.branch 80 (.branch 79 (.leaf 905803554) (.leaf 888685656)) (.branch 81 (.leaf 871926740) (.leaf 855517617)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 839449409) (.leaf 823713532)) (.branch 85 (.leaf 808301686) (.leaf 793205841))) (.branch 88 (.branch 87 (.leaf 778418229) (.leaf 763931329)) (.branch 89 (.leaf 749737859) (.leaf 735830766)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 722203218) (.branch 92 (.leaf 708848591) (.leaf 695760466))) (.branch 95 (.branch 94 (.leaf 682932617) (.leaf 670359004)) (.branch 96 (.leaf 658033769) (.leaf 645951222)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 634105844) (.leaf 622492272)) (.branch 100 (.leaf 611105297) (.leaf 599939859))) (.branch 103 (.branch 102 (.leaf 588991038) (.leaf 578254054)) (.branch 104 (.leaf 567724257) (.leaf 557397125))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 547268258) (.leaf 537333375)) (.branch 108 (.leaf 527588310) (.leaf 518029005))) (.branch 111 (.branch 110 (.leaf 508651511) (.leaf 499451979)) (.branch 112 (.leaf 490426662) (.leaf 481571907)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 472884155) (.leaf 464359936)) (.branch 116 (.leaf 455995867) (.leaf 447788648))) (.branch 119 (.branch 118 (.leaf 439735063) (.leaf 431831971)) (.branch 120 (.leaf 424076310) (.leaf 416465090)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 459).prefactor = (2475326109888669/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 459).cutoff/(generalMeanRows 459).c)).2 =
    (213446595690371/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 459).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 459).q*(generalMeanRows 459).c/2-2 = (2793/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable128.value]
  have hcontinuation : (generalMeanRows 459).q*(generalMeanRows 459).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable146.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 459).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 459).criticalRate j.val*(generalMeanRows 459).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 459).c*(generalMeanRows 459).criticalPoint j.val)).2-
      (generalMeanRows 459).J/2-(generalMeanRows 459).error (generalMeanGrid j.val)+
      (generalMeanRows 459).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 459).c)).2-
      (generalMeanRows 459).J/2-(generalMeanRows 459).error 4 := by
  have he : (generalMeanRows 459).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 459) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 459)
    (generalMeanRows_prefactorDomain 459) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0459

/-! Kernel-checked entropy margins for general spectral rectangle 460. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0460
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5776976510) (.branch 2 (.leaf 5595813936) (.leaf 5422689178))) (.branch 5 (.branch 4 (.leaf 5257135821) (.leaf 5098720760)) (.branch 6 (.leaf 4947041287) (.leaf 4801722501)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4662414976) (.leaf 4528792677)) (.branch 10 (.leaf 4400551080) (.leaf 4277405471))) (.branch 13 (.branch 12 (.leaf 4159089418) (.leaf 4045353371)) (.branch 14 (.leaf 3935963403) (.leaf 3830700052))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3729357272) (.branch 17 (.leaf 3631741475) (.leaf 3537670647))) (.branch 20 (.branch 19 (.leaf 3446973542) (.leaf 3359488943)) (.branch 21 (.leaf 3275064977) (.leaf 3193558494)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3114834479) (.leaf 3038765526)) (.branch 25 (.leaf 2965231337) (.leaf 2894118272))) (.branch 28 (.branch 27 (.leaf 2825318919) (.leaf 2758731703)) (.branch 29 (.leaf 2694260526) (.leaf 2631814420)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2571307240) (.branch 32 (.leaf 2512657366) (.leaf 2455787431))) (.branch 35 (.branch 34 (.leaf 2400624068) (.leaf 2347097670)) (.branch 36 (.leaf 2295142172) (.leaf 2244694840)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2195696081) (.leaf 2148089261)) (.branch 40 (.leaf 2101820532) (.leaf 2056838683))) (.branch 43 (.branch 42 (.leaf 2013094979) (.leaf 1970543033)) (.branch 44 (.leaf 1929138668) (.leaf 1888839800))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1849606318) (.branch 47 (.leaf 1811399981) (.leaf 1774184312))) (.branch 50 (.branch 49 (.leaf 1737924506) (.leaf 1702587339)) (.branch 51 (.leaf 1668141085) (.leaf 1634555435)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1601801424) (.leaf 1569851358)) (.branch 55 (.leaf 1538678753) (.leaf 1508258266))) (.branch 58 (.branch 57 (.leaf 1478565642) (.leaf 1449577654)) (.branch 59 (.leaf 1421272055) (.leaf 1393627525))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1366623626) (.branch 62 (.leaf 1340240758) (.leaf 1314460117))) (.branch 65 (.branch 64 (.leaf 1289263658) (.leaf 1264634053)) (.branch 66 (.leaf 1240554662) (.leaf 1217009495)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1193983183) (.leaf 1171460949)) (.branch 70 (.leaf 1149428577) (.leaf 1127872390))) (.branch 73 (.branch 72 (.leaf 1106779219) (.leaf 1086136386)) (.branch 74 (.leaf 1065931675) (.leaf 1046153315))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1026789958) (.branch 77 (.leaf 1007830661) (.leaf 989264865))) (.branch 80 (.branch 79 (.leaf 971082383) (.leaf 953273377)) (.branch 81 (.leaf 935828348) (.leaf 918738118)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 901993818) (.leaf 885586874)) (.branch 85 (.leaf 869508993) (.leaf 853752153))) (.branch 88 (.branch 87 (.leaf 838308593) (.leaf 823170795)) (.branch 89 (.leaf 808331484) (.leaf 793783611)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 779520344) (.branch 92 (.leaf 765535063) (.leaf 751821350))) (.branch 95 (.branch 94 (.leaf 738372977) (.leaf 725183905)) (.branch 96 (.leaf 712248273) (.leaf 699560389)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 687114729) (.leaf 674905926)) (.branch 100 (.leaf 662928766) (.leaf 651178182))) (.branch 103 (.branch 102 (.leaf 639649247) (.leaf 628337172)) (.branch 104 (.leaf 617237299) (.leaf 606345095))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 595656151) (.leaf 585166173)) (.branch 108 (.leaf 574870983) (.leaf 564766510))) (.branch 111 (.branch 110 (.leaf 554848791) (.leaf 545113964)) (.branch 112 (.leaf 535558265) (.leaf 526178026)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 516969670) (.leaf 507929711)) (.branch 116 (.leaf 499054747) (.leaf 490341461))) (.branch 119 (.branch 118 (.leaf 481786616) (.leaf 473387053)) (.branch 120 (.leaf 465139687) (.leaf 457041510)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 460).prefactor = (2492234547573897/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 460).cutoff/(generalMeanRows 460).c)).2 =
    (434893234047819/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 460).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 460).q*(generalMeanRows 460).c/2-2 = (2707/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable126.value]
  have hcontinuation : (generalMeanRows 460).q*(generalMeanRows 460).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable146.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 460).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 460).criticalRate j.val*(generalMeanRows 460).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 460).c*(generalMeanRows 460).criticalPoint j.val)).2-
      (generalMeanRows 460).J/2-(generalMeanRows 460).error (generalMeanGrid j.val)+
      (generalMeanRows 460).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 460).c)).2-
      (generalMeanRows 460).J/2-(generalMeanRows 460).error 4 := by
  have he : (generalMeanRows 460).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 460) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 460)
    (generalMeanRows_prefactorDomain 460) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0460

/-! Kernel-checked entropy margins for general spectral rectangle 461. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0461
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5393170709) (.branch 2 (.leaf 5197729848) (.leaf 5011210297))) (.branch 5 (.branch 4 (.leaf 4833104467) (.leaf 4662940422)) (.branch 6 (.leaf 4500278772) (.leaf 4344709902)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4195851490) (.leaf 4053346284)) (.branch 10 (.leaf 3916860096) (.leaf 3786079999))) (.branch 13 (.branch 12 (.leaf 3660712693) (.leaf 3540483020)) (.branch 14 (.leaf 3425132621) (.leaf 3314418708))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3208112950) (.branch 17 (.leaf 3106000450) (.leaf 3007878808))) (.branch 20 (.branch 19 (.leaf 2913557262) (.leaf 2822855908)) (.branch 21 (.leaf 2735604966) (.leaf 2651644117)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2570821886) (.leaf 2492995074)) (.branch 25 (.leaf 2418028231) (.leaf 2345793170))) (.branch 28 (.branch 27 (.leaf 2276168512) (.leaf 2209039273)) (.branch 29 (.leaf 2144296469) (.leaf 2081836756)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2021562095) (.branch 32 (.leaf 1963379435) (.leaf 1907200425))) (.branch 35 (.branch 34 (.leaf 1852941137) (.leaf 1800521812)) (.branch 36 (.leaf 1749866623) (.leaf 1700903453)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1653563685) (.leaf 1607782006)) (.branch 40 (.leaf 1563496227) (.leaf 1520647110))) (.branch 43 (.branch 42 (.leaf 1479178208) (.leaf 1439035712)) (.branch 44 (.leaf 1400168313) (.leaf 1362527065))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1326065262) (.branch 47 (.leaf 1290738320) (.leaf 1256503664))) (.branch 50 (.branch 49 (.leaf 1223320628) (.leaf 1191150354)) (.branch 51 (.leaf 1159955697) (.leaf 1129701143)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1100352724) (.leaf 1071877940)) (.branch 55 (.leaf 1044245684) (.leaf 1017426177))) (.branch 58 (.branch 57 (.leaf 991390901) (.leaf 966112535)) (.branch 59 (.leaf 941564899) (.leaf 917722899))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 894562472) (.branch 62 (.leaf 872060540) (.leaf 850194962))) (.branch 65 (.branch 64 (.leaf 828944488) (.leaf 808288720)) (.branch 66 (.leaf 788208070) (.leaf 768683723)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 749697603) (.leaf 731232337)) (.branch 70 (.leaf 713271222) (.leaf 695798199))) (.branch 73 (.branch 72 (.leaf 678797819) (.leaf 662255220)) (.branch 74 (.leaf 646156097) (.leaf 630486680))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 615233710) (.branch 77 (.leaf 600384416) (.leaf 585926494))) (.branch 80 (.branch 79 (.leaf 571848087) (.leaf 558137766)) (.branch 81 (.leaf 544784512) (.leaf 531777698)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 519107071) (.leaf 506762741)) (.branch 85 (.leaf 494735160) (.leaf 483015113))) (.branch 88 (.branch 87 (.leaf 471593701) (.leaf 460462328)) (.branch 89 (.leaf 449612694) (.leaf 439036773)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 428726814) (.branch 92 (.leaf 418675319) (.leaf 408875041))) (.branch 95 (.branch 94 (.leaf 399318971) (.leaf 390000326)) (.branch 96 (.leaf 380912548) (.leaf 372049285)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 363404393) (.leaf 354971921)) (.branch 100 (.leaf 346746106) (.leaf 338721368))) (.branch 103 (.branch 102 (.leaf 330892301) (.leaf 323253665)) (.branch 104 (.leaf 315800384) (.leaf 308527538))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 301430354) (.leaf 294504207)) (.branch 108 (.leaf 287744610) (.leaf 281147212))) (.branch 111 (.branch 110 (.leaf 274707789) (.leaf 268422244)) (.branch 112 (.leaf 262286602) (.leaf 256297003)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 250449698) (.leaf 244741050)) (.branch 116 (.leaf 239167526) (.leaf 233725693))) (.branch 119 (.branch 118 (.leaf 228412217) (.leaf 223223858)) (.branch 120 (.leaf 218157470) (.leaf 213209993)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 461).prefactor = (5380189792068273/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 461).cutoff/(generalMeanRows 461).c)).2 =
    (341442012332633/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 461).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 461).q*(generalMeanRows 461).c/2-2 = (441/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable108.value]
  have hcontinuation : (generalMeanRows 461).q*(generalMeanRows 461).cutoff/2-2 = (524/255:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable143.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 461).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 461).criticalRate j.val*(generalMeanRows 461).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 461).c*(generalMeanRows 461).criticalPoint j.val)).2-
      (generalMeanRows 461).J/2-(generalMeanRows 461).error (generalMeanGrid j.val)+
      (generalMeanRows 461).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 461).c)).2-
      (generalMeanRows 461).J/2-(generalMeanRows 461).error 4 := by
  have he : (generalMeanRows 461).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 461) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 461)
    (generalMeanRows_prefactorDomain 461) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0461

/-! Kernel-checked entropy margins for general spectral rectangle 462. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0462
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5530632630) (.branch 2 (.leaf 5348927489) (.leaf 5175328446))) (.branch 5 (.branch 4 (.leaf 5009369143) (.leaf 4850616339)) (.branch 6 (.leaf 4698667019) (.leaf 4553145820)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4413702712) (.leaf 4280010932)) (.branch 10 (.leaf 4151765112) (.leaf 4028679600))) (.branch 13 (.branch 12 (.leaf 3910486930) (.leaf 3796936444)) (.branch 14 (.leaf 3687793037) (.leaf 3582836008))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3481858024) (.branch 17 (.leaf 3384664163) (.leaf 3291071039))) (.branch 20 (.branch 19 (.leaf 3200906007) (.leaf 3114006424)) (.branch 21 (.leaf 3030218973) (.leaf 2949399042)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2871410150) (.leaf 2796123413)) (.branch 25 (.leaf 2723417060) (.leaf 2653175972))) (.branch 28 (.branch 27 (.leaf 2585291266) (.leaf 2519659905)) (.branch 29 (.leaf 2456184335) (.leaf 2394772147)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2335335767) (.branch 32 (.leaf 2277792163) (.leaf 2222062574))) (.branch 35 (.branch 34 (.leaf 2168072255) (.leaf 2115750247)) (.branch 36 (.leaf 2065029148) (.leaf 2015844913)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1968136661) (.leaf 1921846491)) (.branch 40 (.leaf 1876919317) (.leaf 1833302711))) (.branch 43 (.branch 42 (.leaf 1790946749) (.leaf 1749803879)) (.branch 44 (.leaf 1709828787) (.leaf 1670978274))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1633211145) (.branch 47 (.leaf 1596488097) (.leaf 1560771620))) (.branch 50 (.branch 49 (.leaf 1526025902) (.leaf 1492216738)) (.branch 51 (.leaf 1459311445) (.leaf 1427278784)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1396088884) (.leaf 1365713175)) (.branch 55 (.leaf 1336124314) (.leaf 1307296131))) (.branch 58 (.branch 57 (.leaf 1279203564) (.leaf 1251822605)) (.branch 59 (.leaf 1225130247) (.leaf 1199104436))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1173724022) (.branch 62 (.leaf 1148968713) (.leaf 1124819040))) (.branch 65 (.branch 64 (.leaf 1101256309) (.leaf 1078262568)) (.branch 66 (.leaf 1055820572) (.leaf 1033913747)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1012526159) (.leaf 991642487)) (.branch 70 (.leaf 971247988) (.leaf 951328478))) (.branch 73 (.branch 72 (.leaf 931870300) (.leaf 912860303)) (.branch 74 (.leaf 894285817) (.leaf 876134635))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 858394988) (.branch 77 (.leaf 841055527) (.leaf 824105307))) (.branch 80 (.branch 79 (.leaf 807533764) (.leaf 791330702)) (.branch 81 (.leaf 775486279) (.leaf 759990987)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 744835639) (.leaf 730011359)) (.branch 85 (.leaf 715509563) (.leaf 701321954))) (.branch 88 (.branch 87 (.leaf 687440502) (.leaf 673857439)) (.branch 89 (.leaf 660565248) (.leaf 647556648)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 634824589) (.branch 92 (.leaf 622362243) (.leaf 610162992))) (.branch 95 (.branch 94 (.leaf 598220421) (.leaf 586528313)) (.branch 96 (.leaf 575080635) (.leaf 563871538)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 552895345) (.leaf 542146548)) (.branch 100 (.leaf 531619797) (.leaf 521309900))) (.branch 103 (.branch 102 (.leaf 511211812) (.leaf 501320633)) (.branch 104 (.leaf 491631601) (.leaf 482140089))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 472841595) (.leaf 463731746)) (.branch 108 (.leaf 454806285) (.leaf 446061073))) (.branch 111 (.branch 110 (.leaf 437492082) (.leaf 429095392)) (.branch 112 (.leaf 420867186) (.leaf 412803750)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 404901464) (.leaf 397156806)) (.branch 116 (.leaf 389566343) (.leaf 382126729))) (.branch 119 (.branch 118 (.leaf 374834704) (.leaf 367687093)) (.branch 120 (.leaf 360680797) (.leaf 353812796)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 462).prefactor = (4993113878191157/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 462).cutoff/(generalMeanRows 462).c)).2 =
    (405217465901701/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 462).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 462).q*(generalMeanRows 462).c/2-2 = (593/800:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable154.value]
  have hcontinuation : (generalMeanRows 462).q*(generalMeanRows 462).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable151.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 462).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 462).criticalRate j.val*(generalMeanRows 462).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 462).c*(generalMeanRows 462).criticalPoint j.val)).2-
      (generalMeanRows 462).J/2-(generalMeanRows 462).error (generalMeanGrid j.val)+
      (generalMeanRows 462).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 462).c)).2-
      (generalMeanRows 462).J/2-(generalMeanRows 462).error 4 := by
  have he : (generalMeanRows 462).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 462) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 462)
    (generalMeanRows_prefactorDomain 462) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0462

/-! Kernel-checked entropy margins for general spectral rectangle 463. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0463
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5665552784) (.branch 2 (.leaf 5482215202) (.leaf 5307029740))) (.branch 5 (.branch 4 (.leaf 5139526870) (.leaf 4979270433)) (.branch 6 (.leaf 4825854735) (.leaf 4678901938)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4538059740) (.leaf 4402999277)) (.branch 10 (.leaf 4273413249) (.leaf 4149014217))) (.branch 13 (.branch 12 (.leaf 4029533069) (.leaf 3914717626)) (.branch 14 (.leaf 3804331377) (.leaf 3698152327))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3595971944) (.branch 17 (.leaf 3497594199) (.leaf 3402834688))) (.branch 20 (.branch 19 (.leaf 3311519820) (.leaf 3223486082)) (.branch 21 (.leaf 3138579353) (.leaf 3056654280)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2977573695) (.leaf 2901208086)) (.branch 25 (.leaf 2827435095) (.leaf 2756139069))) (.branch 28 (.branch 27 (.leaf 2687210630) (.leaf 2620546284)) (.branch 29 (.leaf 2556048059) (.leaf 2493623159)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2433183656) (.branch 32 (.leaf 2374646191) (.leaf 2317931704))) (.branch 35 (.branch 34 (.leaf 2262965177) (.leaf 2209675396)) (.branch 36 (.leaf 2157994730) (.leaf 2107858923)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2059206900) (.leaf 2011980585)) (.branch 40 (.leaf 1966124730) (.leaf 1921586759))) (.branch 43 (.branch 42 (.leaf 1878316616) (.leaf 1836266628)) (.branch 44 (.leaf 1795391368) (.leaf 1755647539))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1716993854) (.branch 47 (.leaf 1679390929) (.leaf 1642801179))) (.branch 50 (.branch 49 (.leaf 1607188725) (.leaf 1572519301)) (.branch 51 (.leaf 1538760170) (.leaf 1505880044)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1473849009) (.leaf 1442638454)) (.branch 55 (.leaf 1412221003) (.leaf 1382570452))) (.branch 58 (.branch 57 (.leaf 1353661712) (.leaf 1325470750)) (.branch 59 (.leaf 1297974536) (.leaf 1271150996))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1244978960) (.branch 62 (.leaf 1219438123) (.leaf 1194508999))) (.branch 65 (.branch 64 (.leaf 1170172881) (.leaf 1146411805)) (.branch 66 (.leaf 1123208515) (.leaf 1100546426)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1078409596) (.leaf 1056782693)) (.branch 70 (.leaf 1035650966) (.leaf 1015000222))) (.branch 73 (.branch 72 (.leaf 994816797) (.leaf 975087530)) (.branch 74 (.leaf 955799744) (.leaf 936941222))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 918500188) (.branch 77 (.leaf 900465284) (.leaf 882825554))) (.branch 80 (.branch 79 (.leaf 865570426) (.leaf 848689695)) (.branch 81 (.leaf 832173507) (.leaf 816012342)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 800197003) (.leaf 784718602)) (.branch 85 (.leaf 769568542) (.leaf 754738512))) (.branch 88 (.branch 87 (.leaf 740220469) (.leaf 726006631)) (.branch 89 (.leaf 712089464) (.leaf 698461671)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 685116188) (.branch 92 (.leaf 672046166) (.leaf 659244972))) (.branch 95 (.branch 94 (.leaf 646706171) (.leaf 634423526)) (.branch 96 (.leaf 622390986) (.leaf 610602680)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 599052910) (.leaf 587736144)) (.branch 100 (.leaf 576647013) (.leaf 565780299))) (.branch 103 (.branch 102 (.leaf 555130935) (.leaf 544693994)) (.branch 104 (.leaf 534464691) (.leaf 524438372))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 514610509) (.leaf 504976702)) (.branch 108 (.leaf 495532667) (.leaf 486274237))) (.branch 111 (.branch 110 (.leaf 477197355) (.leaf 468298072)) (.branch 112 (.leaf 459572542) (.leaf 451017021)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 442627859) (.leaf 434401502)) (.branch 116 (.leaf 426334486) (.leaf 418423435))) (.branch 119 (.branch 118 (.leaf 410665056) (.leaf 403056140)) (.branch 120 (.leaf 395593557) (.leaf 388274254)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 463).prefactor = (5027778678769581/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 463).cutoff/(generalMeanRows 463).c)).2 =
    (6454555036447/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 463).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 463).q*(generalMeanRows 463).c/2-2 = (2879/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable152.value]
  have hcontinuation : (generalMeanRows 463).q*(generalMeanRows 463).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable151.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 463).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 463).criticalRate j.val*(generalMeanRows 463).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 463).c*(generalMeanRows 463).criticalPoint j.val)).2-
      (generalMeanRows 463).J/2-(generalMeanRows 463).error (generalMeanGrid j.val)+
      (generalMeanRows 463).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 463).c)).2-
      (generalMeanRows 463).J/2-(generalMeanRows 463).error 4 := by
  have he : (generalMeanRows 463).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 463) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 463)
    (generalMeanRows_prefactorDomain 463) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0463

/-! Kernel-checked entropy margins for general spectral rectangle 464. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0464
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5339493294) (.branch 2 (.leaf 5156358130) (.leaf 4981449918))) (.branch 5 (.branch 4 (.leaf 4814298764) (.leaf 4654467960)) (.branch 6 (.leaf 4501551091) (.leaf 4355169450)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4214969726) (.leaf 4080621931)) (.branch 10 (.leaf 3951817528) (.leaf 3828267753))) (.branch 13 (.branch 12 (.leaf 3709702082) (.leaf 3595866854)) (.branch 14 (.leaf 3486524015) (.leaf 3381449973))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3280434555) (.branch 17 (.leaf 3183280055) (.leaf 3089800362))) (.branch 20 (.branch 19 (.leaf 2999820155) (.leaf 2913174176)) (.branch 21 (.leaf 2829706546) (.leaf 2749270146)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2671726044) (.leaf 2596942963)) (.branch 25 (.leaf 2524796787) (.leaf 2455170115))) (.branch 28 (.branch 27 (.leaf 2387951833) (.leaf 2323036726)) (.branch 29 (.leaf 2260325118) (.leaf 2199722532)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2141139378) (.branch 32 (.leaf 2084490659) (.leaf 2029695703))) (.branch 35 (.branch 34 (.leaf 1976677907) (.leaf 1925364500)) (.branch 36 (.leaf 1875686322) (.leaf 1827577617)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1780975843) (.leaf 1735821486)) (.branch 40 (.leaf 1692057893) (.leaf 1649631114))) (.branch 43 (.branch 42 (.leaf 1608489752) (.leaf 1568584824)) (.branch 44 (.leaf 1529869628) (.leaf 1492299623))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1455832311) (.branch 47 (.leaf 1420427128) (.leaf 1386045346))) (.branch 50 (.branch 49 (.leaf 1352649970) (.leaf 1320205653)) (.branch 51 (.leaf 1288678608) (.leaf 1258036527)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1228248509) (.leaf 1199284986)) (.branch 55 (.leaf 1171117654) (.leaf 1143719412))) (.branch 58 (.branch 57 (.leaf 1117064303) (.leaf 1091127454)) (.branch 59 (.leaf 1065885025) (.leaf 1041314159))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1017392930) (.branch 62 (.leaf 994100304) (.leaf 971416091))) (.branch 65 (.branch 64 (.leaf 949320909) (.leaf 927796141)) (.branch 66 (.leaf 906823904) (.leaf 886387010)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 866468937) (.leaf 847053795)) (.branch 70 (.leaf 828126303) (.leaf 809671752))) (.branch 73 (.branch 72 (.leaf 791675987) (.leaf 774125379)) (.branch 74 (.leaf 757006801) (.leaf 740307606))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 724015606) (.branch 77 (.leaf 708119053) (.leaf 692606616))) (.branch 80 (.branch 79 (.leaf 677467368) (.leaf 662690765)) (.branch 81 (.leaf 648266631) (.leaf 634185142)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 620436810) (.leaf 607012473)) (.branch 85 (.leaf 593903275) (.leaf 581100660))) (.branch 88 (.branch 87 (.leaf 568596355) (.leaf 556382360)) (.branch 89 (.leaf 544450937) (.leaf 532794600)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 521406104) (.branch 92 (.leaf 510278436) (.leaf 499404806))) (.branch 95 (.branch 94 (.leaf 488778637) (.leaf 478393558)) (.branch 96 (.leaf 468243397) (.leaf 458322171)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 448624079) (.leaf 439143498)) (.branch 100 (.leaf 429874975) (.leaf 420813217))) (.branch 103 (.branch 102 (.leaf 411953092) (.leaf 403289617)) (.branch 104 (.leaf 394817955) (.leaf 386533411))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 378431425) (.leaf 370507567)) (.branch 108 (.leaf 362757535) (.leaf 355177147))) (.branch 111 (.branch 110 (.leaf 347762340) (.leaf 340509164)) (.branch 112 (.leaf 333413778) (.leaf 326472447)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 319681540) (.leaf 313037523)) (.branch 116 (.leaf 306536959) (.leaf 300176503))) (.branch 119 (.branch 118 (.leaf 293952899) (.leaf 287862978)) (.branch 120 (.leaf 281903655) (.leaf 276071926)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 464).prefactor = (157410540540467/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 464).cutoff/(generalMeanRows 464).c)).2 =
    (188064841713321/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 464).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 464).q*(generalMeanRows 464).c/2-2 = (3223/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable132.value]
  have hcontinuation : (generalMeanRows 464).q*(generalMeanRows 464).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable145.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 464).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 464).criticalRate j.val*(generalMeanRows 464).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 464).c*(generalMeanRows 464).criticalPoint j.val)).2-
      (generalMeanRows 464).J/2-(generalMeanRows 464).error (generalMeanGrid j.val)+
      (generalMeanRows 464).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 464).c)).2-
      (generalMeanRows 464).J/2-(generalMeanRows 464).error 4 := by
  have he : (generalMeanRows 464).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 464) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 464)
    (generalMeanRows_prefactorDomain 464) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0464

/-! Kernel-checked entropy margins for general spectral rectangle 465. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0465
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5468393705) (.branch 2 (.leaf 5283470548) (.leaf 5106823582))) (.branch 5 (.branch 4 (.leaf 4937979763) (.leaf 4776499487)) (.branch 6 (.leaf 4621973671) (.leaf 4474021152)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4332286351) (.leaf 4196437191)) (.branch 10 (.leaf 4066163204) (.leaf 3941173842))) (.branch 13 (.branch 12 (.leaf 3821196931) (.leaf 3705977287)) (.branch 14 (.leaf 3595275446) (.leaf 3488866509))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3386539096) (.branch 17 (.leaf 3288094382) (.leaf 3193345219))) (.branch 20 (.branch 19 (.leaf 3102115329) (.leaf 3014238561)) (.branch 21 (.leaf 2929558213) (.leaf 2847926403)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2769203489) (.leaf 2693257538)) (.branch 25 (.leaf 2619963826) (.leaf 2549204387))) (.branch 28 (.branch 27 (.leaf 2480867582) (.leaf 2414847712)) (.branch 29 (.leaf 2351044650) (.leaf 2289363500)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2229714285) (.branch 32 (.leaf 2172011650) (.leaf 2116174587))) (.branch 35 (.branch 34 (.leaf 2062126183) (.leaf 2009793379)) (.branch 36 (.leaf 1959106749) (.leaf 1910000290)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1862411225) (.leaf 1816279829)) (.branch 40 (.leaf 1771549249) (.leaf 1728165348))) (.branch 43 (.branch 42 (.leaf 1686076559) (.leaf 1645233735)) (.branch 44 (.leaf 1605590026) (.leaf 1567100751))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1529723281) (.branch 47 (.leaf 1493416930) (.leaf 1458142856))) (.branch 50 (.branch 49 (.leaf 1423863955) (.leaf 1390544782)) (.branch 51 (.leaf 1358151454) (.leaf 1326651575)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1296014160) (.leaf 1266209561)) (.branch 55 (.leaf 1237209400) (.leaf 1208986505))) (.branch 58 (.branch 57 (.leaf 1181514850) (.leaf 1154769498)) (.branch 59 (.leaf 1128726549) (.leaf 1103363084))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1078657123) (.branch 62 (.leaf 1054587576) (.leaf 1031134201))) (.branch 65 (.branch 64 (.leaf 1008277564) (.leaf 985998999)) (.branch 66 (.leaf 964280573) (.leaf 943105053)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 922455870) (.leaf 902317089)) (.branch 70 (.leaf 882673383) (.leaf 863510000))) (.branch 73 (.branch 72 (.leaf 844812743) (.leaf 826567938)) (.branch 74 (.leaf 808762415) (.leaf 791383486))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 774418921) (.branch 77 (.leaf 757856928) (.leaf 741686136))) (.branch 80 (.branch 79 (.leaf 725895575) (.leaf 710474660)) (.branch 81 (.leaf 695413172) (.leaf 680701244)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 666329349) (.leaf 652288279)) (.branch 85 (.leaf 638569138) (.leaf 625163325))) (.branch 88 (.branch 87 (.leaf 612062526) (.leaf 599258697)) (.branch 89 (.leaf 586744058) (.leaf 574511077)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 562552467) (.branch 92 (.leaf 550861169) (.leaf 539430350))) (.branch 95 (.branch 94 (.leaf 528253388) (.leaf 517323867)) (.branch 96 (.leaf 506635569) (.leaf 496182467)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 485958714) (.leaf 475958641)) (.branch 100 (.leaf 466176748) (.leaf 456607697))) (.branch 103 (.branch 102 (.leaf 447246308) (.leaf 438087552)) (.branch 104 (.leaf 429126545) (.leaf 420358545))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 411778944) (.leaf 403383266)) (.branch 108 (.leaf 395167159) (.leaf 387126395))) (.branch 111 (.branch 110 (.leaf 379256862) (.leaf 371554563)) (.branch 112 (.leaf 364015607) (.leaf 356636214)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 349412702) (.leaf 342341490)) (.branch 116 (.leaf 335419092) (.leaf 328642114))) (.branch 119 (.branch 118 (.leaf 322007252) (.leaf 315511289)) (.branch 120 (.leaf 309151091) (.leaf 302923605)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 465).prefactor = (1014537250192863/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 465).cutoff/(generalMeanRows 465).c)).2 =
    (191911014524899/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 465).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 465).q*(generalMeanRows 465).c/2-2 = (3137/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable130.value]
  have hcontinuation : (generalMeanRows 465).q*(generalMeanRows 465).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable145.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 465).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 465).criticalRate j.val*(generalMeanRows 465).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 465).c*(generalMeanRows 465).criticalPoint j.val)).2-
      (generalMeanRows 465).J/2-(generalMeanRows 465).error (generalMeanGrid j.val)+
      (generalMeanRows 465).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 465).c)).2-
      (generalMeanRows 465).J/2-(generalMeanRows 465).error 4 := by
  have he : (generalMeanRows 465).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 465) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 465)
    (generalMeanRows_prefactorDomain 465) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0465

/-! Kernel-checked entropy margins for general spectral rectangle 466. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0466
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5905967260) (.branch 2 (.leaf 5720740455) (.leaf 5543700472))) (.branch 5 (.branch 4 (.leaf 5374374551) (.leaf 5212323596)) (.branch 6 (.leaf 5057139237) (.leaf 4908441204)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4765874981) (.leaf 4629109692)) (.branch 10 (.leaf 4497836209) (.leaf 4371765435))) (.branch 13 (.branch 12 (.leaf 4250626752) (.leaf 4134166622)) (.branch 14 (.leaf 4022147300) (.leaf 3914345681))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3810552232) (.branch 17 (.leaf 3710570025) (.leaf 3614213847))) (.branch 20 (.branch 19 (.leaf 3521309389) (.leaf 3431692495)) (.branch 21 (.leaf 3345208477) (.leaf 3261711478)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3181063891) (.leaf 3103135818)) (.branch 25 (.leaf 3027804571) (.leaf 2954954210))) (.branch 28 (.branch 27 (.leaf 2884475118) (.leaf 2816263600)) (.branch 29 (.leaf 2750221519) (.leaf 2686255950)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2624278865) (.branch 32 (.leaf 2564206832) (.leaf 2505960747))) (.branch 35 (.branch 34 (.leaf 2449465568) (.leaf 2394650079)) (.branch 36 (.leaf 2341446667) (.leaf 2289791112)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2239622387) (.leaf 2190882482)) (.branch 40 (.leaf 2143516226) (.leaf 2097471131))) (.branch 43 (.branch 42 (.leaf 2052697240) (.leaf 2009146984)) (.branch 44 (.leaf 1966775053) (.leaf 1925538271))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1885395477) (.branch 47 (.leaf 1846307420) (.leaf 1808236651))) (.branch 50 (.branch 49 (.leaf 1771147429) (.leaf 1735005631)) (.branch 51 (.leaf 1699778664) (.leaf 1665435386)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1631946030) (.leaf 1599282131)) (.branch 55 (.leaf 1567416461) (.leaf 1536322963))) (.branch 58 (.branch 57 (.leaf 1505976693) (.leaf 1476353763)) (.branch 59 (.leaf 1447431288) (.leaf 1419187335))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1391600876) (.branch 62 (.leaf 1364651741) (.leaf 1338320580))) (.branch 65 (.branch 64 (.leaf 1312588821) (.leaf 1287438629)) (.branch 66 (.leaf 1262852876) (.leaf 1238815101)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1215309483) (.leaf 1192320808)) (.branch 70 (.leaf 1169834441) (.leaf 1147836300))) (.branch 73 (.branch 72 (.leaf 1126312829) (.leaf 1105250971)) (.branch 74 (.leaf 1084638151) (.leaf 1064462250))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1044711583) (.branch 77 (.leaf 1025374886) (.leaf 1006441288))) (.branch 80 (.branch 79 (.leaf 987900300) (.leaf 969741796)) (.branch 81 (.leaf 951955999) (.leaf 934533462)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 917465056) (.leaf 900741958)) (.branch 85 (.leaf 884355634) (.leaf 868297830))) (.branch 88 (.branch 87 (.leaf 852560559) (.leaf 837136091)) (.branch 89 (.leaf 822016938) (.leaf 807195852)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 792665807) (.branch 92 (.leaf 778419996) (.leaf 764451819))) (.branch 95 (.branch 94 (.leaf 750754875) (.leaf 737322955)) (.branch 96 (.leaf 724150035) (.leaf 711230269)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 698557978) (.leaf 686127649)) (.branch 100 (.leaf 673933927) (.leaf 661971608))) (.branch 103 (.branch 102 (.leaf 650235633) (.leaf 638721085)) (.branch 104 (.leaf 627423181) (.leaf 616337271))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 605458829) (.leaf 594783450)) (.branch 108 (.leaf 584306846) (.leaf 574024844))) (.branch 111 (.branch 110 (.leaf 563933378) (.leaf 554028489)) (.branch 112 (.leaf 544306317) (.leaf 534763103)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 525395181) (.leaf 516198979)) (.branch 116 (.leaf 507171012) (.leaf 498307881))) (.branch 119 (.branch 118 (.leaf 489606270) (.leaf 481062946)) (.branch 120 (.leaf 472674751) (.leaf 464438602)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 466).prefactor = (1265671035118051/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 466).cutoff/(generalMeanRows 466).c)).2 =
    (21451405729771/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 466).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 466).q*(generalMeanRows 466).c/2-2 = (2707/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable126.value]
  have hcontinuation : (generalMeanRows 466).q*(generalMeanRows 466).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable151.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 466).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 466).criticalRate j.val*(generalMeanRows 466).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 466).c*(generalMeanRows 466).criticalPoint j.val)).2-
      (generalMeanRows 466).J/2-(generalMeanRows 466).error (generalMeanGrid j.val)+
      (generalMeanRows 466).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 466).c)).2-
      (generalMeanRows 466).J/2-(generalMeanRows 466).error 4 := by
  have he : (generalMeanRows 466).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 466) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 466)
    (generalMeanRows_prefactorDomain 466) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0466

/-! Kernel-checked entropy margins for general spectral rectangle 467. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0467
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5151804435) (.branch 2 (.leaf 4981868068) (.leaf 4819572481))) (.branch 5 (.branch 4 (.leaf 4664472833) (.leaf 4516156149)) (.branch 6 (.leaf 4374238535) (.leaf 4238362694)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4108195698) (.leaf 3983426985)) (.branch 10 (.leaf 3863766560) (.leaf 3748943370))) (.branch 13 (.branch 12 (.leaf 3638703826) (.leaf 3532810473)) (.branch 14 (.leaf 3431040777) (.leaf 3333186017))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3239050277) (.branch 17 (.leaf 3148449529) (.leaf 3061210783))) (.branch 20 (.branch 19 (.leaf 2977171321) (.leaf 2896177980)) (.branch 21 (.leaf 2818086504) (.leaf 2742760941)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2670073088) (.leaf 2599901981)) (.branch 25 (.leaf 2532133420) (.leaf 2466659533))) (.branch 28 (.branch 27 (.leaf 2403378373) (.leaf 2342193537)) (.branch 29 (.leaf 2283013822) (.leaf 2225752902)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2170329024) (.branch 32 (.leaf 2116664730) (.leaf 2064686595))) (.branch 35 (.branch 34 (.leaf 2014324989) (.leaf 1965513845)) (.branch 36 (.leaf 1918190449) (.leaf 1872295249)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1827771662) (.leaf 1784565909)) (.branch 40 (.leaf 1742626848) (.leaf 1701905831))) (.branch 43 (.branch 42 (.leaf 1662356556) (.leaf 1623934939)) (.branch 44 (.leaf 1586598987) (.leaf 1550308685))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1515025886) (.branch 47 (.leaf 1480714210) (.leaf 1447338943))) (.branch 50 (.branch 49 (.leaf 1414866955) (.leaf 1383266606)) (.branch 51 (.leaf 1352507676) (.leaf 1322561282)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1293399811) (.leaf 1264996854)) (.branch 55 (.leaf 1237327144) (.leaf 1210366493))) (.branch 58 (.branch 57 (.leaf 1184091743) (.leaf 1158480708)) (.branch 59 (.leaf 1133512128) (.leaf 1109165620))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1085421638) (.branch 62 (.leaf 1062261429) (.leaf 1039666991))) (.branch 65 (.branch 64 (.leaf 1017621044) (.leaf 996106986)) (.branch 66 (.leaf 975108868) (.leaf 954611358)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 934599712) (.leaf 915059748)) (.branch 70 (.leaf 895977819) (.leaf 877340787))) (.branch 73 (.branch 72 (.leaf 859136000) (.leaf 841351272)) (.branch 74 (.leaf 823974855) (.leaf 806995430))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 790402075) (.branch 77 (.leaf 774184258) (.leaf 758331814))) (.branch 80 (.branch 79 (.leaf 742834931) (.leaf 727684132)) (.branch 81 (.leaf 712870265) (.leaf 698384483)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 684218238) (.leaf 670363262)) (.branch 85 (.leaf 656811560) (.leaf 643555395))) (.branch 88 (.branch 87 (.leaf 630587280) (.leaf 617899965)) (.branch 89 (.leaf 605486432) (.leaf 593339880)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 581453720) (.branch 92 (.leaf 569821566) (.leaf 558437227))) (.branch 95 (.branch 94 (.leaf 547294697) (.leaf 536388153)) (.branch 96 (.leaf 525711942) (.leaf 515260579)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 505028739) (.leaf 495011251)) (.branch 100 (.leaf 485203092) (.leaf 475599382))) (.branch 103 (.branch 102 (.leaf 466195381) (.leaf 456986478)) (.branch 104 (.leaf 447968193) (.leaf 439136168))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 430486166) (.leaf 422014064)) (.branch 108 (.leaf 413715848) (.leaf 405587615))) (.branch 111 (.branch 110 (.leaf 397625564) (.leaf 389825993)) (.branch 112 (.leaf 382185299) (.leaf 374699972)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 367366591) (.leaf 360181824)) (.branch 116 (.leaf 353142425) (.leaf 346245228))) (.branch 119 (.branch 118 (.leaf 339487147) (.leaf 332865174)) (.branch 120 (.leaf 326376375) (.leaf 320017888)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 467).prefactor = (1198649269830967/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 467).cutoff/(generalMeanRows 467).c)).2 =
    (418778741453197/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 467).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 467).q*(generalMeanRows 467).c/2-2 = (1523/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable169.value]
  have hcontinuation : (generalMeanRows 467).q*(generalMeanRows 467).cutoff/2-2 = (1378/627:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable170.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 467).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 467).criticalRate j.val*(generalMeanRows 467).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 467).c*(generalMeanRows 467).criticalPoint j.val)).2-
      (generalMeanRows 467).J/2-(generalMeanRows 467).error (generalMeanGrid j.val)+
      (generalMeanRows 467).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 467).c)).2-
      (generalMeanRows 467).J/2-(generalMeanRows 467).error 4 := by
  have he : (generalMeanRows 467).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 467) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 467)
    (generalMeanRows_prefactorDomain 467) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0467

/-! Kernel-checked entropy margins for general spectral rectangle 468. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0468
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5696986856) (.branch 2 (.leaf 5509874095) (.leaf 5331076599))) (.branch 5 (.branch 4 (.leaf 5160118232) (.leaf 4996556580)) (.branch 6 (.leaf 4839980002) (.leaf 4690005008)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4546273908) (.leaf 4408452698)) (.branch 10 (.leaf 4276229165) (.leaf 4149311173))) (.branch 13 (.branch 12 (.leaf 4027425111) (.leaf 3910314488)) (.branch 14 (.leaf 3797738659) (.leaf 3689471657))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3585301136) (.branch 17 (.leaf 3485027403) (.leaf 3388462527))) (.branch 20 (.branch 19 (.leaf 3295429527) (.leaf 3205761625)) (.branch 21 (.leaf 3119301557) (.leaf 3035900943)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2955419698) (.leaf 2877725498)) (.branch 25 (.leaf 2802693278) (.leaf 2730204771))) (.branch 28 (.branch 27 (.leaf 2660148082) (.leaf 2592417288)) (.branch 29 (.leaf 2526912073) (.leaf 2463537384)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2402203111) (.branch 32 (.leaf 2342823793) (.leaf 2285318342))) (.branch 35 (.branch 34 (.leaf 2229609782) (.leaf 2175625010)) (.branch 36 (.leaf 2123294574) (.leaf 2072552459)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2023335893) (.leaf 1975585163)) (.branch 40 (.leaf 1929243443) (.leaf 1884256632))) (.branch 43 (.branch 42 (.leaf 1840573205) (.leaf 1798144067)) (.branch 44 (.leaf 1756922425) (.leaf 1716863661))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1677925214) (.branch 47 (.leaf 1640066470) (.leaf 1603248660))) (.branch 50 (.branch 49 (.leaf 1567434761) (.leaf 1532589404)) (.branch 51 (.leaf 1498678788) (.leaf 1465670599)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1433533933) (.leaf 1402239226)) (.branch 55 (.leaf 1371758181) (.leaf 1342063707))) (.branch 58 (.branch 57 (.leaf 1313129859) (.leaf 1284931779)) (.branch 59 (.leaf 1257445644) (.leaf 1230648611))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1204518774) (.branch 62 (.leaf 1179035114) (.leaf 1154177458))) (.branch 65 (.branch 64 (.leaf 1129926440) (.leaf 1106263458)) (.branch 66 (.leaf 1083170640) (.leaf 1060630813)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1038627462) (.leaf 1017144706)) (.branch 70 (.leaf 996167268) (.leaf 975680444))) (.branch 73 (.branch 72 (.leaf 955670079) (.leaf 936122540)) (.branch 74 (.leaf 917024696) (.leaf 898363893))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 880127931) (.branch 77 (.leaf 862305048) (.leaf 844883897))) (.branch 80 (.branch 79 (.leaf 827853531) (.leaf 811203383)) (.branch 81 (.leaf 794923250) (.leaf 779003280)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 763433953) (.leaf 748206070)) (.branch 85 (.leaf 733310739) (.leaf 718739361))) (.branch 88 (.branch 87 (.leaf 704483619) (.leaf 690535466)) (.branch 89 (.leaf 676887113) (.leaf 663531021)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 650459890) (.branch 92 (.leaf 637666647) (.leaf 625144440))) (.branch 95 (.branch 94 (.leaf 612886630) (.leaf 600886778)) (.branch 96 (.leaf 589138642) (.leaf 577636168)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 566373481) (.leaf 555344883)) (.branch 100 (.leaf 544544838) (.leaf 533967977))) (.branch 103 (.branch 102 (.leaf 523609081) (.leaf 513463083)) (.branch 104 (.leaf 503525060) (.leaf 493790227))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 484253933) (.leaf 474911655)) (.branch 108 (.leaf 465758997) (.leaf 456791681))) (.branch 111 (.branch 110 (.leaf 448005546) (.leaf 439396543)) (.branch 112 (.leaf 430960730) (.leaf 422694272)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 414593432) (.leaf 406654573)) (.branch 116 (.leaf 398874152) (.leaf 391248717))) (.branch 119 (.branch 118 (.leaf 383774904) (.leaf 376449436)) (.branch 120 (.leaf 369269118) (.leaf 362230834)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 468).prefactor = (2554243043418843/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 468).cutoff/(generalMeanRows 468).c)).2 =
    (39938654559091/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 468).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 468).q*(generalMeanRows 468).c/2-2 = (593/800:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable154.value]
  have hcontinuation : (generalMeanRows 468).q*(generalMeanRows 468).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable145.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 468).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 468).criticalRate j.val*(generalMeanRows 468).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 468).c*(generalMeanRows 468).criticalPoint j.val)).2-
      (generalMeanRows 468).J/2-(generalMeanRows 468).error (generalMeanGrid j.val)+
      (generalMeanRows 468).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 468).c)).2-
      (generalMeanRows 468).J/2-(generalMeanRows 468).error 4 := by
  have he : (generalMeanRows 468).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 468) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 468)
    (generalMeanRows_prefactorDomain 468) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0468

/-! Kernel-checked entropy margins for general spectral rectangle 469. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0469
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5937316618) (.branch 2 (.leaf 5748158287) (.leaf 5567352549))) (.branch 5 (.branch 4 (.leaf 5394420029) (.leaf 5228915361)) (.branch 6 (.leaf 5070424220) (.leaf 4918560674)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4772964805) (.leaf 4633300590)) (.branch 10 (.leaf 4499253977) (.leaf 4370531160))) (.branch 13 (.branch 12 (.leaf 4246857011) (.leaf 4127973667)) (.branch 14 (.leaf 4013639238) (.leaf 3903626634))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3797722495) (.branch 17 (.leaf 3695726213) (.leaf 3597449037))) (.branch 20 (.branch 19 (.leaf 3502713250) (.leaf 3411351418)) (.branch 21 (.leaf 3323205692) (.leaf 3238127171)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3155975316) (.leaf 3076617400)) (.branch 25 (.leaf 2999928006) (.leaf 2925788566))) (.branch 28 (.branch 27 (.leaf 2854086924) (.leaf 2784716938)) (.branch 29 (.leaf 2717578107) (.leaf 2652575227)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2589618069) (.branch 32 (.leaf 2528621079) (.leaf 2469503101))) (.branch 35 (.branch 34 (.leaf 2412187115) (.leaf 2356599996)) (.branch 36 (.leaf 2302672284) (.leaf 2250337979)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2199534335) (.leaf 2150201683)) (.branch 40 (.leaf 2102283248) (.leaf 2055724995))) (.branch 43 (.branch 42 (.leaf 2010475473) (.leaf 1966485671)) (.branch 44 (.leaf 1923708887) (.leaf 1882100600))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1841618352) (.branch 47 (.leaf 1802221637) (.leaf 1763871797))) (.branch 50 (.branch 49 (.leaf 1726531924) (.leaf 1690166767)) (.branch 51 (.leaf 1654742646) (.leaf 1620227367)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1586590149) (.leaf 1553801550)) (.branch 55 (.leaf 1521833396) (.leaf 1490658719))) (.branch 58 (.branch 57 (.leaf 1460251696) (.leaf 1430587588)) (.branch 59 (.leaf 1401642693) (.leaf 1373394286))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1345820575) (.branch 62 (.leaf 1318900656) (.leaf 1292614469))) (.branch 65 (.branch 64 (.leaf 1266942755) (.leaf 1241867020)) (.branch 66 (.leaf 1217369496) (.leaf 1193433108)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1170041442) (.leaf 1147178712)) (.branch 70 (.leaf 1124829731) (.leaf 1102979885))) (.branch 73 (.branch 72 (.leaf 1081615101) (.leaf 1060721832)) (.branch 74 (.leaf 1040287024) (.leaf 1020298097))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1000742923) (.branch 77 (.leaf 981609809) (.leaf 962887474))) (.branch 80 (.branch 79 (.leaf 944565030) (.leaf 926631969)) (.branch 81 (.leaf 909078143) (.leaf 891893751)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 875069321) (.leaf 858595698)) (.branch 85 (.leaf 842464033) (.leaf 826665763))) (.branch 88 (.branch 87 (.leaf 811192606) (.leaf 796036548)) (.branch 89 (.leaf 781189828) (.leaf 766644933)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 752394584) (.branch 92 (.leaf 738431730) (.leaf 724749534))) (.branch 95 (.branch 94 (.leaf 711341369) (.leaf 698200810)) (.branch 96 (.leaf 685321623) (.leaf 672697757)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 660323343) (.leaf 648192680)) (.branch 100 (.leaf 636300233) (.leaf 624640626))) (.branch 103 (.branch 102 (.leaf 613208634) (.leaf 601999181)) (.branch 104 (.leaf 591007331) (.leaf 580228287))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 569657380) (.leaf 559290071)) (.branch 108 (.leaf 549121943) (.leaf 539148695))) (.branch 111 (.branch 110 (.leaf 529366143) (.leaf 519770212)) (.branch 112 (.leaf 510356933) (.leaf 501122440)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 492062966) (.leaf 483174842)) (.branch 116 (.leaf 474454489) (.leaf 465898421))) (.branch 119 (.branch 118 (.leaf 457503236) (.leaf 449265617)) (.branch 120 (.leaf 441182331) (.leaf 433250220)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 469).prefactor = (5144538575484189/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 469).cutoff/(generalMeanRows 469).c)).2 =
    (415197151617551/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 469).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 469).q*(generalMeanRows 469).c/2-2 = (2793/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable128.value]
  have hcontinuation : (generalMeanRows 469).q*(generalMeanRows 469).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable145.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 469).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 469).criticalRate j.val*(generalMeanRows 469).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 469).c*(generalMeanRows 469).criticalPoint j.val)).2-
      (generalMeanRows 469).J/2-(generalMeanRows 469).error (generalMeanGrid j.val)+
      (generalMeanRows 469).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 469).c)).2-
      (generalMeanRows 469).J/2-(generalMeanRows 469).error 4 := by
  have he : (generalMeanRows 469).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 469) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 469)
    (generalMeanRows_prefactorDomain 469) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0469

/-! Kernel-checked entropy margins for general spectral rectangle 470. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0470
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6223419453) (.branch 2 (.leaf 6025099034) (.leaf 5835578115))) (.branch 5 (.branch 4 (.leaf 5654350260) (.leaf 5480944973)) (.branch 6 (.leaf 5314924568) (.leaf 5155881361)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5003435167) (.leaf 4857231055)) (.branch 10 (.leaf 4716937315) (.leaf 4582243641))) (.branch 13 (.branch 12 (.leaf 4452859472) (.leaf 4328512493)) (.branch 14 (.leaf 4208947281) (.leaf 4093924055))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3983217552) (.branch 17 (.leaf 3876615992) (.leaf 3773920130))) (.branch 20 (.branch 19 (.leaf 3674942389) (.leaf 3579506064)) (.branch 21 (.leaf 3487444585) (.leaf 3398600846)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3312826580) (.leaf 3229981782)) (.branch 25 (.leaf 3149934179) (.leaf 3072558737))) (.branch 28 (.branch 27 (.leaf 2997737205) (.leaf 2925357690)) (.branch 29 (.leaf 2855314265) (.leaf 2787506605)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2721839642) (.branch 32 (.leaf 2658223256) (.leaf 2596571974))) (.branch 35 (.branch 34 (.leaf 2536804695) (.leaf 2478844439)) (.branch 36 (.leaf 2422618102) (.leaf 2368056231)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2315092819) (.leaf 2263665109)) (.branch 40 (.leaf 2213713403) (.leaf 2165180899))) (.branch 43 (.branch 42 (.leaf 2118013526) (.leaf 2072159790)) (.branch 44 (.leaf 2027570638) (.leaf 1984199320))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1942001265) (.branch 47 (.leaf 1900933966) (.leaf 1860956866))) (.branch 50 (.branch 49 (.leaf 1822031255) (.leaf 1784120173)) (.branch 51 (.leaf 1747188319) (.leaf 1711201961)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1676128857) (.leaf 1641938177)) (.branch 55 (.leaf 1608600431) (.leaf 1576087398))) (.branch 58 (.branch 57 (.leaf 1544372067) (.leaf 1513428570)) (.branch 59 (.leaf 1483232129) (.leaf 1453758998))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1424986415) (.branch 62 (.leaf 1396892551) (.leaf 1369456467))) (.branch 65 (.branch 64 (.leaf 1342658067) (.leaf 1316478060)) (.branch 66 (.leaf 1290897921) (.leaf 1265899851)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1241466749) (.leaf 1217582171)) (.branch 70 (.leaf 1194230306) (.leaf 1171395942))) (.branch 73 (.branch 72 (.leaf 1149064441) (.leaf 1127221709)) (.branch 74 (.leaf 1105854175) (.leaf 1084948765))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1064492880) (.branch 77 (.leaf 1044474373) (.leaf 1024881532))) (.branch 80 (.branch 79 (.leaf 1005703059) (.leaf 986928049)) (.branch 81 (.leaf 968545979) (.leaf 950546685)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 932920349) (.leaf 915657487)) (.branch 85 (.leaf 898748930) (.leaf 882185812))) (.branch 88 (.branch 87 (.leaf 865959561) (.leaf 850061879)) (.branch 89 (.leaf 834484740) (.leaf 819220372)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 804261247) (.branch 92 (.leaf 789600077) (.leaf 775229795))) (.branch 95 (.branch 94 (.leaf 761143555) (.leaf 747334719)) (.branch 96 (.leaf 733796849) (.leaf 720523698)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 707509205) (.leaf 694747489)) (.branch 100 (.leaf 682232838) (.leaf 669959704))) (.branch 103 (.branch 102 (.leaf 657922700) (.leaf 646116589)) (.branch 104 (.leaf 634536283) (.leaf 623176835))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 612033433) (.leaf 601101399)) (.branch 108 (.leaf 590376180) (.leaf 579853346))) (.branch 111 (.branch 110 (.leaf 569528586) (.leaf 559397700)) (.branch 112 (.leaf 549456601) (.leaf 539701307)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 530127939) (.leaf 520732717)) (.branch 116 (.leaf 511511957) (.leaf 502462067))) (.branch 119 (.branch 118 (.leaf 493579546) (.leaf 484860979)) (.branch 120 (.leaf 476303035) (.leaf 467902465)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 470).prefactor = (2683704038315881/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 470).cutoff/(generalMeanRows 470).c)).2 =
    (418518012927717/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 470).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 470).q*(generalMeanRows 470).c/2-2 = (171/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable097.value]
  have hcontinuation : (generalMeanRows 470).q*(generalMeanRows 470).cutoff/2-2 = (1054/507:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable144.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 470).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 470).criticalRate j.val*(generalMeanRows 470).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 470).c*(generalMeanRows 470).criticalPoint j.val)).2-
      (generalMeanRows 470).J/2-(generalMeanRows 470).error (generalMeanGrid j.val)+
      (generalMeanRows 470).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 470).c)).2-
      (generalMeanRows 470).J/2-(generalMeanRows 470).error 4 := by
  have he : (generalMeanRows 470).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 470) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 470)
    (generalMeanRows_prefactorDomain 470) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0470

/-! Kernel-checked entropy margins for general spectral rectangle 471. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0471
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5033286464) (.branch 2 (.leaf 4860052575) (.leaf 4694721516))) (.branch 5 (.branch 4 (.leaf 4536832824) (.leaf 4385958980)) (.branch 6 (.leaf 4241702528) (.leaf 4103693509)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3971587159) (.leaf 3845061842)) (.branch 10 (.leaf 3723817192) (.leaf 3607572427))) (.branch 13 (.branch 12 (.leaf 3496064832) (.leaf 3389048378)) (.branch 14 (.leaf 3286292470) (.leaf 3187580801))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3092710315) (.branch 17 (.leaf 3001490252) (.leaf 2913741277))) (.branch 20 (.branch 19 (.leaf 2829294683) (.leaf 2747991653)) (.branch 21 (.leaf 2669682586) (.leaf 2594226481)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2521490355) (.leaf 2451348723)) (.branch 25 (.leaf 2383683102) (.leaf 2318381564))) (.branch 28 (.branch 27 (.leaf 2255338315) (.leaf 2194453306)) (.branch 29 (.leaf 2135631874) (.leaf 2078784408)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2023826038) (.branch 32 (.leaf 1970676343) (.leaf 1919259085))) (.branch 35 (.branch 34 (.leaf 1869501957) (.leaf 1821336348)) (.branch 36 (.leaf 1774697126) (.leaf 1729522434)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1685753500) (.leaf 1643334456)) (.branch 40 (.leaf 1602212176) (.leaf 1562336117))) (.branch 43 (.branch 42 (.leaf 1523658176) (.leaf 1486132549)) (.branch 44 (.leaf 1449715608) (.leaf 1414365776))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1380043417) (.branch 47 (.leaf 1346710731) (.leaf 1314331653))) (.branch 50 (.branch 49 (.leaf 1282871759) (.leaf 1252298180)) (.branch 51 (.leaf 1222579518) (.leaf 1193685770)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1165588254) (.leaf 1138259540)) (.branch 55 (.leaf 1111673385) (.leaf 1085804674))) (.branch 58 (.branch 57 (.leaf 1060629360) (.leaf 1036124410)) (.branch 59 (.leaf 1012267758) (.leaf 989038250))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 966415603) (.branch 62 (.leaf 944380362) (.leaf 922913859))) (.branch 65 (.branch 64 (.leaf 901998172) (.leaf 881616092)) (.branch 66 (.leaf 861751089) (.leaf 842387278)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 823509386) (.leaf 805102730)) (.branch 70 (.leaf 787153184) (.leaf 769647152))) (.branch 73 (.branch 72 (.leaf 752571550) (.leaf 735913777)) (.branch 74 (.leaf 719661693) (.leaf 703803603))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 688328232) (.branch 77 (.leaf 673224708) (.leaf 658482547))) (.branch 80 (.branch 79 (.leaf 644091630) (.leaf 630042193)) (.branch 81 (.leaf 616324808) (.leaf 602930371)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 589850087) (.leaf 577075455)) (.branch 85 (.leaf 564598260) (.leaf 552410559))) (.branch 88 (.branch 87 (.leaf 540504668) (.leaf 528873153)) (.branch 89 (.leaf 517508822) (.leaf 506404712)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 495554079) (.branch 92 (.leaf 484950395) (.leaf 474587333))) (.branch 95 (.branch 94 (.leaf 464458763) (.leaf 454558743)) (.branch 96 (.leaf 444881513) (.leaf 435421486)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 426173244) (.leaf 417131529)) (.branch 100 (.leaf 408291240) (.leaf 399647424))) (.branch 103 (.branch 102 (.leaf 391195273) (.leaf 382930118)) (.branch 104 (.leaf 374847425) (.leaf 366942786))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 359211922) (.leaf 351650670)) (.branch 108 (.leaf 344254987) (.leaf 337020940))) (.branch 111 (.branch 110 (.leaf 329944703) (.leaf 323022558)) (.branch 112 (.leaf 316250886) (.leaf 309626165)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 303144968) (.leaf 296803962)) (.branch 116 (.leaf 290599899) (.leaf 284529617))) (.branch 119 (.branch 118 (.leaf 278590038) (.leaf 272778165)) (.branch 120 (.leaf 267091075) (.leaf 261525925)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 471).prefactor = (615524730501991/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 471).cutoff/(generalMeanRows 471).c)).2 =
    (200247466686133/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 471).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 471).q*(generalMeanRows 471).c/2-2 = (261/320:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable137.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 471).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 471).criticalRate j.val*(generalMeanRows 471).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 471).c*(generalMeanRows 471).criticalPoint j.val)).2-
      (generalMeanRows 471).J/2-(generalMeanRows 471).error (generalMeanGrid j.val)+
      (generalMeanRows 471).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 471).c)).2-
      (generalMeanRows 471).J/2-(generalMeanRows 471).error 4 := by
  have he : (generalMeanRows 471).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 471) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 471)
    (generalMeanRows_prefactorDomain 471) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0471

/-! Kernel-checked entropy margins for general spectral rectangle 472. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0472
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6008606893) (.branch 2 (.leaf 5808220842) (.leaf 5616773662))) (.branch 5 (.branch 4 (.leaf 5433755106) (.leaf 5258690949)) (.branch 6 (.leaf 5091139841) (.leaf 4930690509)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4776959241) (.leaf 4629587639)) (.branch 10 (.leaf 4488240589) (.leaf 4352604437))) (.branch 13 (.branch 12 (.leaf 4222385329) (.leaf 4097307719)) (.branch 14 (.leaf 3977113001) (.leaf 3861558273))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3750415205) (.branch 17 (.leaf 3643469003) (.leaf 3540517464))) (.branch 20 (.branch 19 (.leaf 3441370112) (.leaf 3345847393)) (.branch 21 (.leaf 3253779948) (.leaf 3165007935)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3079380408) (.leaf 2996754738)) (.branch 25 (.leaf 2916996083) (.leaf 2839976897))) (.branch 28 (.branch 27 (.leaf 2765576470) (.leaf 2693680506)) (.branch 29 (.leaf 2624180731) (.leaf 2556974523)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2491964576) (.branch 32 (.leaf 2429058583) (.leaf 2368168936))) (.branch 35 (.branch 34 (.leaf 2309212455) (.leaf 2252110129)) (.branch 36 (.leaf 2196786876) (.leaf 2143171318)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2091195570) (.leaf 2040795046)) (.branch 40 (.leaf 1991908272) (.leaf 1944476714))) (.branch 43 (.branch 42 (.leaf 1898444616) (.leaf 1853758850)) (.branch 44 (.leaf 1810368769) (.leaf 1768226078))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1727284703) (.branch 47 (.leaf 1687500679) (.leaf 1648832032))) (.branch 50 (.branch 49 (.leaf 1611238677) (.leaf 1574682321)) (.branch 51 (.leaf 1539126368) (.leaf 1504535831)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1470877251) (.leaf 1438118621)) (.branch 55 (.leaf 1406229306) (.leaf 1375179981))) (.branch 58 (.branch 57 (.leaf 1344942563) (.leaf 1315490145)) (.branch 59 (.leaf 1286796947) (.leaf 1258838252))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1231590357) (.branch 62 (.leaf 1205030527) (.leaf 1179136943))) (.branch 65 (.branch 64 (.leaf 1153888662) (.leaf 1129265573)) (.branch 66 (.leaf 1105248359) (.leaf 1081818458)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1058958031) (.leaf 1036649923)) (.branch 70 (.leaf 1014877637) (.leaf 993625298))) (.branch 73 (.branch 72 (.leaf 972877631) (.leaf 952619928)) (.branch 74 (.leaf 932838026) (.leaf 913518281))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 894647546) (.branch 77 (.leaf 876213147) (.leaf 858202865))) (.branch 80 (.branch 79 (.leaf 840604912) (.leaf 823407918)) (.branch 81 (.leaf 806600907) (.leaf 790173284)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 774114819) (.leaf 758415628)) (.branch 85 (.leaf 743066161) (.leaf 728057189))) (.branch 88 (.branch 87 (.leaf 713379789) (.leaf 699025331)) (.branch 89 (.leaf 684985467) (.leaf 671252119)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 657817471) (.branch 92 (.leaf 644673952) (.leaf 631814233))) (.branch 95 (.branch 94 (.leaf 619231214) (.leaf 606918016)) (.branch 96 (.leaf 594867972) (.leaf 583074617)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 571531685) (.leaf 560233098)) (.branch 100 (.leaf 549172957) (.leaf 538345542))) (.branch 103 (.branch 102 (.leaf 527745297) (.leaf 517366830)) (.branch 104 (.leaf 507204905) (.leaf 497254437))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 487510485) (.leaf 477968246)) (.branch 108 (.leaf 468623056) (.leaf 459470378))) (.branch 111 (.branch 110 (.leaf 450505801) (.leaf 441725035)) (.branch 112 (.leaf 433123908) (.leaf 424698360)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 416444440) (.leaf 408358303)) (.branch 116 (.leaf 400436205) (.leaf 392674503))) (.branch 119 (.branch 118 (.leaf 385069646) (.leaf 377618177)) (.branch 120 (.leaf 370316728) (.leaf 363162017)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 472).prefactor = (5419474409823687/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 472).cutoff/(generalMeanRows 472).c)).2 =
    (388325598231483/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 472).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 472).q*(generalMeanRows 472).c/2-2 = (3/4:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable019.value]
  have hcontinuation : (generalMeanRows 472).q*(generalMeanRows 472).cutoff/2-2 = (524/255:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable143.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 472).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 472).criticalRate j.val*(generalMeanRows 472).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 472).c*(generalMeanRows 472).criticalPoint j.val)).2-
      (generalMeanRows 472).J/2-(generalMeanRows 472).error (generalMeanGrid j.val)+
      (generalMeanRows 472).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 472).c)).2-
      (generalMeanRows 472).J/2-(generalMeanRows 472).error 4 := by
  have he : (generalMeanRows 472).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 472) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 472)
    (generalMeanRows_prefactorDomain 472) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0472

/-! Kernel-checked entropy margins for general spectral rectangle 473. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0473
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5232652576) (.branch 2 (.leaf 5062675576) (.leaf 4900340928))) (.branch 5 (.branch 4 (.leaf 4745201083) (.leaf 4596840683)) (.branch 6 (.leaf 4454873745) (.leaf 4318941155)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4188708408) (.leaf 4063863585)) (.branch 10 (.leaf 3944115537) (.leaf 3829192233))) (.branch 13 (.branch 12 (.leaf 3718839274) (.leaf 3612818541)) (.branch 14 (.leaf 3510906966) (.leaf 3412895417))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3318587676) (.branch 17 (.leaf 3227799507) (.leaf 3140357802))) (.branch 20 (.branch 19 (.leaf 3056099799) (.leaf 2974872365)) (.branch 21 (.leaf 2896531331) (.leaf 2820940891)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2747973034) (.leaf 2677507029)) (.branch 25 (.leaf 2609428951) (.leaf 2543631232))) (.branch 28 (.branch 27 (.leaf 2480012256) (.leaf 2418475979)) (.branch 29 (.leaf 2358931575) (.leaf 2301293112)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2245479243) (.branch 32 (.leaf 2191412933) (.leaf 2139021184))) (.branch 35 (.branch 34 (.leaf 2088234802) (.leaf 2038988158)) (.branch 36 (.leaf 1991218984) (.leaf 1944868170)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1899879577) (.leaf 1856199868)) (.branch 40 (.leaf 1813778343) (.leaf 1772566787))) (.branch 43 (.branch 42 (.leaf 1732519330) (.leaf 1693592314)) (.branch 44 (.leaf 1655744165) (.leaf 1618935283))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1583127925) (.branch 47 (.leaf 1548286107) (.leaf 1514375508))) (.branch 50 (.branch 49 (.leaf 1481363376) (.leaf 1449218447)) (.branch 51 (.leaf 1417910860) (.leaf 1387412089)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1357694865) (.leaf 1328733115)) (.branch 55 (.leaf 1300501897) (.leaf 1272977340))) (.branch 58 (.branch 57 (.leaf 1246136594) (.leaf 1219957769)) (.branch 59 (.leaf 1194419894) (.leaf 1169502866))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1145187406) (.branch 62 (.leaf 1121455023) (.leaf 1098287968))) (.branch 65 (.branch 64 (.leaf 1075669200) (.leaf 1053582354)) (.branch 66 (.leaf 1032011704) (.leaf 1010942135)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 990359112) (.leaf 970248653)) (.branch 70 (.leaf 950597303) (.leaf 931392108))) (.branch 73 (.branch 72 (.leaf 912620595) (.leaf 894270744)) (.branch 74 (.leaf 876330972) (.leaf 858790113))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 841637395) (.branch 77 (.leaf 824862426) (.leaf 808455178))) (.branch 80 (.branch 79 (.leaf 792405964) (.leaf 776705433)) (.branch 81 (.leaf 761344547) (.leaf 746314571)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 731607062) (.leaf 717213852)) (.branch 85 (.leaf 703127038) (.leaf 689338974))) (.branch 88 (.branch 87 (.leaf 675842256) (.leaf 662629715)) (.branch 89 (.leaf 649694406) (.leaf 637029600)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 624628772) (.branch 92 (.leaf 612485598) (.leaf 600593945))) (.branch 95 (.branch 94 (.leaf 588947861) (.leaf 577541572)) (.branch 96 (.leaf 566369471) (.leaf 555426117)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 544706224) (.leaf 534204656)) (.branch 100 (.leaf 523916424) (.leaf 513836677))) (.branch 103 (.branch 102 (.leaf 503960702) (.leaf 494283913)) (.branch 104 (.leaf 484801851) (.leaf 475510177))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 466404669) (.leaf 457481218)) (.branch 108 (.leaf 448735825) (.leaf 440164593))) (.branch 111 (.branch 110 (.leaf 431763729) (.leaf 423529537)) (.branch 112 (.leaf 415458416) (.leaf 407546858)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 399791443) (.leaf 392188836)) (.branch 116 (.leaf 384735786) (.leaf 377429124))) (.branch 119 (.branch 118 (.leaf 370265755) (.leaf 363242665)) (.branch 120 (.leaf 356356908) (.leaf 349605613)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 473).prefactor = (4817202937555087/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 473).cutoff/(generalMeanRows 473).c)).2 =
    (432277485760663/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 473).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 473).q*(generalMeanRows 473).c/2-2 = (1481/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable171.value]
  have hcontinuation : (generalMeanRows 473).q*(generalMeanRows 473).cutoff/2-2 = (2078/935:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable172.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 473).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 473).criticalRate j.val*(generalMeanRows 473).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 473).c*(generalMeanRows 473).criticalPoint j.val)).2-
      (generalMeanRows 473).J/2-(generalMeanRows 473).error (generalMeanGrid j.val)+
      (generalMeanRows 473).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 473).c)).2-
      (generalMeanRows 473).J/2-(generalMeanRows 473).error 4 := by
  have he : (generalMeanRows 473).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 473) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 473)
    (generalMeanRows_prefactorDomain 473) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0473

/-! Kernel-checked entropy margins for general spectral rectangle 474. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0474
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5120258004) (.branch 2 (.leaf 4948865544) (.leaf 4785233867))) (.branch 5 (.branch 4 (.leaf 4628909460) (.leaf 4479471368)) (.branch 6 (.leaf 4336528347) (.leaf 4199716322)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4068696115) (.leaf 3943151392)) (.branch 10 (.leaf 3822786829) (.leaf 3707326443))) (.branch 13 (.branch 12 (.leaf 3596512090) (.leaf 3490102096)) (.branch 14 (.leaf 3387870022) (.leaf 3289603526))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3195103339) (.branch 17 (.leaf 3104182319) (.leaf 3016664589))) (.branch 20 (.branch 19 (.leaf 2932384749) (.leaf 2851187143)) (.branch 21 (.leaf 2772925198) (.leaf 2697460808)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2624663764) (.leaf 2554411232)) (.branch 25 (.leaf 2486587275) (.leaf 2421082398))) (.branch 28 (.branch 27 (.leaf 2357793138) (.leaf 2296621683)) (.branch 29 (.leaf 2237475509) (.leaf 2180267058)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2124913422) (.branch 32 (.leaf 2071336067) (.leaf 2019460557))) (.branch 35 (.branch 34 (.leaf 1969216316) (.leaf 1920536389)) (.branch 36 (.leaf 1873357232) (.leaf 1827618510)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1783262906) (.leaf 1740235951)) (.branch 40 (.leaf 1698485857) (.leaf 1657963360))) (.branch 43 (.branch 42 (.leaf 1618621586) (.leaf 1580415905)) (.branch 44 (.leaf 1543303814) (.leaf 1507244815))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1472200303) (.branch 47 (.leaf 1438133464) (.leaf 1405009178))) (.branch 50 (.branch 49 (.leaf 1372793925) (.leaf 1341455700)) (.branch 51 (.leaf 1310963934) (.leaf 1281289413)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1252404212) (.leaf 1224281622)) (.branch 55 (.leaf 1196896092) (.leaf 1170223165))) (.branch 58 (.branch 57 (.leaf 1144239426) (.leaf 1118922442)) (.branch 59 (.leaf 1094250721) (.leaf 1070203656))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1046761489) (.branch 62 (.leaf 1023905262) (.leaf 1001616780))) (.branch 65 (.branch 64 (.leaf 979878576) (.leaf 958673871)) (.branch 66 (.leaf 937986544) (.leaf 917801101)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 898102641) (.leaf 878876833)) (.branch 70 (.leaf 860109886) (.leaf 841788524))) (.branch 73 (.branch 72 (.leaf 823899964) (.leaf 806431890)) (.branch 74 (.leaf 789372436) (.leaf 772710162))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 756434038) (.branch 77 (.leaf 740533422) (.leaf 724998045))) (.branch 80 (.branch 79 (.leaf 709817995) (.leaf 694983702)) (.branch 81 (.leaf 680485919) (.leaf 666315713)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 652464451) (.leaf 638923783)) (.branch 85 (.leaf 625685635) (.leaf 612742196))) (.branch 88 (.branch 87 (.leaf 600085907) (.leaf 587709449)) (.branch 89 (.leaf 575605736) (.leaf 563767905)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 552189305) (.branch 92 (.leaf 540863492) (.leaf 529784218))) (.branch 95 (.branch 94 (.leaf 518945424) (.leaf 508341235)) (.branch 96 (.leaf 497965949) (.leaf 487814034)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 477880119) (.leaf 468158991)) (.branch 100 (.leaf 458645585) (.leaf 449334984))) (.branch 103 (.branch 102 (.leaf 440222407) (.leaf 431303211)) (.branch 104 (.leaf 422572880) (.leaf 414027025))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 405661378) (.leaf 397471787)) (.branch 108 (.leaf 389454211) (.leaf 381604722))) (.branch 111 (.branch 110 (.leaf 373919493) (.leaf 366394800)) (.branch 112 (.leaf 359027019) (.leaf 351812618)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 344748158) (.leaf 337830291)) (.branch 116 (.leaf 331055752) (.leaf 324421362))) (.branch 119 (.branch 118 (.leaf 317924019) (.leaf 311560703)) (.branch 120 (.leaf 305328468) (.leaf 299224442)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 474).prefactor = (609866945105453/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 474).cutoff/(generalMeanRows 474).c)).2 =
    (26066754193571/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 474).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 474).q*(generalMeanRows 474).c/2-2 = (313/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable173.value]
  have hcontinuation : (generalMeanRows 474).q*(generalMeanRows 474).cutoff/2-2 = (2078/935:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable172.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 474).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 474).criticalRate j.val*(generalMeanRows 474).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 474).c*(generalMeanRows 474).criticalPoint j.val)).2-
      (generalMeanRows 474).J/2-(generalMeanRows 474).error (generalMeanGrid j.val)+
      (generalMeanRows 474).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 474).c)).2-
      (generalMeanRows 474).J/2-(generalMeanRows 474).error 4 := by
  have he : (generalMeanRows 474).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 474) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 474)
    (generalMeanRows_prefactorDomain 474) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0474

/-! Kernel-checked entropy margins for general spectral rectangle 475. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0475
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5811240402) (.branch 2 (.leaf 5609149911) (.leaf 5416136003))) (.branch 5 (.branch 4 (.leaf 5231684120) (.leaf 5055315841)) (.branch 6 (.leaf 4886585730) (.leaf 4725078529)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4570406636) (.leaf 4422207853)) (.branch 10 (.leaf 4280143353) (.leaf 4143895851))) (.branch 13 (.branch 12 (.leaf 4013167944) (.leaf 3887680613)) (.branch 14 (.leaf 3767171857) (.leaf 3651395454))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3540119825) (.branch 17 (.leaf 3433127002) (.leaf 3330211680))) (.branch 20 (.branch 19 (.leaf 3231180347) (.leaf 3135850488)) (.branch 21 (.leaf 3044049848) (.leaf 2955615760)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2870394515) (.leaf 2788240795)) (.branch 25 (.leaf 2709017130) (.leaf 2632593412))) (.branch 28 (.branch 27 (.leaf 2558846433) (.leaf 2487659465)) (.branch 29 (.leaf 2418921862) (.leaf 2352528694)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2288380408) (.branch 32 (.leaf 2226382508) (.leaf 2166445260))) (.branch 35 (.branch 34 (.leaf 2108483415) (.leaf 2052415950)) (.branch 36 (.leaf 1998165828) (.leaf 1945659773)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1894828056) (.leaf 1845604302)) (.branch 40 (.leaf 1797925298) (.leaf 1751730826))) (.branch 43 (.branch 42 (.leaf 1706963496) (.leaf 1663568596)) (.branch 44 (.leaf 1621493943) (.leaf 1580689755))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1541108518) (.branch 47 (.leaf 1502704872) (.leaf 1465435492))) (.branch 50 (.branch 49 (.leaf 1429258990) (.leaf 1394135809)) (.branch 51 (.leaf 1360028131) (.leaf 1326899791)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1294716189) (.leaf 1263444217)) (.branch 55 (.leaf 1233052177) (.leaf 1203509719))) (.branch 58 (.branch 57 (.leaf 1174787769) (.leaf 1146858467)) (.branch 59 (.leaf 1119695111) (.leaf 1093272098))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1067564872) (.branch 62 (.leaf 1042549875) (.leaf 1018204495))) (.branch 65 (.branch 64 (.leaf 994507029) (.leaf 971436633)) (.branch 66 (.leaf 948973286) (.leaf 927097749)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 905791533) (.leaf 885036859)) (.branch 70 (.leaf 864816632) (.leaf 845114403))) (.branch 73 (.branch 72 (.leaf 825914346) (.leaf 807201227)) (.branch 74 (.leaf 788960378) (.leaf 771177671))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 753839498) (.branch 77 (.leaf 736932744) (.leaf 720444766))) (.branch 80 (.branch 79 (.leaf 704363377) (.leaf 688676820)) (.branch 81 (.leaf 673373756) (.leaf 658443240)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 643874711) (.leaf 629657969)) (.branch 85 (.leaf 615783168) (.leaf 602240791))) (.branch 88 (.branch 87 (.leaf 589021649) (.leaf 576116855)) (.branch 89 (.leaf 563517822) (.leaf 551216245)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 539204091) (.branch 92 (.leaf 527473589) (.leaf 516017221))) (.branch 95 (.branch 94 (.leaf 504827707) (.leaf 493898001)) (.branch 96 (.leaf 483221281) (.leaf 472790938)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 462600568) (.leaf 452643968)) (.branch 100 (.leaf 442915126) (.leaf 433408210))) (.branch 103 (.branch 102 (.leaf 424117570) (.leaf 415037723)) (.branch 104 (.leaf 406163352) (.leaf 397489297))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 389010550) (.leaf 380722254)) (.branch 108 (.leaf 372619688) (.leaf 364698272))) (.branch 111 (.branch 110 (.leaf 356953556) (.leaf 349381218)) (.branch 112 (.leaf 341977059) (.leaf 334736999)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 327657072) (.leaf 320733423)) (.branch 116 (.leaf 313962303) (.leaf 307340069))) (.branch 119 (.branch 118 (.leaf 300863175) (.leaf 294528174)) (.branch 120 (.leaf 288331711) (.leaf 282270523)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 475).prefactor = (5473565403297109/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 475).cutoff/(generalMeanRows 475).c)).2 =
    (44842994020221/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 475).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 475).q*(generalMeanRows 475).c/2-2 = (102/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable107.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 475).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 475).criticalRate j.val*(generalMeanRows 475).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 475).c*(generalMeanRows 475).criticalPoint j.val)).2-
      (generalMeanRows 475).J/2-(generalMeanRows 475).error (generalMeanGrid j.val)+
      (generalMeanRows 475).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 475).c)).2-
      (generalMeanRows 475).J/2-(generalMeanRows 475).error 4 := by
  have he : (generalMeanRows 475).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 475) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 475)
    (generalMeanRows_prefactorDomain 475) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0475

/-! Kernel-checked entropy margins for general spectral rectangle 476. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0476
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5043838654) (.branch 2 (.leaf 4872529556) (.leaf 4708980041))) (.branch 5 (.branch 4 (.leaf 4552739181) (.leaf 4403388288)) (.branch 6 (.leaf 4260538098) (.leaf 4123826255)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3992915062) (.leaf 3867489457)) (.branch 10 (.leaf 3747255189) (.leaf 3631937175))) (.branch 13 (.branch 12 (.leaf 3521278014) (.leaf 3415036633)) (.branch 14 (.leaf 3312987062) (.leaf 3214917318))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3120628384) (.branch 17 (.leaf 3029933276) (.leaf 2942656194))) (.branch 20 (.branch 19 (.leaf 2858631740) (.leaf 2777704194)) (.branch 21 (.leaf 2699726863) (.leaf 2624561463)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2552077568) (.leaf 2482152085)) (.branch 25 (.leaf 2414668780) (.leaf 2349517837))) (.branch 28 (.branch 27 (.leaf 2286595443) (.leaf 2225803412)) (.branch 29 (.leaf 2167048832) (.leaf 2110243738)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2055304808) (.branch 32 (.leaf 2002153077) (.leaf 1950713678))) (.branch 35 (.branch 34 (.leaf 1900915594) (.leaf 1852691428)) (.branch 36 (.leaf 1805977192) (.leaf 1760712106)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1716838412) (.leaf 1674301201)) (.branch 40 (.leaf 1633048248) (.leaf 1593029859))) (.branch 43 (.branch 42 (.leaf 1554198733) (.leaf 1516509822)) (.branch 44 (.leaf 1479920210) (.leaf 1444388994))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1409877173) (.branch 47 (.leaf 1376347545) (.leaf 1343764610))) (.branch 50 (.branch 49 (.leaf 1312094479) (.leaf 1281304785)) (.branch 51 (.leaf 1251364606) (.leaf 1222244389)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1193915875) (.leaf 1166352034)) (.branch 55 (.leaf 1139527002) (.leaf 1113416020))) (.branch 58 (.branch 57 (.leaf 1087995379) (.leaf 1063242364)) (.branch 59 (.leaf 1039135209) (.leaf 1015653044))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 992775855) (.branch 62 (.leaf 970484440) (.leaf 948760368))) (.branch 65 (.branch 64 (.leaf 927585945) (.leaf 906944174)) (.branch 66 (.leaf 886818726) (.leaf 867193904)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 848054617) (.leaf 829386349)) (.branch 70 (.leaf 811175131) (.leaf 793407522))) (.branch 73 (.branch 72 (.leaf 776070575) (.leaf 759151823)) (.branch 74 (.leaf 742639253) (.leaf 726521287))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 710786761) (.branch 77 (.leaf 695424908) (.leaf 680425340))) (.branch 80 (.branch 79 (.leaf 665778034) (.leaf 651473309)) (.branch 81 (.leaf 637501821) (.leaf 623854540)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 610522743) (.leaf 597497997)) (.branch 85 (.leaf 584772148) (.leaf 572337311))) (.branch 88 (.branch 87 (.leaf 560185857) (.leaf 548310403)) (.branch 89 (.leaf 536703802) (.leaf 525359136)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 514269702) (.branch 92 (.leaf 503429009) (.leaf 492830764))) (.branch 95 (.branch 94 (.leaf 482468869) (.leaf 472337411)) (.branch 96 (.leaf 462430657) (.leaf 452743045)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 443269178) (.leaf 434003818)) (.branch 100 (.leaf 424941882) (.leaf 416078433))) (.branch 103 (.branch 102 (.leaf 407408677) (.leaf 398927958)) (.branch 104 (.leaf 390631752) (.leaf 382515661))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 374575413) (.leaf 366806852)) (.branch 108 (.leaf 359205939) (.leaf 351768745))) (.branch 111 (.branch 110 (.leaf 344491447) (.leaf 337370328)) (.branch 112 (.leaf 330401768) (.leaf 323582246)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 316908333) (.leaf 310376692)) (.branch 116 (.leaf 303984072) (.leaf 297727306))) (.branch 119 (.branch 118 (.leaf 291603312) (.leaf 285609085)) (.branch 120 (.leaf 279741698) (.leaf 273998298)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 476).prefactor = (4857015098832597/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 476).cutoff/(generalMeanRows 476).c)).2 =
    (201842057615357/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 476).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 476).q*(generalMeanRows 476).c/2-2 = (1607/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable174.value]
  have hcontinuation : (generalMeanRows 476).q*(generalMeanRows 476).cutoff/2-2 = (1378/627:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable170.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 476).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 476).criticalRate j.val*(generalMeanRows 476).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 476).c*(generalMeanRows 476).criticalPoint j.val)).2-
      (generalMeanRows 476).J/2-(generalMeanRows 476).error (generalMeanGrid j.val)+
      (generalMeanRows 476).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 476).c)).2-
      (generalMeanRows 476).J/2-(generalMeanRows 476).error 4 := by
  have he : (generalMeanRows 476).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 476) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 476)
    (generalMeanRows_prefactorDomain 476) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0476

/-! Kernel-checked entropy margins for general spectral rectangle 477. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0477
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6083442036) (.branch 2 (.leaf 5892651545) (.leaf 5710261225))) (.branch 5 (.branch 4 (.leaf 5535788324) (.leaf 5368784371)) (.branch 6 (.leaf 5208832181) (.leaf 5055543184)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4908555037) (.leaf 4767529473)) (.branch 10 (.leaf 4632150373) (.leaf 4502122021))) (.branch 13 (.branch 12 (.leaf 4377167529) (.leaf 4257027405)) (.branch 14 (.leaf 4141458254) (.leaf 4030231597))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3923132790) (.branch 17 (.leaf 3819960041) (.leaf 3720523503))) (.branch 20 (.branch 19 (.leaf 3624644447) (.leaf 3532154504)) (.branch 21 (.leaf 3442894964) (.leaf 3356716130)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3273476727) (.leaf 3193043353)) (.branch 25 (.leaf 3115289966) (.leaf 3040097424))) (.branch 28 (.branch 27 (.leaf 2967353040) (.leaf 2896950187)) (.branch 29 (.leaf 2828787915) (.leaf 2762770610)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2698807665) (.branch 32 (.leaf 2636813180) (.leaf 2576705683))) (.branch 35 (.branch 34 (.leaf 2518407863) (.leaf 2461846330)) (.branch 36 (.leaf 2406951385) (.leaf 2353656806)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2301899647) (.leaf 2251620056)) (.branch 40 (.leaf 2202761095) (.leaf 2155268581))) (.branch 43 (.branch 42 (.leaf 2109090926) (.leaf 2064179000)) (.branch 44 (.leaf 2020485993) (.leaf 1977967284))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1936580331) (.branch 47 (.leaf 1896284551) (.leaf 1857041218))) (.branch 50 (.branch 49 (.leaf 1818813364) (.leaf 1781565685)) (.branch 51 (.leaf 1745264457) (.leaf 1709877446)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1675373839) (.leaf 1641724163)) (.branch 55 (.leaf 1608900224) (.leaf 1576875032))) (.branch 58 (.branch 57 (.leaf 1545622749) (.leaf 1515118627)) (.branch 59 (.leaf 1485338951) (.leaf 1456260993))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1427862956) (.branch 62 (.leaf 1400123936) (.leaf 1373023872))) (.branch 65 (.branch 64 (.leaf 1346543507) (.leaf 1320664352)) (.branch 66 (.leaf 1295368642) (.leaf 1270639311)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1246459949) (.leaf 1222814778)) (.branch 70 (.leaf 1199688619) (.leaf 1177066865))) (.branch 73 (.branch 72 (.leaf 1154935455) (.leaf 1133280847)) (.branch 74 (.leaf 1112089996) (.leaf 1091350332))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1071049736) (.branch 77 (.leaf 1051176521) (.leaf 1031719414))) (.branch 80 (.branch 79 (.leaf 1012667536) (.leaf 994010384)) (.branch 81 (.leaf 975737819) (.leaf 957840042)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 940307590) (.leaf 923131310)) (.branch 85 (.leaf 906302357) (.leaf 889812172))) (.branch 88 (.branch 87 (.leaf 873652475) (.leaf 857815253)) (.branch 89 (.leaf 842292747) (.leaf 827077443)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 812162061) (.branch 92 (.leaf 797539548) (.leaf 783203065))) (.branch 95 (.branch 94 (.leaf 769145983) (.leaf 755361871)) (.branch 96 (.leaf 741844489) (.leaf 728587783)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 715585874) (.leaf 702833056)) (.branch 100 (.leaf 690323784) (.leaf 678052673))) (.branch 103 (.branch 102 (.leaf 666014489) (.leaf 654204143)) (.branch 104 (.leaf 642616690) (.leaf 631247317))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 620091345) (.leaf 609144220)) (.branch 108 (.leaf 598401508) (.leaf 587858896))) (.branch 111 (.branch 110 (.leaf 577512181) (.leaf 567357273)) (.branch 112 (.leaf 557390183) (.leaf 547607029)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 538004025) (.leaf 528577481)) (.branch 116 (.leaf 519323799) (.leaf 510239470))) (.branch 119 (.branch 118 (.leaf 501321073) (.leaf 492565268)) (.branch 120 (.leaf 483968800) (.leaf 475528487)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 477).prefactor = (5180845499968537/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 477).cutoff/(generalMeanRows 477).c)).2 =
    (211598597142313/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 477).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 477).q*(generalMeanRows 477).c/2-2 = (2707/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable126.value]
  have hcontinuation : (generalMeanRows 477).q*(generalMeanRows 477).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable145.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 477).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 477).criticalRate j.val*(generalMeanRows 477).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 477).c*(generalMeanRows 477).criticalPoint j.val)).2-
      (generalMeanRows 477).J/2-(generalMeanRows 477).error (generalMeanGrid j.val)+
      (generalMeanRows 477).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 477).c)).2-
      (generalMeanRows 477).J/2-(generalMeanRows 477).error 4 := by
  have he : (generalMeanRows 477).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 477) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 477)
    (generalMeanRows_prefactorDomain 477) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0477

/-! Kernel-checked entropy margins for general spectral rectangle 478. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0478
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4951036483) (.branch 2 (.leaf 4778141315) (.leaf 4613112247))) (.branch 5 (.branch 4 (.leaf 4455494866) (.leaf 4304867085)) (.branch 6 (.leaf 4160836331) (.leaf 4023037016)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3891128290) (.leaf 3764792011)) (.branch 10 (.leaf 3643730923) (.leaf 3527667007))) (.branch 13 (.branch 12 (.leaf 3416339994) (.leaf 3309506013)) (.branch 14 (.leaf 3206936361) (.leaf 3108416389))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3013744479) (.branch 17 (.leaf 2922731109) (.leaf 2835198007))) (.branch 20 (.branch 19 (.leaf 2750977362) (.leaf 2669911108)) (.branch 21 (.leaf 2591850260) (.leaf 2516654310)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2444190664) (.leaf 2374334121)) (.branch 25 (.leaf 2306966398) (.leaf 2241975684))) (.branch 28 (.branch 27 (.leaf 2179256232) (.leaf 2118707975)) (.branch 29 (.leaf 2060236177) (.leaf 2003751100)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1949167703) (.branch 32 (.leaf 1896405357) (.leaf 1845387577))) (.branch 35 (.branch 34 (.leaf 1796041781) (.leaf 1748299058)) (.branch 36 (.leaf 1702093950) (.leaf 1657364256)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1614050845) (.leaf 1572097474)) (.branch 40 (.leaf 1531450635) (.leaf 1492059391))) (.branch 43 (.branch 42 (.leaf 1453875239) (.leaf 1416851971)) (.branch 44 (.leaf 1380945552) (.leaf 1346113996))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1312317260) (.branch 47 (.leaf 1279517136) (.leaf 1247677153))) (.branch 50 (.branch 49 (.leaf 1216762486) (.leaf 1186739869)) (.branch 51 (.leaf 1157577511) (.leaf 1129245023)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1101713342) (.leaf 1074954663)) (.branch 55 (.leaf 1048942379) (.leaf 1023651014))) (.branch 58 (.branch 57 (.leaf 999056171) (.leaf 975134474)) (.branch 59 (.leaf 951863523) (.leaf 929221838))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 907188820) (.branch 62 (.leaf 885744706) (.leaf 864870528))) (.branch 65 (.branch 64 (.leaf 844548076) (.leaf 824759859)) (.branch 66 (.leaf 805489074) (.leaf 786719574)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 768435834) (.leaf 750622923)) (.branch 70 (.leaf 733266478) (.leaf 716352679))) (.branch 73 (.branch 72 (.leaf 699868219) (.leaf 683800288)) (.branch 74 (.leaf 668136543) (.leaf 652865095))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 637974482) (.branch 77 (.leaf 623453654) (.leaf 609291955))) (.branch 80 (.branch 79 (.leaf 595479103) (.leaf 582005178)) (.branch 81 (.leaf 568860604) (.leaf 556036134)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 543522838) (.leaf 531312087)) (.branch 85 (.leaf 519395543) (.leaf 507765148))) (.branch 88 (.branch 87 (.leaf 496413108) (.leaf 485331887)) (.branch 89 (.leaf 474514193) (.leaf 463952971)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 453641391) (.branch 92 (.leaf 443572843) (.leaf 433740924))) (.branch 95 (.branch 94 (.leaf 424139433) (.leaf 414762360)) (.branch 96 (.leaf 405603883) (.leaf 396658358)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 387920314) (.leaf 379384444)) (.branch 100 (.leaf 371045601) (.leaf 362898791))) (.branch 103 (.branch 102 (.leaf 354939169) (.leaf 347162033)) (.branch 104 (.leaf 339562816) (.leaf 332137087))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 324880540) (.leaf 317788994)) (.branch 108 (.leaf 310858386) (.leaf 304084769))) (.branch 111 (.branch 110 (.leaf 297464306) (.leaf 290993269)) (.branch 112 (.leaf 284668032) (.leaf 278485069)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 272440952) (.leaf 266532347)) (.branch 116 (.leaf 260756008) (.leaf 255108779))) (.branch 119 (.branch 118 (.leaf 249587587) (.leaf 244189444)) (.branch 120 (.leaf 238911438) (.leaf 233750736)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 478).prefactor = (4898220459239667/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 478).cutoff/(generalMeanRows 478).c)).2 =
    (382983032440467/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 478).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 478).q*(generalMeanRows 478).c/2-2 = (1691/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable175.value]
  have hcontinuation : (generalMeanRows 478).q*(generalMeanRows 478).cutoff/2-2 = (1028/473:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable176.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 478).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 478).criticalRate j.val*(generalMeanRows 478).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 478).c*(generalMeanRows 478).criticalPoint j.val)).2-
      (generalMeanRows 478).J/2-(generalMeanRows 478).error (generalMeanGrid j.val)+
      (generalMeanRows 478).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 478).c)).2-
      (generalMeanRows 478).J/2-(generalMeanRows 478).error 4 := by
  have he : (generalMeanRows 478).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 478) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 478)
    (generalMeanRows_prefactorDomain 478) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0478

/-! Kernel-checked entropy margins for general spectral rectangle 479. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0479
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5076563865) (.branch 2 (.leaf 4904143287) (.leaf 4739532637))) (.branch 5 (.branch 4 (.leaf 4582278062) (.leaf 4431958157)) (.branch 6 (.leaf 4288181132) (.leaf 4150582282)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4018821717) (.leaf 3892582331)) (.branch 10 (.leaf 3771567964) (.leaf 3655501749))) (.branch 13 (.branch 12 (.leaf 3544124614) (.leaf 3437193923)) (.branch 14 (.leaf 3334482239) (.leaf 3235776203))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3140875507) (.branch 17 (.leaf 3049591955) (.leaf 2961748606))) (.branch 20 (.branch 19 (.leaf 2877178988) (.leaf 2795726372)) (.branch 21 (.leaf 2717243111) (.leaf 2641590027)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2568635844) (.leaf 2498256674)) (.branch 25 (.leaf 2430335528) (.leaf 2364761875))) (.branch 28 (.branch 27 (.leaf 2301431230) (.leaf 2240244771)) (.branch 29 (.leaf 2181108982) (.leaf 2123935328)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2068639946) (.branch 32 (.leaf 2015143358) (.leaf 1963370213))) (.branch 35 (.branch 34 (.leaf 1913249030) (.leaf 1864711978)) (.branch 36 (.leaf 1817694653) (.leaf 1772135880)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1727977527) (.leaf 1685164328)) (.branch 40 (.leaf 1643643719) (.leaf 1603365685))) (.branch 43 (.branch 42 (.leaf 1564282616) (.leaf 1526349174)) (.branch 44 (.leaf 1489522163) (.leaf 1453760415))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1419024676) (.branch 47 (.leaf 1385277503) (.leaf 1352483165))) (.branch 50 (.branch 49 (.leaf 1320607552) (.leaf 1289618090)) (.branch 51 (.leaf 1259483655) (.leaf 1230174501)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1201662187) (.leaf 1173919508)) (.branch 55 (.leaf 1146920431) (.leaf 1120640037))) (.branch 58 (.branch 57 (.leaf 1095054462) (.leaf 1070140846)) (.branch 59 (.leaf 1045877280) (.leaf 1022242759))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 999217139) (.branch 62 (.leaf 976781094) (.leaf 954916073))) (.branch 65 (.branch 64 (.leaf 933604267) (.leaf 912828569)) (.branch 66 (.leaf 892572544) (.leaf 872820393)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 853556928) (.leaf 834767536)) (.branch 70 (.leaf 816438162) (.leaf 798555273))) (.branch 73 (.branch 72 (.leaf 781105842) (.leaf 764077318)) (.branch 74 (.leaf 747457612) (.leaf 731235070))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 715398456) (.branch 77 (.leaf 699936933) (.leaf 684840046))) (.branch 80 (.branch 79 (.leaf 670097705) (.leaf 655700169)) (.branch 81 (.leaf 641638032) (.leaf 627902206)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 614483910) (.leaf 601374657)) (.branch 85 (.leaf 588566241) (.leaf 576050725))) (.branch 88 (.branch 87 (.leaf 563820430) (.leaf 551867926)) (.branch 89 (.leaf 540186020) (.leaf 528767748)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 517606364) (.branch 92 (.leaf 506695335) (.leaf 496028327))) (.branch 95 (.branch 94 (.leaf 485599202) (.leaf 475402010)) (.branch 96 (.leaf 465430980) (.leaf 455680513)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 446145177) (.leaf 436819702)) (.branch 100 (.leaf 427698971) (.leaf 418778014))) (.branch 103 (.branch 102 (.leaf 410052008) (.leaf 401516265)) (.branch 104 (.leaf 393166231) (.leaf 384997482))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 377005716) (.leaf 369186752)) (.branch 108 (.leaf 361536523) (.leaf 354051075))) (.branch 111 (.branch 110 (.leaf 346726561) (.leaf 339559239)) (.branch 112 (.leaf 332545466) (.leaf 325681698)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 318964484) (.leaf 312390464)) (.branch 116 (.leaf 305956368) (.leaf 299659007))) (.branch 119 (.branch 118 (.leaf 293495280) (.leaf 287462162)) (.branch 120 (.leaf 281556706) (.leaf 275776042)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 479).prefactor = (488852816934463/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 479).cutoff/(generalMeanRows 479).c)).2 =
    (201842057615357/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 479).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 479).q*(generalMeanRows 479).c/2-2 = (1607/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable174.value]
  have hcontinuation : (generalMeanRows 479).q*(generalMeanRows 479).cutoff/2-2 = (1378/627:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable170.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 479).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 479).criticalRate j.val*(generalMeanRows 479).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 479).c*(generalMeanRows 479).criticalPoint j.val)).2-
      (generalMeanRows 479).J/2-(generalMeanRows 479).error (generalMeanGrid j.val)+
      (generalMeanRows 479).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 479).c)).2-
      (generalMeanRows 479).J/2-(generalMeanRows 479).error 4 := by
  have he : (generalMeanRows 479).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 479) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 479)
    (generalMeanRows_prefactorDomain 479) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0479

/-! Kernel-checked entropy margins for general spectral rectangle 480. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0480
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5109501402) (.branch 2 (.leaf 4935962132) (.leaf 4770283463))) (.branch 5 (.branch 4 (.leaf 4612008596) (.leaf 4460713392)) (.branch 6 (.leaf 4316003520) (.leaf 4177511906)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4044896459) (.leaf 3917838012)) (.branch 10 (.leaf 3796038484) (.leaf 3679219214))) (.branch 13 (.branch 12 (.leaf 3567119447) (.leaf 3459494972)) (.branch 14 (.leaf 3356116879) (.leaf 3256770423))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3161253996) (.branch 17 (.leaf 3069378182) (.leaf 2980964892))) (.branch 20 (.branch 19 (.leaf 2895846573) (.leaf 2813865480)) (.branch 21 (.leaf 2734873008) (.leaf 2658729074)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2585301554) (.leaf 2514465752)) (.branch 25 (.leaf 2446103923) (.leaf 2380104818))) (.branch 28 (.branch 27 (.leaf 2316363275) (.leaf 2254779828)) (.branch 29 (.leaf 2195260357) (.leaf 2137715752)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2082061604) (.branch 32 (.leaf 2028217922) (.leaf 1976108864))) (.branch 35 (.branch 34 (.leaf 1925662488) (.leaf 1876810520)) (.branch 36 (.leaf 1829488139) (.leaf 1783633774)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1739188915) (.leaf 1696097937)) (.branch 40 (.leaf 1654307936) (.leaf 1613768571))) (.branch 43 (.branch 42 (.leaf 1574431926) (.leaf 1536252365)) (.branch 44 (.leaf 1499186415) (.leaf 1463192639))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1428231529) (.branch 47 (.leaf 1394265399) (.leaf 1361258286))) (.branch 50 (.branch 49 (.leaf 1329175860) (.leaf 1297985333)) (.branch 51 (.leaf 1267655381) (.leaf 1238156065)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1209458759) (.leaf 1181536080)) (.branch 55 (.leaf 1154361829) (.leaf 1127910924))) (.branch 58 (.branch 57 (.leaf 1102159346) (.leaf 1077084087)) (.branch 59 (.leaf 1052663094) (.leaf 1028875229))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1005700216) (.branch 62 (.leaf 983118602) (.leaf 961111717))) (.branch 65 (.branch 64 (.leaf 939661637) (.leaf 918751143)) (.branch 66 (.leaf 898363693) (.leaf 878483388)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 859094938) (.leaf 840183638)) (.branch 70 (.leaf 821735340) (.leaf 803736424))) (.branch 73 (.branch 72 (.leaf 786173778) (.leaf 769034771)) (.branch 74 (.leaf 752307234) (.leaf 735979437))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 720040072) (.branch 77 (.leaf 704478233) (.leaf 689283395))) (.branch 80 (.branch 79 (.leaf 674445403) (.leaf 659954454)) (.branch 81 (.leaf 645801079) (.leaf 631976133)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 618470777) (.leaf 605276470)) (.branch 85 (.leaf 592384950) (.leaf 579788232))) (.branch 88 (.branch 87 (.leaf 567478585) (.leaf 555448531)) (.branch 89 (.leaf 543690831) (.leaf 532198475)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 520964675) (.branch 92 (.leaf 509982853) (.leaf 499246636))) (.branch 95 (.branch 94 (.leaf 488749845) (.leaf 478486492)) (.branch 96 (.leaf 468450768) (.leaf 458637039)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 449039837) (.leaf 439653857)) (.branch 100 (.leaf 430473948) (.leaf 421495111))) (.branch 103 (.branch 102 (.leaf 412712489) (.leaf 404121365)) (.branch 104 (.leaf 395717155) (.leaf 387495406))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 379451788) (.leaf 371582093)) (.branch 108 (.leaf 363882228) (.leaf 356348214))) (.branch 111 (.branch 110 (.leaf 348976177) (.leaf 341762352)) (.branch 112 (.leaf 334703073) (.leaf 327794772)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 321033975) (.leaf 314417302)) (.branch 116 (.leaf 307941460) (.leaf 301603242))) (.branch 119 (.branch 118 (.leaf 295399523) (.leaf 289327261)) (.branch 120 (.leaf 283383490) (.leaf 277565320)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 480).prefactor = (4920245701566761/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 480).cutoff/(generalMeanRows 480).c)).2 =
    (201842057615357/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 480).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 480).q*(generalMeanRows 480).c/2-2 = (1607/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable174.value]
  have hcontinuation : (generalMeanRows 480).q*(generalMeanRows 480).cutoff/2-2 = (1378/627:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable170.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 480).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 480).criticalRate j.val*(generalMeanRows 480).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 480).c*(generalMeanRows 480).criticalPoint j.val)).2-
      (generalMeanRows 480).J/2-(generalMeanRows 480).error (generalMeanGrid j.val)+
      (generalMeanRows 480).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 480).c)).2-
      (generalMeanRows 480).J/2-(generalMeanRows 480).error 4 := by
  have he : (generalMeanRows 480).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 480) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 480)
    (generalMeanRows_prefactorDomain 480) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0480

/-! Kernel-checked entropy margins for general spectral rectangle 481. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0481
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4983673066) (.branch 2 (.leaf 4809638196) (.leaf 4643521278))) (.branch 5 (.branch 4 (.leaf 4484864903) (.leaf 4333244205)) (.branch 6 (.leaf 4188264018) (.leaf 4049556348)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3916778097) (.leaf 3789609027)) (.branch 10 (.leaf 3667749919) (.leaf 3550920925))) (.branch 13 (.branch 12 (.leaf 3438860059) (.leaf 3331321842)) (.branch 14 (.leaf 3228076065) (.leaf 3128906663))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3033610687) (.branch 17 (.leaf 2941997369) (.leaf 2853887261))) (.branch 20 (.branch 19 (.leaf 2769111444) (.leaf 2687510811)) (.branch 21 (.leaf 2608935397) (.leaf 2533243765)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2460302448) (.leaf 2389985420)) (.branch 25 (.leaf 2322173618) (.leaf 2256754494))) (.branch 28 (.branch 27 (.leaf 2193621603) (.leaf 2132674220)) (.branch 29 (.leaf 2073816983) (.leaf 2016959564)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1962016361) (.branch 32 (.leaf 1908906212) (.leaf 1857552130))) (.branch 35 (.branch 34 (.leaf 1807881053) (.leaf 1759823616)) (.branch 36 (.leaf 1713313930) (.leaf 1668289384)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1624690456) (.leaf 1582460535)) (.branch 40 (.leaf 1541545757) (.leaf 1501894851))) (.branch 43 (.branch 42 (.leaf 1463458994) (.leaf 1426191674)) (.branch 44 (.leaf 1390048564) (.leaf 1354987403))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1320967883) (.branch 47 (.leaf 1287951545) (.leaf 1255901677))) (.branch 50 (.branch 49 (.leaf 1224783225) (.leaf 1194562702)) (.branch 51 (.leaf 1165208110) (.leaf 1136688858)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1108975692) (.leaf 1082040624)) (.branch 55 (.leaf 1055856870) (.leaf 1030398787))) (.branch 58 (.branch 57 (.leaf 1005641818) (.leaf 981562433)) (.branch 59 (.leaf 958138082) (.leaf 935347146))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 913168890) (.branch 62 (.leaf 891583419) (.leaf 870571641))) (.branch 65 (.branch 64 (.leaf 850115226) (.leaf 830196568)) (.branch 66 (.leaf 810798753) (.leaf 791905527)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 773501262) (.leaf 755570931)) (.branch 70 (.leaf 738100075) (.leaf 721074782))) (.branch 73 (.branch 72 (.leaf 704481659) (.leaf 688307810)) (.branch 74 (.leaf 672540812) (.leaf 657168696))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 642179926) (.branch 77 (.leaf 627563379) (.leaf 613308327))) (.branch 80 (.branch 79 (.leaf 599404423) (.leaf 585841680)) (.branch 81 (.leaf 572610459) (.leaf 559701452)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 547105669) (.leaf 534814426)) (.branch 85 (.leaf 522819331) (.leaf 511112269))) (.branch 88 (.branch 87 (.leaf 499685398) (.leaf 488531131)) (.branch 89 (.leaf 477642128) (.leaf 467011288)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 456631736) (.branch 92 (.leaf 446496817) (.leaf 436600088))) (.branch 95 (.branch 94 (.leaf 426935304) (.leaf 417496419)) (.branch 96 (.leaf 408277571) (.leaf 399273078)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 390477434) (.leaf 381885297)) (.branch 100 (.leaf 373491485) (.leaf 365290972))) (.branch 103 (.branch 102 (.leaf 357278882) (.leaf 349450479)) (.branch 104 (.leaf 341801170) (.leaf 334326491))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 327022110) (.leaf 319883817)) (.branch 108 (.leaf 312907523) (.leaf 306089256))) (.branch 111 (.branch 110 (.leaf 299425152) (.leaf 292911459)) (.branch 112 (.leaf 286544526) (.leaf 280320806)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 274236847) (.leaf 268289293)) (.branch 116 (.leaf 262474877) (.leaf 256790422))) (.branch 119 (.branch 118 (.leaf 251232836) (.leaf 245799109)) (.branch 120 (.leaf 240486311) (.leaf 235291590)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 481).prefactor = (4930508886108411/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 481).cutoff/(generalMeanRows 481).c)).2 =
    (382983032440467/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 481).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 481).q*(generalMeanRows 481).c/2-2 = (1691/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable175.value]
  have hcontinuation : (generalMeanRows 481).q*(generalMeanRows 481).cutoff/2-2 = (1028/473:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable176.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 481).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 481).criticalRate j.val*(generalMeanRows 481).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 481).c*(generalMeanRows 481).criticalPoint j.val)).2-
      (generalMeanRows 481).J/2-(generalMeanRows 481).error (generalMeanGrid j.val)+
      (generalMeanRows 481).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 481).c)).2-
      (generalMeanRows 481).J/2-(generalMeanRows 481).error 4 := by
  have he : (generalMeanRows 481).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 481) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 481)
    (generalMeanRows_prefactorDomain 481) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0481

/-! Kernel-checked entropy margins for general spectral rectangle 482. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0482
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4933562523) (.branch 2 (.leaf 4758928463) (.leaf 4592272450))) (.branch 5 (.branch 4 (.leaf 4433133814) (.leaf 4281084629)) (.branch 6 (.leaf 4135726859) (.leaf 3996689803)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3863627818) (.leaf 3736218261)) (.branch 10 (.leaf 3614159647) (.leaf 3497169981))) (.branch 13 (.branch 12 (.leaf 3384985251) (.leaf 3277358054)) (.branch 14 (.leaf 3174056361) (.leaf 3074862379))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2979571519) (.branch 17 (.leaf 2887991455) (.leaf 2799941256))) (.branch 20 (.branch 19 (.leaf 2715250596) (.leaf 2633759026)) (.branch 21 (.leaf 2555315304) (.leaf 2479776777)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2407008817) (.leaf 2336884292)) (.branch 25 (.leaf 2269283084) (.leaf 2204091639))) (.branch 28 (.branch 27 (.leaf 2141202549) (.leaf 2080514172)) (.branch 29 (.leaf 2021930269) (.leaf 1965359672)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1910715980) (.branch 32 (.leaf 1857917265) (.leaf 1806885807))) (.branch 35 (.branch 34 (.leaf 1757547845) (.leaf 1709833344)) (.branch 36 (.leaf 1663675774) (.leaf 1619011912)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1575781649) (.leaf 1533927813)) (.branch 40 (.leaf 1493396004) (.leaf 1454134437))) (.branch 43 (.branch 42 (.leaf 1416093798) (.leaf 1379227103)) (.branch 44 (.leaf 1343489577) (.leaf 1308838528))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1275233236) (.branch 47 (.leaf 1242634847) (.leaf 1211006273))) (.branch 50 (.branch 49 (.leaf 1180312098) (.leaf 1150518493)) (.branch 51 (.leaf 1121593127) (.leaf 1093505095)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1066224842) (.leaf 1039724092)) (.branch 55 (.leaf 1013975786) (.leaf 988954018))) (.branch 58 (.branch 57 (.leaf 964633980) (.leaf 940991902)) (.branch 59 (.leaf 918005006) (.leaf 895651454))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 873910304) (.branch 62 (.leaf 852761462) (.leaf 832185648))) (.branch 65 (.branch 64 (.leaf 812164351) (.leaf 792679793)) (.branch 66 (.leaf 773714900) (.leaf 755253260)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 737279099) (.leaf 719777249)) (.branch 70 (.leaf 702733120) (.leaf 686132673))) (.branch 73 (.branch 72 (.leaf 669962395) (.leaf 654209278)) (.branch 74 (.leaf 638860793) (.leaf 623904868))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 609329871) (.branch 77 (.leaf 595124591) (.leaf 581278216))) (.branch 80 (.branch 79 (.leaf 567780316) (.leaf 554620831)) (.branch 81 (.leaf 541790052) (.leaf 529278604)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 517077436) (.leaf 505177808)) (.branch 85 (.leaf 493571271) (.leaf 482249664))) (.branch 88 (.branch 87 (.leaf 471205097) (.leaf 460429941)) (.branch 89 (.leaf 449916817) (.leaf 439658588)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 429648346) (.branch 92 (.leaf 419879407) (.leaf 410345300))) (.branch 95 (.branch 94 (.leaf 401039758) (.leaf 391956710)) (.branch 96 (.leaf 383090278) (.leaf 374434764)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 365984645) (.leaf 357734568)) (.branch 100 (.leaf 349679343) (.leaf 341813934))) (.branch 103 (.branch 102 (.leaf 334133460) (.leaf 326633183)) (.branch 104 (.leaf 319308504) (.leaf 312154962))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 305168225) (.leaf 298344085)) (.branch 108 (.leaf 291678460) (.leaf 285167380))) (.branch 111 (.branch 110 (.leaf 278806991) (.leaf 272593548)) (.branch 112 (.leaf 266523412) (.leaf 260593044)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 254799005) (.leaf 249137952)) (.branch 116 (.leaf 243606633) (.leaf 238201886))) (.branch 119 (.branch 118 (.leaf 232920633) (.leaf 227759883)) (.branch 120 (.leaf 222716723) (.leaf 217788320)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 482).prefactor = (4963010154052473/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 482).cutoff/(generalMeanRows 482).c)).2 =
    (46953757266901/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 482).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 482).q*(generalMeanRows 482).c/2-2 = (1733/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable177.value]
  have hcontinuation : (generalMeanRows 482).q*(generalMeanRows 482).cutoff/2-2 = (1028/473:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable176.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 482).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 482).criticalRate j.val*(generalMeanRows 482).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 482).c*(generalMeanRows 482).criticalPoint j.val)).2-
      (generalMeanRows 482).J/2-(generalMeanRows 482).error (generalMeanGrid j.val)+
      (generalMeanRows 482).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 482).c)).2-
      (generalMeanRows 482).J/2-(generalMeanRows 482).error 4 := by
  have he : (generalMeanRows 482).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 482) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 482)
    (generalMeanRows_prefactorDomain 482) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0482

/-! Kernel-checked entropy margins for general spectral rectangle 483. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0483
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5152961705) (.branch 2 (.leaf 4980474541) (.leaf 4815797729))) (.branch 5 (.branch 4 (.leaf 4658474859) (.leaf 4508082288)) (.branch 6 (.leaf 4364226272) (.leaf 4226540413)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4094683364) (.leaf 3968336772)) (.branch 10 (.leaf 3847203426) (.leaf 3731005581))) (.branch 13 (.branch 12 (.leaf 3619483443) (.leaf 3512393797)) (.branch 14 (.leaf 3409508753) (.leaf 3310614617))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3215510846) (.branch 17 (.leaf 3124009103) (.leaf 3035932387))) (.branch 20 (.branch 19 (.leaf 2951114241) (.leaf 2869398017)) (.branch 21 (.leaf 2790636204) (.leaf 2714689813)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2641427805) (.leaf 2570726563)) (.branch 25 (.leaf 2502469406) (.leaf 2436546141))) (.branch 28 (.branch 27 (.leaf 2372852646) (.leaf 2311290481)) (.branch 29 (.leaf 2251766533) (.leaf 2194192685)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2138485499) (.branch 32 (.leaf 2084565938) (.leaf 2032359094))) (.branch 35 (.branch 34 (.leaf 1981793936) (.leaf 1932803085)) (.branch 36 (.leaf 1885322589) (.leaf 1839291728)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1794652820) (.leaf 1751351047)) (.branch 40 (.leaf 1709334289) (.leaf 1668552971))) (.branch 43 (.branch 42 (.leaf 1628959916) (.leaf 1590510211)) (.branch 44 (.leaf 1553161081) (.leaf 1516871768))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1481603422) (.branch 47 (.leaf 1447318994) (.leaf 1413983139))) (.branch 50 (.branch 49 (.leaf 1381562124) (.leaf 1350023738)) (.branch 51 (.leaf 1319337218) (.leaf 1289473162)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1260403467) (.leaf 1232101255)) (.branch 55 (.leaf 1204540810) (.leaf 1177697521))) (.branch 58 (.branch 57 (.leaf 1151547820) (.leaf 1126069134)) (.branch 59 (.leaf 1101239831) (.leaf 1077039175))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1053447280) (.branch 62 (.leaf 1030445067) (.leaf 1008014226))) (.branch 65 (.branch 64 (.leaf 986137177) (.leaf 964797035)) (.branch 66 (.leaf 943977576) (.leaf 923663206)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 903838930) (.leaf 884490325)) (.branch 70 (.leaf 865603511) (.leaf 847165128))) (.branch 73 (.branch 72 (.leaf 829162311) (.leaf 811582667)) (.branch 74 (.leaf 794414252) (.leaf 777645555))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 761265473) (.branch 77 (.leaf 745263297) (.leaf 729628694))) (.branch 80 (.branch 79 (.leaf 714351688) (.leaf 699422646)) (.branch 81 (.leaf 684832264) (.leaf 670571552)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 656631819) (.leaf 643004665)) (.branch 85 (.leaf 629681964) (.leaf 616655854))) (.branch 88 (.branch 87 (.leaf 603918727) (.leaf 591463219)) (.branch 89 (.leaf 579282199) (.leaf 567368758)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 555716204) (.branch 92 (.leaf 544318052) (.leaf 533168013))) (.branch 95 (.branch 94 (.leaf 522259991) (.leaf 511588071)) (.branch 96 (.leaf 501146517) (.leaf 490929760)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 480932397) (.leaf 471149178)) (.branch 100 (.leaf 461575010) (.leaf 452204940))) (.branch 103 (.branch 102 (.leaf 443034160) (.leaf 434057996)) (.branch 104 (.leaf 425271903) (.leaf 416671465))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 408252386) (.leaf 400010486)) (.branch 108 (.leaf 391941702) (.leaf 384042077))) (.branch 111 (.branch 110 (.leaf 376307761) (.leaf 368735008)) (.branch 112 (.leaf 361320167) (.leaf 354059687)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 346950106) (.leaf 339988054)) (.branch 116 (.leaf 333170245) (.leaf 326493480))) (.branch 119 (.branch 118 (.leaf 319954638) (.leaf 313550679)) (.branch 120 (.leaf 307278638) (.leaf 301135625)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 483).prefactor = (4910097906528989/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 483).cutoff/(generalMeanRows 483).c)).2 =
    (26066754193571/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 483).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 483).q*(generalMeanRows 483).c/2-2 = (313/400:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable173.value]
  have hcontinuation : (generalMeanRows 483).q*(generalMeanRows 483).cutoff/2-2 = (2078/935:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable172.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 483).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 483).criticalRate j.val*(generalMeanRows 483).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 483).c*(generalMeanRows 483).criticalPoint j.val)).2-
      (generalMeanRows 483).J/2-(generalMeanRows 483).error (generalMeanGrid j.val)+
      (generalMeanRows 483).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 483).c)).2-
      (generalMeanRows 483).J/2-(generalMeanRows 483).error 4 := by
  have he : (generalMeanRows 483).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 483) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 483)
    (generalMeanRows_prefactorDomain 483) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0483

/-! Kernel-checked entropy margins for general spectral rectangle 484. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0484
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5252239776) (.branch 2 (.leaf 5081452271) (.leaf 4918316774))) (.branch 5 (.branch 4 (.leaf 4762386620) (.leaf 4613247232)) (.branch 6 (.leaf 4470513314) (.leaf 4333826346)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4202852339) (.leaf 4077279820)) (.branch 10 (.leaf 3956818011) (.leaf 3841195196))) (.branch 13 (.branch 12 (.leaf 3730157231) (.leaf 3623466200)) (.branch 14 (.leaf 3520899196) (.leaf 3422247198))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3327314064) (.branch 17 (.leaf 3235915595) (.leaf 3147878691))) (.branch 20 (.branch 19 (.leaf 3063040567) (.leaf 2981248036)) (.branch 21 (.leaf 2902356859) (.leaf 2826231129)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2752742721) (.leaf 2681770769)) (.branch 25 (.leaf 2613201198) (.leaf 2546926275))) (.branch 28 (.branch 27 (.leaf 2482844209) (.leaf 2420858765)) (.branch 29 (.leaf 2360878920) (.leaf 2302818536)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2246596053) (.branch 32 (.leaf 2192134213) (.leaf 2139359794))) (.branch 35 (.branch 34 (.leaf 2088203370) (.leaf 2038599081)) (.branch 36 (.leaf 1990484420) (.leaf 1943800037)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1898489553) (.leaf 1854499389)) (.branch 40 (.leaf 1811778602) (.leaf 1770278735))) (.branch 43 (.branch 42 (.leaf 1729953676) (.leaf 1690759524)) (.branch 44 (.leaf 1652654468) (.leaf 1615598665))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1579554137) (.branch 47 (.leaf 1544484665) (.leaf 1510355694))) (.branch 50 (.branch 49 (.leaf 1477134243) (.leaf 1444788819)) (.branch 51 (.leaf 1413289338) (.leaf 1382607050)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1352714469) (.leaf 1323585304)) (.branch 55 (.leaf 1295194403) (.leaf 1267517686))) (.branch 58 (.branch 57 (.leaf 1240532096) (.leaf 1214215542)) (.branch 59 (.leaf 1188546855) (.leaf 1163505737))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1139072719) (.branch 62 (.leaf 1115229120) (.leaf 1091957009))) (.branch 65 (.branch 64 (.leaf 1069239165) (.leaf 1047059047)) (.branch 66 (.leaf 1025400756) (.leaf 1004249007)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 983589101) (.leaf 963406893)) (.branch 70 (.leaf 943688771) (.leaf 924421625))) (.branch 73 (.branch 72 (.leaf 905592831) (.leaf 887190222)) (.branch 74 (.leaf 869202071) (.leaf 851617070))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 834424310) (.branch 77 (.leaf 817613266) (.leaf 801173776))) (.branch 80 (.branch 79 (.leaf 785096029) (.leaf 769370546)) (.branch 81 (.leaf 753988170) (.leaf 738940047)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 724217617) (.leaf 709812600)) (.branch 85 (.leaf 695716985) (.leaf 681923019))) (.branch 88 (.branch 87 (.leaf 668423192) (.leaf 655210236)) (.branch 89 (.leaf 642277106) (.leaf 629616977)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 617223232) (.branch 92 (.leaf 605089455) (.leaf 593209425))) (.branch 95 (.branch 94 (.leaf 581577104) (.leaf 570186634)) (.branch 96 (.leaf 559032328) (.leaf 548108664)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 537410280) (.leaf 526931966)) (.branch 100 (.leaf 516668660) (.leaf 506615441))) (.branch 103 (.branch 102 (.leaf 496767527) (.leaf 487120265)) (.branch 104 (.leaf 477669131) (.leaf 468409725))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 459337764) (.leaf 450449079)) (.branch 108 (.leaf 441739613) (.leaf 433205415))) (.branch 111 (.branch 110 (.leaf 424842637) (.leaf 416647531)) (.branch 112 (.leaf 408616446) (.leaf 400745824)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 393032196) (.leaf 385472183)) (.branch 116 (.leaf 378062488) (.leaf 370799898))) (.branch 119 (.branch 118 (.leaf 363681278) (.leaf 356703571)) (.branch 120 (.leaf 349863793) (.leaf 343159034)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 484).prefactor = (4841604031889871/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 484).cutoff/(generalMeanRows 484).c)).2 =
    (85672309111729/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 484).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 484).q*(generalMeanRows 484).c/2-2 = (1199/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable178.value]
  have hcontinuation : (generalMeanRows 484).q*(generalMeanRows 484).cutoff/2-2 = (4104/1849:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable179.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 484).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 484).criticalRate j.val*(generalMeanRows 484).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 484).c*(generalMeanRows 484).criticalPoint j.val)).2-
      (generalMeanRows 484).J/2-(generalMeanRows 484).error (generalMeanGrid j.val)+
      (generalMeanRows 484).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 484).c)).2-
      (generalMeanRows 484).J/2-(generalMeanRows 484).error 4 := by
  have he : (generalMeanRows 484).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 484) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 484)
    (generalMeanRows_prefactorDomain 484) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0484

/-! Kernel-checked entropy margins for general spectral rectangle 485. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0485
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5196042646) (.branch 2 (.leaf 5024538831) (.leaf 4860746412))) (.branch 5 (.branch 4 (.leaf 4704215747) (.leaf 4554529464)) (.branch 6 (.leaf 4411299635) (.leaf 4274165266)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4142790029) (.leaf 4016860245)) (.branch 10 (.leaf 3896083049) (.leaf 3780184748))) (.branch 13 (.branch 12 (.leaf 3668909324) (.leaf 3562017086)) (.branch 14 (.leaf 3459283436) (.leaf 3360497750))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3265462356) (.branch 17 (.leaf 3173991604) (.leaf 3085911004))) (.branch 20 (.branch 19 (.leaf 3001056449) (.leaf 2919273493)) (.branch 21 (.leaf 2840416689) (.leaf 2764348980)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2690941137) (.leaf 2620071242)) (.branch 25 (.leaf 2551624210) (.leaf 2485491344))) (.branch 28 (.branch 27 (.leaf 2421569924) (.leaf 2359762831)) (.branch 29 (.leaf 2299978190) (.leaf 2242129045)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2186133055) (.branch 32 (.leaf 2131912209) (.leaf 2079392565))) (.branch 35 (.branch 34 (.leaf 2028504002) (.leaf 1979179992)) (.branch 36 (.leaf 1931357391) (.leaf 1884976233)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1839979547) (.leaf 1796313186)) (.branch 40 (.leaf 1753925658) (.leaf 1712767983))) (.branch 43 (.branch 42 (.leaf 1672793541) (.leaf 1633957944)) (.branch 44 (.leaf 1596218913) (.leaf 1559536156))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1523871259) (.branch 47 (.leaf 1489187588) (.leaf 1455450185))) (.branch 50 (.branch 49 (.leaf 1422625682) (.leaf 1390682214)) (.branch 51 (.leaf 1359589340) (.leaf 1329317965)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1299840271) (.leaf 1271129650)) (.branch 55 (.leaf 1243160641) (.leaf 1215908869))) (.branch 58 (.branch 57 (.leaf 1189350993) (.leaf 1163464649)) (.branch 59 (.leaf 1138228404) (.leaf 1113621707))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1089624847) (.branch 62 (.leaf 1066218909) (.leaf 1043385737))) (.branch 65 (.branch 64 (.leaf 1021107894) (.leaf 999368630)) (.branch 66 (.leaf 978151848) (.leaf 957442071)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 937224416) (.leaf 917484561)) (.branch 70 (.leaf 898208725) (.leaf 879383635))) (.branch 73 (.branch 72 (.leaf 860996510) (.leaf 843035035)) (.branch 74 (.leaf 825487339) (.leaf 808341975))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 791587905) (.branch 77 (.leaf 775214475) (.leaf 759211404))) (.branch 80 (.branch 79 (.leaf 743568765) (.leaf 728276970)) (.branch 81 (.leaf 713326754) (.leaf 698709165)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 684415545) (.leaf 670437523)) (.branch 85 (.leaf 656767000) (.leaf 643396140))) (.branch 88 (.branch 87 (.leaf 630317355) (.leaf 617523299)) (.branch 89 (.leaf 605006857) (.leaf 592761136)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 580779453) (.branch 92 (.leaf 569055334) (.leaf 557582496))) (.branch 95 (.branch 94 (.leaf 546354849) (.leaf 535366483)) (.branch 96 (.leaf 524611662) (.leaf 514084818)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 503780545) (.leaf 493693594)) (.branch 100 (.leaf 483818865) (.leaf 474151401))) (.branch 103 (.branch 102 (.leaf 464686386) (.leaf 455419139)) (.branch 104 (.leaf 446345107) (.leaf 437459861))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 428759097) (.leaf 420238622)) (.branch 108 (.leaf 411894360) (.leaf 403722340))) (.branch 111 (.branch 110 (.leaf 395718700) (.leaf 387879675)) (.branch 112 (.leaf 380201602) (.leaf 372680910)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 365314123) (.leaf 358097850)) (.branch 116 (.leaf 351028790) (.leaf 344103724))) (.branch 119 (.branch 118 (.leaf 337319511) (.leaf 330673092)) (.branch 120 (.leaf 324161482) (.leaf 317781771)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 485).prefactor = (2436221492488123/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 485).cutoff/(generalMeanRows 485).c)).2 =
    (210421356572309/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 485).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 485).q*(generalMeanRows 485).c/2-2 = (6161/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable180.value]
  have hcontinuation : (generalMeanRows 485).q*(generalMeanRows 485).cutoff/2-2 = (4104/1849:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable179.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 485).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 485).criticalRate j.val*(generalMeanRows 485).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 485).c*(generalMeanRows 485).criticalPoint j.val)).2-
      (generalMeanRows 485).J/2-(generalMeanRows 485).error (generalMeanGrid j.val)+
      (generalMeanRows 485).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 485).c)).2-
      (generalMeanRows 485).J/2-(generalMeanRows 485).error 4 := by
  have he : (generalMeanRows 485).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 485) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 485)
    (generalMeanRows_prefactorDomain 485) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0485

/-! Kernel-checked entropy margins for general spectral rectangle 486. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0486
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7656128634) (.branch 2 (.leaf 7438439272) (.leaf 7229530763))) (.branch 5 (.branch 4 (.leaf 7028937091) (.leaf 6836224340)) (.branch 6 (.leaf 6650987814) (.leaf 6472849481)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6301455706) (.leaf 6136475219)) (.branch 10 (.leaf 5977597307) (.leaf 5824530185))) (.branch 13 (.branch 12 (.leaf 5676999535) (.leaf 5534747177)) (.branch 14 (.leaf 5397529882) (.leaf 5265118280))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5137295881) (.branch 17 (.leaf 5013858172) (.leaf 4894611800))) (.branch 20 (.branch 19 (.leaf 4779373819) (.leaf 4667971006)) (.branch 21 (.leaf 4560239229) (.leaf 4456022865)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4355174264) (.leaf 4257553261)) (.branch 25 (.leaf 4163026714) (.leaf 4071468085))) (.branch 28 (.branch 27 (.leaf 3982757045) (.leaf 3896779117)) (.branch 29 (.leaf 3813425332) (.leaf 3732591921)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3654180016) (.branch 32 (.leaf 3578095384) (.leaf 3504248166))) (.branch 35 (.branch 34 (.leaf 3432552644) (.leaf 3362927017)) (.branch 36 (.leaf 3295293189) (.leaf 3229576580)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3165705939) (.leaf 3103613170)) (.branch 40 (.leaf 3043233177) (.leaf 2984503704))) (.branch 43 (.branch 42 (.leaf 2927365198) (.leaf 2871760673)) (.branch 44 (.leaf 2817635581) (.leaf 2764937695))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2713616994) (.branch 47 (.leaf 2663625558) (.leaf 2614917467))) (.branch 50 (.branch 49 (.leaf 2567448705) (.leaf 2521177071)) (.branch 51 (.leaf 2476062093) (.leaf 2432064950)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2389148390) (.leaf 2347276664)) (.branch 55 (.leaf 2306415454) (.leaf 2266531808))) (.branch 58 (.branch 57 (.leaf 2227594078) (.leaf 2189571865)) (.branch 59 (.leaf 2152435957) (.leaf 2116158283))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2080711856) (.branch 62 (.leaf 2046070733) (.leaf 2012209960))) (.branch 65 (.branch 64 (.leaf 1979105539) (.leaf 1946734378)) (.branch 66 (.leaf 1915074259) (.leaf 1884103794)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1853802395) (.leaf 1824150239)) (.branch 70 (.leaf 1795128231) (.leaf 1766717982))) (.branch 73 (.branch 72 (.leaf 1738901771) (.leaf 1711662521)) (.branch 74 (.leaf 1684983774) (.leaf 1658849662))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1633244884) (.branch 77 (.leaf 1608154685) (.leaf 1583564829))) (.branch 80 (.branch 79 (.leaf 1559461583) (.leaf 1535831693)) (.branch 81 (.leaf 1512662366) (.leaf 1489941254)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1467656430) (.leaf 1445796378)) (.branch 85 (.leaf 1424349973) (.leaf 1403306465))) (.branch 88 (.branch 87 (.leaf 1382655469) (.leaf 1362386944)) (.branch 89 (.leaf 1342491185) (.leaf 1322958806)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1303780732) (.branch 92 (.leaf 1284948183) (.leaf 1266452664))) (.branch 95 (.branch 94 (.leaf 1248285956) (.leaf 1230440103)) (.branch 96 (.leaf 1212907402) (.leaf 1195680396)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1178751861) (.leaf 1162114803)) (.branch 100 (.leaf 1145762441) (.leaf 1129688208))) (.branch 103 (.branch 102 (.leaf 1113885736) (.leaf 1098348855)) (.branch 104 (.leaf 1083071578) (.leaf 1068048102))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1053272797) (.leaf 1038740200)) (.branch 108 (.leaf 1024445011) (.leaf 1010382084))) (.branch 111 (.branch 110 (.leaf 996546425) (.leaf 982933183)) (.branch 112 (.leaf 969537649) (.leaf 956355247)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 943381532) (.leaf 930612183)) (.branch 116 (.leaf 918043003) (.leaf 905669908))) (.branch 119 (.branch 118 (.leaf 893488931) (.leaf 881496210)) (.branch 120 (.leaf 869687991) (.leaf 858060621)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 486).prefactor = (2477639399230941/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 486).cutoff/(generalMeanRows 486).c)).2 =
    (179326291033569/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 486).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 486).q*(generalMeanRows 486).c/2-2 = (39/80:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable085.value]
  have hcontinuation : (generalMeanRows 486).q*(generalMeanRows 486).cutoff/2-2 = (103/66:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable181.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 486).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 486).criticalRate j.val*(generalMeanRows 486).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 486).c*(generalMeanRows 486).criticalPoint j.val)).2-
      (generalMeanRows 486).J/2-(generalMeanRows 486).error (generalMeanGrid j.val)+
      (generalMeanRows 486).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 486).c)).2-
      (generalMeanRows 486).J/2-(generalMeanRows 486).error 4 := by
  have he : (generalMeanRows 486).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 486) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 486)
    (generalMeanRows_prefactorDomain 486) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0486

/-! Kernel-checked entropy margins for general spectral rectangle 487. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0487
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7034614483) (.branch 2 (.leaf 6808373825) (.leaf 6591416297))) (.branch 5 (.branch 4 (.leaf 6383253397) (.leaf 6183430143)) (.branch 6 (.leaf 5991522054) (.leaf 5807132491)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5629890284) (.leaf 5459447614)) (.branch 10 (.leaf 5295478126) (.leaf 5137675224))) (.branch 13 (.branch 12 (.leaf 4985750549) (.leaf 4839432593)) (.branch 14 (.leaf 4698465457) (.leaf 4562607716))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4431631392) (.branch 17 (.leaf 4305321015) (.leaf 4183472772))) (.branch 20 (.branch 19 (.leaf 4065893719) (.leaf 3952401068)) (.branch 21 (.leaf 3842821529) (.leaf 3736990704)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3634752526) (.leaf 3535958750)) (.branch 25 (.leaf 3440468476) (.leaf 3348147705))) (.branch 28 (.branch 27 (.leaf 3258868936) (.leaf 3172510786)) (.branch 29 (.leaf 3088957639) (.leaf 3008099316)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2929830775) (.branch 32 (.leaf 2854051823) (.leaf 2780666851))) (.branch 35 (.branch 34 (.leaf 2709584591) (.leaf 2640717878)) (.branch 36 (.leaf 2573983435) (.leaf 2509301672)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2446596493) (.leaf 2385795117)) (.branch 40 (.leaf 2326827910) (.leaf 2269628228))) (.branch 43 (.branch 42 (.leaf 2214132264) (.leaf 2160278915)) (.branch 44 (.leaf 2108009641) (.leaf 2057268349))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2008001270) (.branch 47 (.leaf 1960156847) (.leaf 1913685638))) (.branch 50 (.branch 49 (.leaf 1868540205) (.leaf 1824675032)) (.branch 51 (.leaf 1782046429) (.leaf 1740612448)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1700332807) (.leaf 1661168814)) (.branch 55 (.leaf 1623083293) (.leaf 1586040515))) (.branch 58 (.branch 57 (.leaf 1550006141) (.leaf 1514947151)) (.branch 59 (.leaf 1480831793) (.leaf 1447629526))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1415310964) (.branch 62 (.leaf 1383847832) (.leaf 1353212914))) (.branch 65 (.branch 64 (.leaf 1323380010) (.leaf 1294323890)) (.branch 66 (.leaf 1266020259) (.leaf 1238445710)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1211577695) (.leaf 1185394481)) (.branch 70 (.leaf 1159875124) (.leaf 1134999432))) (.branch 73 (.branch 72 (.leaf 1110747936) (.leaf 1087101860)) (.branch 74 (.leaf 1064043092) (.leaf 1041554159))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1019618202) (.branch 77 (.leaf 998218947) (.leaf 977340689))) (.branch 80 (.branch 79 (.leaf 956968262) (.leaf 937087023)) (.branch 81 (.leaf 917682830) (.leaf 898742020)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 880251396) (.leaf 862198202)) (.branch 85 (.leaf 844570113) (.leaf 827355212))) (.branch 88 (.branch 87 (.leaf 810541981) (.leaf 794119279)) (.branch 89 (.leaf 778076333) (.leaf 762402723)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 747088366) (.branch 92 (.leaf 732123506) (.leaf 717498703))) (.branch 95 (.branch 94 (.leaf 703204819) (.leaf 689233006)) (.branch 96 (.leaf 675574698) (.leaf 662221599)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 649165676) (.leaf 636399144)) (.branch 100 (.leaf 623914463) (.leaf 611704324))) (.branch 103 (.branch 102 (.leaf 599761644) (.leaf 588079559)) (.branch 104 (.leaf 576651413) (.leaf 565470750))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 554531313) (.leaf 543827031)) (.branch 108 (.leaf 533352013) (.leaf 523100545))) (.branch 111 (.branch 110 (.leaf 513067084) (.leaf 503246246)) (.branch 112 (.leaf 493632809) (.leaf 484221700)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 475007994) (.leaf 465986911)) (.branch 116 (.leaf 457153805) (.leaf 448504164))) (.branch 119 (.branch 118 (.leaf 440033605) (.leaf 431737868)) (.branch 120 (.leaf 423612813) (.leaf 415654416)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 487).prefactor = (650671885713237/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 487).cutoff/(generalMeanRows 487).c)).2 =
    (281319378663969/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 487).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 487).q*(generalMeanRows 487).c/2-2 = (11/16:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable087.value]
  have hcontinuation : (generalMeanRows 487).q*(generalMeanRows 487).cutoff/2-2 = (103/66:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable181.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 487).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 487).criticalRate j.val*(generalMeanRows 487).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 487).c*(generalMeanRows 487).criticalPoint j.val)).2-
      (generalMeanRows 487).J/2-(generalMeanRows 487).error (generalMeanGrid j.val)+
      (generalMeanRows 487).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 487).c)).2-
      (generalMeanRows 487).J/2-(generalMeanRows 487).error 4 := by
  have he : (generalMeanRows 487).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 487) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 487)
    (generalMeanRows_prefactorDomain 487) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0487

/-! Kernel-checked entropy margins for general spectral rectangle 488. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0488
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7107027051) (.branch 2 (.leaf 6899927324) (.leaf 6701342409))) (.branch 5 (.branch 4 (.leaf 6510813896) (.leaf 6327915002)) (.branch 6 (.leaf 6152247761) (.leaf 5983440522)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5821145736) (.leaf 5665037964)) (.branch 10 (.leaf 5514812098) (.leaf 5370181765))) (.branch 13 (.branch 12 (.leaf 5230877884) (.leaf 5096647359)) (.branch 14 (.leaf 4967251908) (.leaf 4842466981))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4722080792) (.branch 17 (.leaf 4605893430) (.leaf 4493716041))) (.branch 20 (.branch 19 (.leaf 4385370087) (.leaf 4280686665)) (.branch 21 (.leaf 4179505878) (.leaf 4081676256)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3987054227) (.leaf 3895503623)) (.branch 25 (.leaf 3806895228) (.leaf 3721106354))) (.branch 28 (.branch 27 (.leaf 3638020455) (.leaf 3557526759)) (.branch 29 (.leaf 3479519938) (.leaf 3403899789)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3330570945) (.branch 32 (.leaf 3259442603) (.leaf 3190428269))) (.branch 35 (.branch 34 (.leaf 3123445518) (.leaf 3058415778)) (.branch 36 (.leaf 2995264116) (.leaf 2933919046)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2874312346) (.leaf 2816378886)) (.branch 40 (.leaf 2760056467) (.leaf 2705285670))) (.branch 43 (.branch 42 (.leaf 2652009713) (.leaf 2600174318)) (.branch 44 (.leaf 2549727583) (.leaf 2500619864))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2452803664) (.branch 47 (.leaf 2406233524) (.leaf 2360865928))) (.branch 50 (.branch 49 (.leaf 2316659203) (.leaf 2273573432)) (.branch 51 (.leaf 2231570374) (.leaf 2190613376)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2150667304) (.leaf 2111698469)) (.branch 55 (.leaf 2073674559) (.leaf 2036564577))) (.branch 58 (.branch 57 (.leaf 2000338777) (.leaf 1964968609)) (.branch 59 (.leaf 1930426663) (.leaf 1896686616))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1863723186) (.branch 62 (.leaf 1831512082) (.leaf 1800029962))) (.branch 65 (.branch 64 (.leaf 1769254386) (.leaf 1739163783)) (.branch 66 (.leaf 1709737407) (.leaf 1680955303)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1652798271) (.leaf 1625247837)) (.branch 70 (.leaf 1598286217) (.leaf 1571896287))) (.branch 73 (.branch 72 (.leaf 1546061559) (.leaf 1520766151)) (.branch 74 (.leaf 1495994762) (.leaf 1471732645))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1447965589) (.branch 77 (.leaf 1424679889) (.leaf 1401862333))) (.branch 80 (.branch 79 (.leaf 1379500175) (.leaf 1357581119)) (.branch 81 (.leaf 1336093300) (.leaf 1315025265)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1294365958) (.leaf 1274104702)) (.branch 85 (.leaf 1254231185) (.leaf 1234735447))) (.branch 88 (.branch 87 (.leaf 1215607859) (.leaf 1196839119)) (.branch 89 (.leaf 1178420232) (.leaf 1160342500)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1142597514) (.branch 92 (.leaf 1125177134) (.leaf 1108073488))) (.branch 95 (.branch 94 (.leaf 1091278955) (.leaf 1074786158)) (.branch 96 (.leaf 1058587954) (.leaf 1042677426)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1027047873) (.leaf 1011692801)) (.branch 100 (.leaf 996605918) (.leaf 981781123))) (.branch 103 (.branch 102 (.leaf 967212504) (.leaf 952894323)) (.branch 104 (.leaf 938821017) (.leaf 924987189))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 911387599) (.leaf 898017162)) (.branch 108 (.leaf 884870943) (.leaf 871944146))) (.branch 111 (.branch 110 (.leaf 859232114) (.leaf 846730325)) (.branch 112 (.leaf 834434381) (.leaf 822340010)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 810443057) (.leaf 798739484)) (.branch 116 (.leaf 787225362) (.leaf 775896870))) (.branch 119 (.branch 118 (.leaf 764750288) (.leaf 753781999)) (.branch 120 (.leaf 742988480) (.leaf 732366300)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 488).prefactor = (4893791124759253/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 488).cutoff/(generalMeanRows 488).c)).2 =
    (369092144802517/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 488).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 488).q*(generalMeanRows 488).cutoff/2-2 = (128/77:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable182.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 488).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 488).criticalRate j.val*(generalMeanRows 488).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 488).c*(generalMeanRows 488).criticalPoint j.val)).2-
      (generalMeanRows 488).J/2-(generalMeanRows 488).error (generalMeanGrid j.val)+
      (generalMeanRows 488).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 488).c)).2-
      (generalMeanRows 488).J/2-(generalMeanRows 488).error 4 := by
  have he : (generalMeanRows 488).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 488) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 488)
    (generalMeanRows_prefactorDomain 488) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0488

/-! Kernel-checked entropy margins for general spectral rectangle 489. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0489
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6184503647) (.branch 2 (.leaf 5972887295) (.leaf 5770240874))) (.branch 5 (.branch 4 (.leaf 5576085981) (.leaf 5389976994)) (.branch 6 (.leaf 5211498157) (.leaf 5040261001)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4875902042) (.leaf 4718080722)) (.branch 10 (.leaf 4566477570) (.leaf 4420792544))) (.branch 13 (.branch 12 (.leaf 4280743539) (.leaf 4146065039)) (.branch 14 (.leaf 4016506895) (.leaf 3891833216))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3771821359) (.branch 17 (.leaf 3656261011) (.leaf 3544953346))) (.branch 20 (.branch 19 (.leaf 3437710257) (.leaf 3334353645)) (.branch 21 (.leaf 3234714778) (.leaf 3138633687)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3045958619) (.leaf 2956545528)) (.branch 25 (.leaf 2870257604) (.leaf 2786964839))) (.branch 28 (.branch 27 (.leaf 2706543622) (.leaf 2628876367)) (.branch 29 (.leaf 2553851163) (.leaf 2481361449)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2411305715) (.branch 32 (.leaf 2343587218) (.leaf 2278113720))) (.branch 35 (.branch 34 (.leaf 2214797243) (.leaf 2153553837)) (.branch 36 (.leaf 2094303368) (.leaf 2036969314)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1981478576) (.leaf 1927761302)) (.branch 40 (.leaf 1875750719) (.leaf 1825382977))) (.branch 43 (.branch 42 (.leaf 1776597000) (.leaf 1729334349)) (.branch 44 (.leaf 1683539089) (.leaf 1639157670))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1596138805) (.branch 47 (.leaf 1554433364) (.leaf 1513994268))) (.branch 50 (.branch 49 (.leaf 1474776394) (.leaf 1436736480)) (.branch 51 (.leaf 1399833038) (.leaf 1364026271)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1329277994) (.leaf 1295551562)) (.branch 55 (.leaf 1262811796) (.leaf 1231024919))) (.branch 58 (.branch 57 (.leaf 1200158491) (.leaf 1170181349)) (.branch 59 (.leaf 1141063552) (.leaf 1112776324))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1085292003) (.branch 62 (.leaf 1058583993) (.leaf 1032626718))) (.branch 65 (.branch 64 (.leaf 1007395577) (.leaf 982866899)) (.branch 66 (.leaf 959017909) (.leaf 935826685)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 913272123) (.leaf 891333904)) (.branch 70 (.leaf 869992456) (.leaf 849228932))) (.branch 73 (.branch 72 (.leaf 829025168) (.leaf 809363666)) (.branch 74 (.leaf 790227558) (.leaf 771600585))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 753467071) (.branch 77 (.leaf 735811896) (.leaf 718620481))) (.branch 80 (.branch 79 (.leaf 701878758) (.leaf 685573154)) (.branch 81 (.leaf 669690573) (.leaf 654218370)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 639144342) (.leaf 624456704)) (.branch 85 (.leaf 610144075) (.leaf 596195462))) (.branch 88 (.branch 87 (.leaf 582600247) (.leaf 569348168)) (.branch 89 (.leaf 556429311) (.leaf 543834090)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 531553240) (.branch 92 (.leaf 519577805) (.leaf 507899121))) (.branch 95 (.branch 94 (.leaf 496508809) (.leaf 485398764)) (.branch 96 (.leaf 474561146) (.leaf 463988366)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 453673080) (.leaf 443608180)) (.branch 100 (.leaf 433786785) (.leaf 424202230))) (.branch 103 (.branch 102 (.leaf 414848064) (.leaf 405718035)) (.branch 104 (.leaf 396806089) (.leaf 388106361))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 379613166) (.leaf 371320994)) (.branch 108 (.leaf 363224507) (.leaf 355318528))) (.branch 111 (.branch 110 (.leaf 347598036) (.leaf 340058166)) (.branch 112 (.leaf 332694197) (.leaf 325501549)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 318475781) (.leaf 311612583)) (.branch 116 (.leaf 304907771) (.leaf 298357287))) (.branch 119 (.branch 118 (.leaf 291957190) (.leaf 285703654)) (.branch 120 (.leaf 279592966) (.leaf 273621518)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 489).prefactor = (1021478587168889/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 489).cutoff/(generalMeanRows 489).c)).2 =
    (3373897808911/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 489).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 489).q*(generalMeanRows 489).c/2-2 = (199/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable053.value]
  have hcontinuation : (generalMeanRows 489).q*(generalMeanRows 489).cutoff/2-2 = (128/77:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable182.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 489).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 489).criticalRate j.val*(generalMeanRows 489).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 489).c*(generalMeanRows 489).criticalPoint j.val)).2-
      (generalMeanRows 489).J/2-(generalMeanRows 489).error (generalMeanGrid j.val)+
      (generalMeanRows 489).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 489).c)).2-
      (generalMeanRows 489).J/2-(generalMeanRows 489).error 4 := by
  have he : (generalMeanRows 489).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 489) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 489)
    (generalMeanRows_prefactorDomain 489) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0489

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock06 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 6 i) := by
  fin_cases i
  · exact EntropyRow0420.numerical
  · exact EntropyRow0421.numerical
  · exact EntropyRow0422.numerical
  · exact EntropyRow0423.numerical
  · exact EntropyRow0424.numerical
  · exact EntropyRow0425.numerical
  · exact EntropyRow0426.numerical
  · exact EntropyRow0427.numerical
  · exact EntropyRow0428.numerical
  · exact EntropyRow0429.numerical
  · exact EntropyRow0430.numerical
  · exact EntropyRow0431.numerical
  · exact EntropyRow0432.numerical
  · exact EntropyRow0433.numerical
  · exact EntropyRow0434.numerical
  · exact EntropyRow0435.numerical
  · exact EntropyRow0436.numerical
  · exact EntropyRow0437.numerical
  · exact EntropyRow0438.numerical
  · exact EntropyRow0439.numerical
  · exact EntropyRow0440.numerical
  · exact EntropyRow0441.numerical
  · exact EntropyRow0442.numerical
  · exact EntropyRow0443.numerical
  · exact EntropyRow0444.numerical
  · exact EntropyRow0445.numerical
  · exact EntropyRow0446.numerical
  · exact EntropyRow0447.numerical
  · exact EntropyRow0448.numerical
  · exact EntropyRow0449.numerical
  · exact EntropyRow0450.numerical
  · exact EntropyRow0451.numerical
  · exact EntropyRow0452.numerical
  · exact EntropyRow0453.numerical
  · exact EntropyRow0454.numerical
  · exact EntropyRow0455.numerical
  · exact EntropyRow0456.numerical
  · exact EntropyRow0457.numerical
  · exact EntropyRow0458.numerical
  · exact EntropyRow0459.numerical
  · exact EntropyRow0460.numerical
  · exact EntropyRow0461.numerical
  · exact EntropyRow0462.numerical
  · exact EntropyRow0463.numerical
  · exact EntropyRow0464.numerical
  · exact EntropyRow0465.numerical
  · exact EntropyRow0466.numerical
  · exact EntropyRow0467.numerical
  · exact EntropyRow0468.numerical
  · exact EntropyRow0469.numerical
  · exact EntropyRow0470.numerical
  · exact EntropyRow0471.numerical
  · exact EntropyRow0472.numerical
  · exact EntropyRow0473.numerical
  · exact EntropyRow0474.numerical
  · exact EntropyRow0475.numerical
  · exact EntropyRow0476.numerical
  · exact EntropyRow0477.numerical
  · exact EntropyRow0478.numerical
  · exact EntropyRow0479.numerical
  · exact EntropyRow0480.numerical
  · exact EntropyRow0481.numerical
  · exact EntropyRow0482.numerical
  · exact EntropyRow0483.numerical
  · exact EntropyRow0484.numerical
  · exact EntropyRow0485.numerical
  · exact EntropyRow0486.numerical
  · exact EntropyRow0487.numerical
  · exact EntropyRow0488.numerical
  · exact EntropyRow0489.numerical
end SingularValueBounds.KL.Certificates
