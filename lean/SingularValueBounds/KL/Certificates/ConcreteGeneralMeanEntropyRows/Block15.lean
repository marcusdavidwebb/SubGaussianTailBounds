import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs
import SingularValueBounds.KL.Certificates.GeneralMeanPrefactorLogs
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block17
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block19
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block20
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block21
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block22
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block23
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 1050. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1050
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5575577201) (.branch 2 (.leaf 5389750921) (.leaf 5211757191))) (.branch 5 (.branch 4 (.leaf 5041170426) (.leaf 4877594583)) (.branch 6 (.leaf 4720660568) (.leaf 4570023930)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4425362803) (.leaf 4286376051)) (.branch 10 (.leaf 4152781609) (.leaf 4024314985))) (.branch 13 (.branch 12 (.leaf 3900727907) (.leaf 3781787095)) (.branch 14 (.leaf 3667273148) (.leaf 3556979537))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3450711676) (.branch 17 (.leaf 3348286084) (.leaf 3249529612))) (.branch 20 (.branch 19 (.leaf 3154278742) (.leaf 3062378931)) (.branch 21 (.leaf 2973684023) (.leaf 2888055696)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2805362960) (.leaf 2725481685)) (.branch 25 (.leaf 2648294176) (.leaf 2573688770))) (.branch 28 (.branch 27 (.leaf 2501559467) (.leaf 2431805587)) (.branch 29 (.leaf 2364331450) (.leaf 2299046083)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2235862940) (.branch 32 (.leaf 2174699651) (.leaf 2115477776))) (.branch 35 (.branch 34 (.leaf 2058122589) (.leaf 2002562861)) (.branch 36 (.leaf 1948730674) (.leaf 1896561234)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1845992699) (.leaf 1796966023)) (.branch 40 (.leaf 1749424804) (.leaf 1703315145))) (.branch 43 (.branch 42 (.leaf 1658585520) (.leaf 1615186653)) (.branch 44 (.leaf 1573071398) (.leaf 1532194633))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1492513157) (.branch 47 (.leaf 1453985589) (.leaf 1416572282))) (.branch 50 (.branch 49 (.leaf 1380235233) (.leaf 1344938006)) (.branch 51 (.leaf 1310645650) (.leaf 1277324632)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1244942766) (.leaf 1213469150)) (.branch 55 (.leaf 1182874104) (.leaf 1153129114))) (.branch 58 (.branch 57 (.leaf 1124206775) (.leaf 1096080744)) (.branch 59 (.leaf 1068725685) (.leaf 1042117230))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1016231929) (.branch 62 (.leaf 991047213) (.leaf 966541352))) (.branch 65 (.branch 64 (.leaf 942693419) (.leaf 919483255)) (.branch 66 (.leaf 896891434) (.leaf 874899233)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 853488600) (.leaf 832642127)) (.branch 70 (.leaf 812343021) (.leaf 792575078))) (.branch 73 (.branch 72 (.leaf 773322662) (.leaf 754570675)) (.branch 74 (.leaf 736304542) (.leaf 718510183))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 701173998) (.branch 77 (.leaf 684282842) (.leaf 667824015))) (.branch 80 (.branch 79 (.leaf 651785235) (.leaf 636154628)) (.branch 81 (.leaf 620920709) (.leaf 606072369)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 591598858) (.leaf 577489772)) (.branch 85 (.leaf 563735039) (.leaf 550324911))) (.branch 88 (.branch 87 (.leaf 537249944) (.leaf 524500994)) (.branch 89 (.leaf 512069201) (.leaf 499945980)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 488123012) (.branch 92 (.leaf 476592233) (.leaf 465345824))) (.branch 95 (.branch 94 (.leaf 454376206) (.leaf 443676026)) (.branch 96 (.leaf 433238153) (.leaf 423055669)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 413121862) (.leaf 403430216)) (.branch 100 (.leaf 393974408) (.leaf 384748301))) (.branch 103 (.branch 102 (.leaf 375745934) (.leaf 366961521)) (.branch 104 (.leaf 358389441) (.leaf 350024235))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 341860600) (.leaf 333893382)) (.branch 108 (.leaf 326117574) (.leaf 318528309))) (.branch 111 (.branch 110 (.leaf 311120859) (.leaf 303890623)) (.branch 112 (.leaf 296833133) (.leaf 289944041)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 283219120) (.leaf 276654259)) (.branch 116 (.leaf 270245458) (.leaf 263988829))) (.branch 119 (.branch 118 (.leaf 257880585) (.leaf 251917045)) (.branch 120 (.leaf 246094625) (.leaf 240409837)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1050).prefactor = (5217144433682381/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1050).cutoff/(generalMeanRows 1050).c)).2 =
    (338124664959033/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1050).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1050).q*(generalMeanRows 1050).cutoff/2-2 = (407/196:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable340.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1050).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1050).criticalRate j.val*(generalMeanRows 1050).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1050).c*(generalMeanRows 1050).criticalPoint j.val)).2-
      (generalMeanRows 1050).J/2-(generalMeanRows 1050).error (generalMeanGrid j.val)+
      (generalMeanRows 1050).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1050).c)).2-
      (generalMeanRows 1050).J/2-(generalMeanRows 1050).error 4 := by
  have he : (generalMeanRows 1050).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1050) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1050)
    (generalMeanRows_prefactorDomain 1050) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1050

/-! Kernel-checked entropy margins for general spectral rectangle 1051. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1051
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5690381473) (.branch 2 (.leaf 5498534528) (.leaf 5314811044))) (.branch 5 (.branch 4 (.leaf 5138769650) (.leaf 4969999575)) (.branch 6 (.leaf 4808117968) (.leaf 4652767511)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4503614284) (.leaf 4360345846)) (.branch 10 (.leaf 4222669523) (.leaf 4090310850))) (.branch 13 (.branch 12 (.leaf 3963012170) (.leaf 3840531369)) (.branch 14 (.leaf 3722640721) (.leaf 3609125838))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3499784720) (.branch 17 (.leaf 3394426878) (.leaf 3292872539))) (.branch 20 (.branch 19 (.leaf 3194951913) (.leaf 3100504522)) (.branch 21 (.leaf 3009378587) (.leaf 2921430454)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2836524075) (.leaf 2754530520)) (.branch 25 (.leaf 2675327537) (.leaf 2598799131))) (.branch 28 (.branch 27 (.leaf 2524835186) (.leaf 2453331106)) (.branch 29 (.leaf 2384187487) (.leaf 2317309810)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2252608153) (.branch 32 (.leaf 2189996930) (.leaf 2129394635))) (.branch 35 (.branch 34 (.leaf 2070723619) (.leaf 2013909868)) (.branch 36 (.leaf 1958882805) (.leaf 1905575096)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1853922480) (.leaf 1803863596)) (.branch 40 (.leaf 1755339833) (.leaf 1708295183))) (.branch 43 (.branch 42 (.leaf 1662676102) (.leaf 1618431384)) (.branch 44 (.leaf 1575512040) (.leaf 1533871183))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1493463924) (.branch 47 (.leaf 1454247267) (.leaf 1416180019))) (.branch 50 (.branch 49 (.leaf 1379222698) (.leaf 1343337448)) (.branch 51 (.leaf 1308487964) (.leaf 1274639411)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1241758358) (.leaf 1209812710)) (.branch 55 (.leaf 1178771642) (.leaf 1148605544))) (.branch 58 (.branch 57 (.leaf 1119285961) (.leaf 1090785540)) (.branch 59 (.leaf 1063077980) (.leaf 1036137986))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1009941218) (.branch 62 (.leaf 984464254) (.leaf 959684546))) (.branch 65 (.branch 64 (.leaf 935580382) (.leaf 912130849)) (.branch 66 (.leaf 889315797) (.leaf 867115810)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 845512168) (.leaf 824486825)) (.branch 70 (.leaf 804022372) (.leaf 784102017))) (.branch 73 (.branch 72 (.leaf 764709557) (.leaf 745829350)) (.branch 74 (.leaf 727446299) (.leaf 709545822))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 692113838) (.branch 77 (.leaf 675136740) (.leaf 658601382))) (.branch 80 (.branch 79 (.leaf 642495056) (.leaf 626805479)) (.branch 81 (.leaf 611520772) (.leaf 596629447)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 582120390) (.leaf 567982850)) (.branch 85 (.leaf 554206420) (.leaf 540781027))) (.branch 88 (.branch 87 (.leaf 527696921) (.leaf 514944660)) (.branch 89 (.leaf 502515097) (.leaf 490399375)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 478588911) (.branch 92 (.leaf 467075389) (.leaf 455850746))) (.branch 95 (.branch 94 (.leaf 444907171) (.leaf 434237086)) (.branch 96 (.leaf 423833147) (.leaf 413688228)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 403795418) (.leaf 394148013)) (.branch 100 (.leaf 384739507) (.leaf 375563586))) (.branch 103 (.branch 102 (.leaf 366614124) (.leaf 357885172)) (.branch 104 (.leaf 349370954) (.leaf 341065863))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 332964452) (.leaf 325061433)) (.branch 108 (.leaf 317351666) (.leaf 309830161))) (.branch 111 (.branch 110 (.leaf 302492066) (.leaf 295332668)) (.branch 112 (.leaf 288347386) (.leaf 281531768)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 274881484) (.leaf 268392326)) (.branch 116 (.leaf 262060203) (.leaf 255881135))) (.branch 119 (.branch 118 (.leaf 249851253) (.leaf 243966792)) (.branch 120 (.leaf 238224091) (.leaf 232619587)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1051).prefactor = (5402261213923671/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1051).cutoff/(generalMeanRows 1051).c)).2 =
    (4153671808103/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1051).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1051).q*(generalMeanRows 1051).c/2-2 = (231/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable341.value]
  have hcontinuation : (generalMeanRows 1051).q*(generalMeanRows 1051).cutoff/2-2 = (407/196:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable340.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1051).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1051).criticalRate j.val*(generalMeanRows 1051).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1051).c*(generalMeanRows 1051).criticalPoint j.val)).2-
      (generalMeanRows 1051).J/2-(generalMeanRows 1051).error (generalMeanGrid j.val)+
      (generalMeanRows 1051).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1051).c)).2-
      (generalMeanRows 1051).J/2-(generalMeanRows 1051).error 4 := by
  have he : (generalMeanRows 1051).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1051) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1051)
    (generalMeanRows_prefactorDomain 1051) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1051

/-! Kernel-checked entropy margins for general spectral rectangle 1052. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1052
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5892289836) (.branch 2 (.leaf 5693635703) (.leaf 5503393269))) (.branch 5 (.branch 4 (.leaf 5321105505) (.leaf 5146347063)) (.branch 6 (.leaf 4978721510) (.leaf 4817858847)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4663413305) (.leaf 4515061361)) (.branch 10 (.leaf 4372499952) (.leaf 4235444875))) (.branch 13 (.branch 12 (.leaf 4103629333) (.leaf 3976802621)) (.branch 14 (.leaf 3854728930) (.leaf 3737186267))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3623965465) (.branch 17 (.leaf 3514869274) (.leaf 3409711544))) (.branch 20 (.branch 19 (.leaf 3308316459) (.leaf 3210517849)) (.branch 21 (.leaf 3116158547) (.leaf 3025089804)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2937170743) (.leaf 2852267861)) (.branch 25 (.leaf 2770254566) (.leaf 2691010749))) (.branch 28 (.branch 27 (.leaf 2614422386) (.leaf 2540381169)) (.branch 29 (.leaf 2468784169) (.leaf 2399533512)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2332536086) (.branch 32 (.leaf 2267703266) (.leaf 2204950657))) (.branch 35 (.branch 34 (.leaf 2144197853) (.leaf 2085368214)) (.branch 36 (.leaf 2028388658) (.leaf 1973189465)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1919704090) (.leaf 1867868997)) (.branch 40 (.leaf 1817623495) (.leaf 1768909588))) (.branch 43 (.branch 42 (.leaf 1721671832) (.leaf 1675857206)) (.branch 44 (.leaf 1631414981) (.leaf 1588296607))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1546455601) (.branch 47 (.leaf 1505847444) (.leaf 1466429478))) (.branch 50 (.branch 49 (.leaf 1428160823) (.leaf 1391002278)) (.branch 51 (.leaf 1354916251) (.leaf 1319866670)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1285818919) (.leaf 1252739762)) (.branch 55 (.leaf 1220597283) (.leaf 1189360820))) (.branch 58 (.branch 57 (.leaf 1159000908) (.leaf 1129489223)) (.branch 59 (.leaf 1100798533) (.leaf 1072902643))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1045776351) (.branch 62 (.leaf 1019395404) (.leaf 993736453))) (.branch 65 (.branch 64 (.leaf 968777015) (.leaf 944495436)) (.branch 66 (.leaf 920870852) (.leaf 897883155)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 875512965) (.leaf 853741592)) (.branch 70 (.leaf 832551011) (.leaf 811923835))) (.branch 73 (.branch 72 (.leaf 791843283) (.leaf 772293162)) (.branch 74 (.leaf 753257836) (.leaf 734722208))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 716671694) (.branch 77 (.leaf 699092208) (.leaf 681970136))) (.branch 80 (.branch 79 (.leaf 665292320) (.leaf 649046039)) (.branch 81 (.leaf 633218994) (.leaf 617799289)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 602775416) (.leaf 588136242)) (.branch 85 (.leaf 573870991) (.leaf 559969233))) (.branch 88 (.branch 87 (.leaf 546420872) (.leaf 533216129)) (.branch 89 (.leaf 520345536) (.leaf 507799920)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 495570392) (.branch 92 (.leaf 483648342) (.leaf 472025423))) (.branch 95 (.branch 94 (.leaf 460693543) (.leaf 449644858)) (.branch 96 (.leaf 438871762) (.leaf 428366877)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 418123046) (.leaf 408133328)) (.branch 100 (.leaf 398390986) (.leaf 388889482))) (.branch 103 (.branch 102 (.leaf 379622472) (.leaf 370583795)) (.branch 104 (.leaf 361767472) (.leaf 353167696))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 344778828) (.leaf 336595391)) (.branch 108 (.leaf 328612063) (.leaf 320823677))) (.branch 111 (.branch 110 (.leaf 313225209) (.leaf 305811778)) (.branch 112 (.leaf 298578642) (.leaf 291521189)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 284634937) (.leaf 277915529)) (.branch 116 (.leaf 271358727) (.leaf 264960411))) (.branch 119 (.branch 118 (.leaf 258716574) (.leaf 252623318)) (.branch 120 (.leaf 246676852) (.leaf 240873488)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1052).prefactor = (5593946380906501/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1052).cutoff/(generalMeanRows 1052).c)).2 =
    (4153671808103/12500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1052).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1052).q*(generalMeanRows 1052).c/2-2 = (231/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable341.value]
  have hcontinuation : (generalMeanRows 1052).q*(generalMeanRows 1052).cutoff/2-2 = (407/196:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable340.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1052).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1052).criticalRate j.val*(generalMeanRows 1052).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1052).c*(generalMeanRows 1052).criticalPoint j.val)).2-
      (generalMeanRows 1052).J/2-(generalMeanRows 1052).error (generalMeanGrid j.val)+
      (generalMeanRows 1052).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1052).c)).2-
      (generalMeanRows 1052).J/2-(generalMeanRows 1052).error 4 := by
  have he : (generalMeanRows 1052).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1052) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1052)
    (generalMeanRows_prefactorDomain 1052) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1052

/-! Kernel-checked entropy margins for general spectral rectangle 1053. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1053
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6435508793) (.branch 2 (.leaf 6242523864) (.leaf 6057428008))) (.branch 5 (.branch 4 (.leaf 5879785945) (.leaf 5709193173)) (.branch 6 (.leaf 5545273245) (.leaf 5387675360)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5236072196) (.leaf 5090157972)) (.branch 10 (.leaf 4949646706) (.leaf 4814270641))) (.branch 13 (.branch 12 (.leaf 4683778828) (.leaf 4557935836)) (.branch 14 (.leaf 4436520590) (.leaf 4319325303))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4206154515) (.branch 17 (.leaf 4096824204) (.leaf 3991160984))) (.branch 20 (.branch 19 (.leaf 3889001359) (.leaf 3790191051)) (.branch 21 (.leaf 3694584371) (.leaf 3602043650)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3512438705) (.leaf 3425646356)) (.branch 25 (.leaf 3341549973) (.leaf 3260039061))) (.branch 28 (.branch 27 (.leaf 3181008873) (.leaf 3104360054)) (.branch 29 (.leaf 3029998308) (.leaf 2957834091)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2887782324) (.branch 32 (.leaf 2819762129) (.leaf 2753696577))) (.branch 35 (.branch 34 (.leaf 2689512463) (.leaf 2627140083)) (.branch 36 (.leaf 2566513041) (.leaf 2507568054)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2450244780) (.leaf 2394485656)) (.branch 40 (.leaf 2340235739) (.leaf 2287442565))) (.branch 43 (.branch 42 (.leaf 2236056015) (.leaf 2186028188)) (.branch 44 (.leaf 2137313280) (.leaf 2089867475))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2043648843) (.branch 47 (.leaf 1998617234) (.leaf 1954734193))) (.branch 50 (.branch 49 (.leaf 1911962870) (.leaf 1870267939)) (.branch 51 (.leaf 1829615519) (.leaf 1789973105)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1751309497) (.leaf 1713594735)) (.branch 55 (.leaf 1676800041) (.leaf 1640897761))) (.branch 58 (.branch 57 (.leaf 1605861308) (.leaf 1571665113)) (.branch 59 (.leaf 1538284579) (.leaf 1505696031))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1473876675) (.branch 62 (.leaf 1442804558) (.leaf 1412458527))) (.branch 65 (.branch 64 (.leaf 1382818197) (.leaf 1353863909)) (.branch 66 (.leaf 1325576705) (.leaf 1297938292)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1270931014) (.leaf 1244537826)) (.branch 70 (.leaf 1218742265) (.leaf 1193528423))) (.branch 73 (.branch 72 (.leaf 1168880930) (.leaf 1144784924)) (.branch 74 (.leaf 1121226036) (.leaf 1098190362))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1075664452) (.branch 77 (.leaf 1053635285) (.leaf 1032090256))) (.branch 80 (.branch 79 (.leaf 1011017155) (.leaf 990404155)) (.branch 81 (.leaf 970239794) (.leaf 950512964)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 931212894) (.leaf 912329137)) (.branch 85 (.leaf 893851561) (.leaf 875770332))) (.branch 88 (.branch 87 (.leaf 858075909) (.leaf 840759027)) (.branch 89 (.leaf 823810690) (.leaf 807222162)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 790984953) (.branch 92 (.leaf 775090817) (.leaf 759531736))) (.branch 95 (.branch 94 (.leaf 744299919) (.leaf 729387787)) (.branch 96 (.leaf 714787971) (.leaf 700493303)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 686496809) (.leaf 672791701)) (.branch 100 (.leaf 659371373) (.leaf 646229395))) (.branch 103 (.branch 102 (.leaf 633359505) (.leaf 620755605)) (.branch 104 (.leaf 608411755) (.leaf 596322169))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 584481210) (.leaf 572883384)) (.branch 108 (.leaf 561523335) (.leaf 550395843))) (.branch 111 (.branch 110 (.leaf 539495819) (.leaf 528818301)) (.branch 112 (.leaf 518358448) (.leaf 508111539)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 498072969) (.leaf 488238245)) (.branch 116 (.leaf 478602982) (.leaf 469162902))) (.branch 119 (.branch 118 (.leaf 459913828) (.leaf 450851684)) (.branch 120 (.leaf 441972490) (.leaf 433272359)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1053).prefactor = (2705913355760017/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1053).cutoff/(generalMeanRows 1053).c)).2 =
    (8143693416309/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1053).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1053).q*(generalMeanRows 1053).c/2-2 = (6177/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable342.value]
  have hcontinuation : (generalMeanRows 1053).q*(generalMeanRows 1053).cutoff/2-2 = (1637/756:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable343.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1053).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1053).criticalRate j.val*(generalMeanRows 1053).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1053).c*(generalMeanRows 1053).criticalPoint j.val)).2-
      (generalMeanRows 1053).J/2-(generalMeanRows 1053).error (generalMeanGrid j.val)+
      (generalMeanRows 1053).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1053).c)).2-
      (generalMeanRows 1053).J/2-(generalMeanRows 1053).error 4 := by
  have he : (generalMeanRows 1053).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1053) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1053)
    (generalMeanRows_prefactorDomain 1053) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1053

/-! Kernel-checked entropy margins for general spectral rectangle 1054. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1054
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6749956169) (.branch 2 (.leaf 6550236873) (.leaf 6358650184))) (.branch 5 (.branch 4 (.leaf 6174746884) (.leaf 5998109555)) (.branch 6 (.leaf 5828349776) (.leaf 5665105623)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5508039434) (.leaf 5356835801)) (.branch 10 (.leaf 5211199772) (.leaf 5070855224))) (.branch 13 (.branch 12 (.leaf 4935543395) (.leaf 4805021554)) (.branch 14 (.leaf 4679061795) (.leaf 4557449940))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4439984537) (.branch 17 (.leaf 4326475948) (.leaf 4216745516))) (.branch 20 (.branch 19 (.leaf 4110624796) (.leaf 4007954860)) (.branch 21 (.leaf 3908585644) (.leaf 3812375364)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3719189962) (.leaf 3628902607)) (.branch 25 (.leaf 3541393227) (.leaf 3456548079))) (.branch 28 (.branch 27 (.leaf 3374259351) (.leaf 3294424793)) (.branch 29 (.leaf 3216947372) (.leaf 3141734957)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3068700022) (.branch 32 (.leaf 2997759370) (.leaf 2928833879))) (.branch 35 (.branch 34 (.leaf 2861848261) (.leaf 2796730840)) (.branch 36 (.leaf 2733413347) (.leaf 2671830722)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2611920936) (.leaf 2553624818)) (.branch 40 (.leaf 2496885900) (.leaf 2441650267))) (.branch 43 (.branch 42 (.leaf 2387866415) (.leaf 2335485127)) (.branch 44 (.leaf 2284459342) (.leaf 2234744048))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2186296170) (.branch 47 (.leaf 2139074467) (.leaf 2093039442))) (.branch 50 (.branch 49 (.leaf 2048153247) (.leaf 2004379601)) (.branch 51 (.leaf 1961683713) (.leaf 1920032201)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1879393027) (.leaf 1839735429)) (.branch 55 (.leaf 1801029858) (.leaf 1763247917))) (.branch 58 (.branch 57 (.leaf 1726362310) (.leaf 1690346785)) (.branch 59 (.leaf 1655176085) (.leaf 1620825904))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1587272837) (.branch 62 (.leaf 1554494344) (.leaf 1522468707))) (.branch 65 (.branch 64 (.leaf 1491174992) (.leaf 1460593014)) (.branch 66 (.leaf 1430703305) (.leaf 1401487081)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1372926208) (.leaf 1345003179)) (.branch 70 (.leaf 1317701086) (.leaf 1291003589))) (.branch 73 (.branch 72 (.leaf 1264894897) (.leaf 1239359744)) (.branch 74 (.leaf 1214383363) (.leaf 1189951469))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1166050240) (.branch 77 (.leaf 1142666292) (.leaf 1119786668))) (.branch 80 (.branch 79 (.leaf 1097398816) (.leaf 1075490576)) (.branch 81 (.leaf 1054050161) (.leaf 1033066146)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1012527451) (.leaf 992423329)) (.branch 85 (.leaf 972743353) (.leaf 953477405))) (.branch 88 (.branch 87 (.leaf 934615660) (.leaf 916148583)) (.branch 89 (.leaf 898066908) (.leaf 880361637)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 863024026) (.branch 92 (.leaf 846045577) (.leaf 829418028))) (.branch 95 (.branch 94 (.leaf 813133346) (.leaf 797183719)) (.branch 96 (.leaf 781561545) (.leaf 766259432)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 751270182) (.leaf 736586792)) (.branch 100 (.leaf 722202441) (.leaf 708110489))) (.branch 103 (.branch 102 (.leaf 694304469) (.leaf 680778082)) (.branch 104 (.leaf 667525189) (.leaf 654539809))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 641816113) (.leaf 629348419)) (.branch 108 (.leaf 617131186) (.leaf 605159013))) (.branch 111 (.branch 110 (.leaf 593426631) (.leaf 581928901)) (.branch 112 (.leaf 570660810) (.leaf 559617467)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 548794099) (.leaf 538186047)) (.branch 116 (.leaf 527788764) (.leaf 517597812))) (.branch 119 (.branch 118 (.leaf 507608856) (.leaf 497817665)) (.branch 120 (.leaf 488220105) (.leaf 478812141)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1054).prefactor = (1118381869808811/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1054).cutoff/(generalMeanRows 1054).c)).2 =
    (206622647713571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1054).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1054).q*(generalMeanRows 1054).cutoff/2-2 = (1637/756:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable343.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1054).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1054).criticalRate j.val*(generalMeanRows 1054).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1054).c*(generalMeanRows 1054).criticalPoint j.val)).2-
      (generalMeanRows 1054).J/2-(generalMeanRows 1054).error (generalMeanGrid j.val)+
      (generalMeanRows 1054).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1054).c)).2-
      (generalMeanRows 1054).J/2-(generalMeanRows 1054).error 4 := by
  have he : (generalMeanRows 1054).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1054) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1054)
    (generalMeanRows_prefactorDomain 1054) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1054

/-! Kernel-checked entropy margins for general spectral rectangle 1055. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1055
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6934295688) (.branch 2 (.leaf 6711270764) (.leaf 6497521289))) (.branch 5 (.branch 4 (.leaf 6292542887) (.leaf 6095866319)) (.branch 6 (.leaf 5907054395) (.leaf 5725699226)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5551419765) (.leaf 5383859607)) (.branch 10 (.leaf 5222685006) (.leaf 5067583093))) (.branch 13 (.branch 12 (.leaf 4918260259) (.leaf 4774440703)) (.branch 14 (.leaf 4635865098) (.leaf 4502289392))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4373483707) (.branch 17 (.leaf 4249231339) (.leaf 4129327836))) (.branch 20 (.branch 19 (.leaf 4013580164) (.leaf 3901805931)) (.branch 21 (.leaf 3793832679) (.leaf 3689497235)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3588645107) (.leaf 3491129927)) (.branch 25 (.leaf 3396812943) (.leaf 3305562541))) (.branch 28 (.branch 27 (.leaf 3217253806) (.leaf 3131768113)) (.branch 29 (.leaf 3048992751) (.leaf 2968820570)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2891149651) (.branch 32 (.leaf 2815883007) (.leaf 2742928291))) (.branch 35 (.branch 34 (.leaf 2672197540) (.leaf 2603606919)) (.branch 36 (.leaf 2537076496) (.leaf 2472530024)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2409894736) (.leaf 2349101159)) (.branch 40 (.leaf 2290082936) (.leaf 2232776659))) (.branch 43 (.branch 42 (.leaf 2177121711) (.leaf 2123060123)) (.branch 44 (.leaf 2070536432) (.leaf 2019497558))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1969892673) (.branch 47 (.leaf 1921673095) (.leaf 1874792175))) (.branch 50 (.branch 49 (.leaf 1829205197) (.leaf 1784869283)) (.branch 51 (.leaf 1741743301) (.leaf 1699787781)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1658964834) (.leaf 1619238075)) (.branch 55 (.leaf 1580572553) (.leaf 1542934684))) (.branch 58 (.branch 57 (.leaf 1506292185) (.leaf 1470614011)) (.branch 59 (.leaf 1435870305) (.leaf 1402032335))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1369072450) (.branch 62 (.leaf 1336964025) (.leaf 1305681420))) (.branch 65 (.branch 64 (.leaf 1275199934) (.leaf 1245495762)) (.branch 66 (.leaf 1216545958) (.leaf 1188328396)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1160821736) (.leaf 1134005390)) (.branch 70 (.leaf 1107859488) (.leaf 1082364849))) (.branch 73 (.branch 72 (.leaf 1057502955) (.leaf 1033255916)) (.branch 74 (.leaf 1009606452) (.leaf 986537863))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 964034008) (.branch 77 (.leaf 942079279) (.leaf 920658584))) (.branch 80 (.branch 79 (.leaf 899757322) (.leaf 879361368)) (.branch 81 (.leaf 859457051) (.leaf 840031137)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 821070812) (.leaf 802563668)) (.branch 85 (.leaf 784497683) (.leaf 766861212))) (.branch 88 (.branch 87 (.leaf 749642969) (.leaf 732832013)) (.branch 89 (.leaf 716417738) (.leaf 700389860)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 684738403) (.branch 92 (.leaf 669453691) (.leaf 654526335))) (.branch 95 (.branch 94 (.leaf 639947224) (.leaf 625707513)) (.branch 96 (.leaf 611798616) (.leaf 598212197)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 584940159) (.leaf 571974639)) (.branch 100 (.leaf 559307995) (.leaf 546932805))) (.branch 103 (.branch 102 (.leaf 534841854) (.leaf 523028131)) (.branch 104 (.leaf 511484818) (.leaf 500205289))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 489183098) (.leaf 478411979)) (.branch 108 (.leaf 467885833) (.leaf 457598731))) (.branch 111 (.branch 110 (.leaf 447544901) (.leaf 437718728)) (.branch 112 (.leaf 428114746) (.leaf 418727636)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 409552219) (.leaf 400583454)) (.branch 116 (.leaf 391816431) (.leaf 383246369))) (.branch 119 (.branch 118 (.leaf 374868612) (.leaf 366678625)) (.branch 120 (.leaf 358671988) (.leaf 350844397)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1055).prefactor = (1242156892934647/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1055).cutoff/(generalMeanRows 1055).c)).2 =
    (177912121029217/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1055).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1055).q*(generalMeanRows 1055).c/2-2 = (107/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable344.value]
  have hcontinuation : (generalMeanRows 1055).q*(generalMeanRows 1055).cutoff/2-2 = (407/196:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable340.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1055).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1055).criticalRate j.val*(generalMeanRows 1055).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1055).c*(generalMeanRows 1055).criticalPoint j.val)).2-
      (generalMeanRows 1055).J/2-(generalMeanRows 1055).error (generalMeanGrid j.val)+
      (generalMeanRows 1055).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1055).c)).2-
      (generalMeanRows 1055).J/2-(generalMeanRows 1055).error 4 := by
  have he : (generalMeanRows 1055).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1055) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1055)
    (generalMeanRows_prefactorDomain 1055) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1055

/-! Kernel-checked entropy margins for general spectral rectangle 1056. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1056
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7192150619) (.branch 2 (.leaf 6987429074) (.leaf 6790612444))) (.branch 5 (.branch 4 (.leaf 6601289064) (.leaf 6419075561)) (.branch 6 (.leaf 6243614330) (.leaf 6074571297)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5911633924) (.leaf 5754509427)) (.branch 10 (.leaf 5602923178) (.leaf 5456617272))) (.branch 13 (.branch 12 (.leaf 5315349231) (.leaf 5178890835)) (.branch 14 (.leaf 5047027066) (.leaf 4919555147))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4796283668) (.branch 17 (.leaf 4677031790) (.leaf 4561628517))) (.branch 20 (.branch 19 (.leaf 4449912031) (.leaf 4341729083)) (.branch 21 (.leaf 4236934432) (.leaf 4135390329)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4036966042) (.leaf 3941537423)) (.branch 25 (.leaf 3848986496) (.leaf 3759201086))) (.branch 28 (.branch 27 (.leaf 3672074473) (.leaf 3587505071)) (.branch 29 (.leaf 3505396125) (.leaf 3425655436)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3348195102) (.branch 32 (.leaf 3272931275) (.leaf 3199783942))) (.branch 35 (.branch 34 (.leaf 3128676704) (.leaf 3059536591)) (.branch 36 (.leaf 2992293872) (.leaf 2926881883)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2863236868) (.leaf 2801297827)) (.branch 40 (.leaf 2741006372) (.leaf 2682306597))) (.branch 43 (.branch 42 (.leaf 2625144951) (.leaf 2569470118)) (.branch 44 (.leaf 2515232910) (.leaf 2462386157))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2410884616) (.branch 47 (.leaf 2360684870) (.leaf 2311745244))) (.branch 50 (.branch 49 (.leaf 2264025722) (.leaf 2217487870)) (.branch 51 (.leaf 2172094757) (.leaf 2127810892)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2084602149) (.leaf 2042435715)) (.branch 55 (.leaf 2001280019) (.leaf 1961104684))) (.branch 58 (.branch 57 (.leaf 1921880472) (.leaf 1883579231)) (.branch 59 (.leaf 1846173846) (.leaf 1809638199))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1773947120) (.branch 62 (.leaf 1739076348) (.leaf 1705002493))) (.branch 65 (.branch 64 (.leaf 1671702997) (.leaf 1639156098)) (.branch 66 (.leaf 1607340800) (.leaf 1576236837)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1545824644) (.leaf 1516085329)) (.branch 70 (.leaf 1487000642) (.leaf 1458552954))) (.branch 73 (.branch 72 (.leaf 1430725228) (.leaf 1403500994)) (.branch 74 (.leaf 1376864330) (.leaf 1350799839))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1325292624) (.branch 77 (.leaf 1300328276) (.leaf 1275892848))) (.branch 80 (.branch 79 (.leaf 1251972840) (.leaf 1228555181)) (.branch 81 (.leaf 1205627213) (.leaf 1183176676)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1161191690) (.leaf 1139660744)) (.branch 85 (.leaf 1118572680) (.leaf 1097916680))) (.branch 88 (.branch 87 (.leaf 1077682255) (.leaf 1057859229)) (.branch 89 (.leaf 1038437735) (.leaf 1019408193)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1000761310) (.branch 92 (.leaf 982488064) (.leaf 964579694))) (.branch 95 (.branch 94 (.leaf 947027693) (.leaf 929823799)) (.branch 96 (.leaf 912959985) (.leaf 896428450)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 880221616) (.leaf 864332112)) (.branch 100 (.leaf 848752776) (.leaf 833476641))) (.branch 103 (.branch 102 (.leaf 818496933) (.leaf 803807059)) (.branch 104 (.leaf 789400608) (.leaf 775271339))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 761413179) (.leaf 747820216)) (.branch 108 (.leaf 734486693) (.leaf 721407005))) (.branch 111 (.branch 110 (.leaf 708575692) (.leaf 695987436)) (.branch 112 (.leaf 683637056) (.leaf 671519502)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 659629854) (.leaf 647963316)) (.branch 116 (.leaf 636515212) (.leaf 625280981))) (.branch 119 (.branch 118 (.leaf 614256179) (.leaf 603436468)) (.branch 120 (.leaf 592817619) (.leaf 582395505)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1056).prefactor = (5174136577301751/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1056).cutoff/(generalMeanRows 1056).c)).2 =
    (327972293495017/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1056).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1056).q*(generalMeanRows 1056).c/2-2 = (673/1000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable313.value]
  have hcontinuation : (generalMeanRows 1056).q*(generalMeanRows 1056).cutoff/2-2 = (65/38:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable044.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1056).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1056).criticalRate j.val*(generalMeanRows 1056).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1056).c*(generalMeanRows 1056).criticalPoint j.val)).2-
      (generalMeanRows 1056).J/2-(generalMeanRows 1056).error (generalMeanGrid j.val)+
      (generalMeanRows 1056).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1056).c)).2-
      (generalMeanRows 1056).J/2-(generalMeanRows 1056).error 4 := by
  have he : (generalMeanRows 1056).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1056) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1056)
    (generalMeanRows_prefactorDomain 1056) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1056

/-! Kernel-checked entropy margins for general spectral rectangle 1057. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1057
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6893823966) (.branch 2 (.leaf 6697080747) (.leaf 6507997417))) (.branch 5 (.branch 4 (.leaf 6326171435) (.leaf 6151228012)) (.branch 6 (.leaf 5982817638) (.leaf 5820613903)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5664311534) (.leaf 5513624656)) (.branch 10 (.leaf 5368285223) (.leaf 5228041612))) (.branch 13 (.branch 12 (.leaf 5092657352) (.leaf 4961909977)) (.branch 14 (.leaf 4835589988) (.leaf 4713499909))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4595453423) (.branch 17 (.leaf 4481274597) (.leaf 4370797161))) (.branch 20 (.branch 19 (.leaf 4263863852) (.leaf 4160325820)) (.branch 21 (.leaf 4060042067) (.leaf 3962878948)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3868709697) (.leaf 3777414001)) (.branch 25 (.leaf 3688877596) (.leaf 3602991901))) (.branch 28 (.branch 27 (.leaf 3519653674) (.leaf 3438764699)) (.branch 29 (.leaf 3360231485) (.leaf 3283964997)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3209880399) (.branch 32 (.leaf 3137896817) (.leaf 3067937116))) (.branch 35 (.branch 34 (.leaf 2999927695) (.leaf 2933798292)) (.branch 36 (.leaf 2869481803) (.leaf 2806914112)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2746033936) (.leaf 2686782671)) (.branch 40 (.leaf 2629104256) (.leaf 2572945038))) (.branch 43 (.branch 42 (.leaf 2518253654) (.leaf 2464980911)) (.branch 44 (.leaf 2413079677) (.leaf 2362504780))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2313212911) (.branch 47 (.leaf 2265162532) (.leaf 2218313789))) (.branch 50 (.branch 49 (.leaf 2172628431) (.leaf 2128069735)) (.branch 51 (.leaf 2084602434) (.leaf 2042192644)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2000807802) (.leaf 1960416607)) (.branch 55 (.leaf 1920988957) (.leaf 1882495899))) (.branch 58 (.branch 57 (.leaf 1844909571) (.leaf 1808203159)) (.branch 59 (.leaf 1772350845) (.leaf 1737327765))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1703109969) (.branch 62 (.leaf 1669674374) (.leaf 1636998734))) (.branch 65 (.branch 64 (.leaf 1605061598) (.leaf 1573842279)) (.branch 66 (.leaf 1543320820) (.leaf 1513477964)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1484295121) (.leaf 1455754347)) (.branch 70 (.leaf 1427838308) (.leaf 1400530263))) (.branch 73 (.branch 72 (.leaf 1373814034) (.leaf 1347673985)) (.branch 74 (.leaf 1322095003) (.leaf 1297062469))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1272562246) (.branch 77 (.leaf 1248580657) (.leaf 1225104465))) (.branch 80 (.branch 79 (.leaf 1202120858) (.leaf 1179617432)) (.branch 81 (.leaf 1157582174) (.leaf 1136003448)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1114869979) (.leaf 1094170842)) (.branch 85 (.leaf 1073895446) (.leaf 1054033523))) (.branch 88 (.branch 87 (.leaf 1034575115) (.leaf 1015510563)) (.branch 89 (.leaf 996830496) (.leaf 978525820)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 960587707) (.branch 92 (.leaf 943007589) (.leaf 925777144))) (.branch 95 (.branch 94 (.leaf 908888289) (.leaf 892333174)) (.branch 96 (.leaf 876104169) (.leaf 860193860)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 844595040) (.leaf 829300703)) (.branch 100 (.leaf 814304035) (.leaf 799598408))) (.branch 103 (.branch 102 (.leaf 785177377) (.leaf 771034668)) (.branch 104 (.leaf 757164177) (.leaf 743559962))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 730216239) (.leaf 717127376)) (.branch 108 (.leaf 704287887) (.leaf 691692430))) (.branch 111 (.branch 110 (.leaf 679335800) (.leaf 667212925)) (.branch 112 (.leaf 655318863) (.leaf 643648797)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 632198029) (.leaf 620961982)) (.branch 116 (.leaf 609936190) (.leaf 599116298))) (.branch 119 (.branch 118 (.leaf 588498058) (.leaf 578077325)) (.branch 120 (.leaf 567850056) (.leaf 557812304)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1057).prefactor = (5051498850118719/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1057).cutoff/(generalMeanRows 1057).c)).2 =
    (343026113237427/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1057).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1057).q*(generalMeanRows 1057).cutoff/2-2 = (3140/1767:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable345.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1057).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1057).criticalRate j.val*(generalMeanRows 1057).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1057).c*(generalMeanRows 1057).criticalPoint j.val)).2-
      (generalMeanRows 1057).J/2-(generalMeanRows 1057).error (generalMeanGrid j.val)+
      (generalMeanRows 1057).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1057).c)).2-
      (generalMeanRows 1057).J/2-(generalMeanRows 1057).error 4 := by
  have he : (generalMeanRows 1057).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1057) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1057)
    (generalMeanRows_prefactorDomain 1057) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1057

/-! Kernel-checked entropy margins for general spectral rectangle 1058. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1058
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6631868327) (.branch 2 (.leaf 6427193768) (.leaf 6230664563))) (.branch 5 (.branch 4 (.leaf 6041855026) (.leaf 5860368603)) (.branch 6 (.leaf 5685835297) (.leaf 5517909370)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5356267302) (.leaf 5200605962)) (.branch 10 (.leaf 5050640967) (.leaf 4906105207))) (.branch 13 (.branch 12 (.leaf 4766747517) (.leaf 4632331474)) (.branch 14 (.leaf 4502634309) (.leaf 4377445913))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4256567943) (.branch 17 (.leaf 4139812998) (.leaf 4027003868))) (.branch 20 (.branch 19 (.leaf 3917972849) (.leaf 3812561111)) (.branch 21 (.leaf 3710618121) (.leaf 3612001111)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3516574586) (.leaf 3424209871)) (.branch 25 (.leaf 3334784693) (.leaf 3248182795))) (.branch 28 (.branch 27 (.leaf 3164293573) (.leaf 3083011747)) (.branch 29 (.leaf 3004237049) (.leaf 2927873935)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2853831320) (.branch 32 (.leaf 2782022325) (.leaf 2712364042))) (.branch 35 (.branch 34 (.leaf 2644777324) (.leaf 2579186571)) (.branch 36 (.leaf 2515519550) (.leaf 2453707207)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2393683508) (.leaf 2335385276)) (.branch 40 (.leaf 2278752048) (.leaf 2223725932))) (.branch 43 (.branch 42 (.leaf 2170251484) (.leaf 2118275579)) (.branch 44 (.leaf 2067747297) (.leaf 2018617818))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1970840317) (.branch 47 (.leaf 1924369868) (.leaf 1879163351))) (.branch 50 (.branch 49 (.leaf 1835179370) (.leaf 1792378169)) (.branch 51 (.leaf 1750721555) (.leaf 1710172827)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1670696706) (.leaf 1632259271)) (.branch 55 (.leaf 1594827895) (.leaf 1558371190))) (.branch 58 (.branch 57 (.leaf 1522858948) (.leaf 1488262093)) (.branch 59 (.leaf 1454552625) (.leaf 1421703579))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1389688976) (.branch 62 (.leaf 1358483781) (.leaf 1328063864))) (.branch 65 (.branch 64 (.leaf 1298405960) (.leaf 1269487633)) (.branch 66 (.leaf 1241287240) (.leaf 1213783899)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1186957458) (.leaf 1160788463)) (.branch 70 (.leaf 1135258130) (.leaf 1110348319))) (.branch 73 (.branch 72 (.leaf 1086041506) (.leaf 1062320758)) (.branch 74 (.leaf 1039169714) (.leaf 1016572554))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 994513987) (.branch 77 (.leaf 972979221) (.leaf 951953952))) (.branch 80 (.branch 79 (.leaf 931424338) (.leaf 911376986)) (.branch 81 (.leaf 891798933) (.leaf 872677629)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 854000923) (.leaf 835757045)) (.branch 85 (.leaf 817934598) (.leaf 800522535))) (.branch 88 (.branch 87 (.leaf 783510154) (.leaf 766887081)) (.branch 89 (.leaf 750643260) (.leaf 734768941)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 719254667) (.branch 92 (.leaf 704091268) (.leaf 689269845))) (.branch 95 (.branch 94 (.leaf 674781766) (.leaf 660618652)) (.branch 96 (.leaf 646772371) (.leaf 633235028)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 619998957) (.leaf 607056714)) (.branch 100 (.leaf 594401069) (.leaf 582024997))) (.branch 103 (.branch 102 (.leaf 569921675) (.leaf 558084469)) (.branch 104 (.leaf 546506936) (.leaf 535182809))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 524105998) (.leaf 513270580)) (.branch 108 (.leaf 502670794) (.leaf 492301040))) (.branch 111 (.branch 110 (.leaf 482155867) (.leaf 472229973)) (.branch 112 (.leaf 462518199) (.leaf 453015526)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 443717066) (.leaf 434618062)) (.branch 116 (.leaf 425713883) (.leaf 417000021))) (.branch 119 (.branch 118 (.leaf 408472083) (.leaf 400125794)) (.branch 120 (.leaf 391956987) (.leaf 383961605)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1058).prefactor = (5304191381252729/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1058).cutoff/(generalMeanRows 1058).c)).2 =
    (76015036176011/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1058).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1058).q*(generalMeanRows 1058).c/2-2 = (3147/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable328.value]
  have hcontinuation : (generalMeanRows 1058).q*(generalMeanRows 1058).cutoff/2-2 = (3140/1767:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable345.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1058).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1058).criticalRate j.val*(generalMeanRows 1058).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1058).c*(generalMeanRows 1058).criticalPoint j.val)).2-
      (generalMeanRows 1058).J/2-(generalMeanRows 1058).error (generalMeanGrid j.val)+
      (generalMeanRows 1058).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1058).c)).2-
      (generalMeanRows 1058).J/2-(generalMeanRows 1058).error 4 := by
  have he : (generalMeanRows 1058).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1058) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1058)
    (generalMeanRows_prefactorDomain 1058) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1058

/-! Kernel-checked entropy margins for general spectral rectangle 1059. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1059
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6627006406) (.branch 2 (.leaf 6429957095) (.leaf 6240719412))) (.branch 5 (.branch 4 (.leaf 6058880249) (.leaf 5884054987)) (.branch 6 (.leaf 5715884981) (.leaf 5554035312)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5398192791) (.leaf 5248064172)) (.branch 10 (.leaf 5103374541) (.leaf 4963865875))) (.branch 13 (.branch 12 (.leaf 4829295738) (.leaf 4699436104)) (.branch 14 (.leaf 4574072284) (.leaf 4453001961))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4336034302) (.branch 17 (.leaf 4222989154) (.leaf 4113696308))) (.branch 20 (.branch 19 (.leaf 4007994823) (.leaf 3905732407)) (.branch 21 (.leaf 3806764850) (.leaf 3710955500)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3618174781) (.leaf 3528299748)) (.branch 25 (.leaf 3441213677) (.leaf 3356805680))) (.branch 28 (.branch 27 (.leaf 3274970360) (.leaf 3195607475)) (.branch 29 (.leaf 3118621643) (.leaf 3043922049)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2971422194) (.branch 32 (.leaf 2901039639) (.leaf 2832695783))) (.branch 35 (.branch 34 (.leaf 2766315648) (.leaf 2701827677)) (.branch 36 (.leaf 2639163551) (.leaf 2578258013)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2519048704) (.leaf 2461476009)) (.branch 40 (.leaf 2405482915) (.leaf 2351014875))) (.branch 43 (.branch 42 (.leaf 2298019680) (.leaf 2246447341)) (.branch 44 (.leaf 2196249977) (.leaf 2147381707))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2099798553) (.branch 47 (.leaf 2053458346) (.leaf 2008320635))) (.branch 50 (.branch 49 (.leaf 1964346606) (.leaf 1921499002)) (.branch 51 (.leaf 1879742050) (.leaf 1839041389)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1799364002) (.leaf 1760678158)) (.branch 55 (.leaf 1722953349) (.leaf 1686160234))) (.branch 58 (.branch 57 (.leaf 1650270585) (.leaf 1615257238)) (.branch 59 (.leaf 1581094044) (.leaf 1547755826))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1515218331) (.branch 62 (.leaf 1483458193) (.leaf 1452452893))) (.branch 65 (.branch 64 (.leaf 1422180723) (.leaf 1392620749)) (.branch 66 (.leaf 1363752778) (.leaf 1335557330)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1308015602) (.leaf 1281109445)) (.branch 70 (.leaf 1254821331) (.leaf 1229134334))) (.branch 73 (.branch 72 (.leaf 1204032099) (.leaf 1179498821)) (.branch 74 (.leaf 1155519225) (.leaf 1132078538))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1109162477) (.branch 77 (.leaf 1086757224) (.leaf 1064849408))) (.branch 80 (.branch 79 (.leaf 1043426090) (.leaf 1022474742)) (.branch 81 (.leaf 1001983237) (.leaf 981939827)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 962333133) (.leaf 943152127)) (.branch 85 (.leaf 924386125) (.leaf 906024765))) (.branch 88 (.branch 87 (.leaf 888058005) (.leaf 870476103)) (.branch 89 (.leaf 853269610) (.leaf 836429358)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 819946451) (.branch 92 (.leaf 803812252) (.leaf 788018378))) (.branch 95 (.branch 94 (.leaf 772556689) (.leaf 757419277)) (.branch 96 (.leaf 742598463) (.leaf 728086783)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 713876986) (.leaf 699962024)) (.branch 100 (.leaf 686335043) (.leaf 672989381))) (.branch 103 (.branch 102 (.leaf 659918558) (.leaf 647116271)) (.branch 104 (.leaf 634576389) (.leaf 622292945))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 610260133) (.leaf 598472302)) (.branch 108 (.leaf 586923949) (.leaf 575609717))) (.branch 111 (.branch 110 (.leaf 564524390) (.leaf 553662886)) (.branch 112 (.leaf 543020256) (.leaf 532591677)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 522372450) (.leaf 512357996)) (.branch 116 (.leaf 502543850) (.leaf 492925661))) (.branch 119 (.branch 118 (.leaf 483499186) (.leaf 474260288)) (.branch 120 (.leaf 465204933) (.leaf 456329184)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1059).prefactor = (2581045037769017/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1059).cutoff/(generalMeanRows 1059).c)).2 =
    (170019881447567/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1059).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1059).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1059).criticalRate j.val*(generalMeanRows 1059).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1059).c*(generalMeanRows 1059).criticalPoint j.val)).2-
      (generalMeanRows 1059).J/2-(generalMeanRows 1059).error (generalMeanGrid j.val)+
      (generalMeanRows 1059).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1059).c)).2-
      (generalMeanRows 1059).J/2-(generalMeanRows 1059).error 4 := by
  have he : (generalMeanRows 1059).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1059) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1059)
    (generalMeanRows_prefactorDomain 1059) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1059

/-! Kernel-checked entropy margins for general spectral rectangle 1060. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1060
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6449033264) (.branch 2 (.leaf 6260059043) (.leaf 6078599573))) (.branch 5 (.branch 4 (.leaf 5904252945) (.leaf 5736645147)) (.branch 6 (.leaf 5575427602) (.leaf 5420274974)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5270883211) (.leaf 5126967791)) (.branch 10 (.leaf 4988262148) (.leaf 4854516259))) (.branch 13 (.branch 12 (.leaf 4725495359) (.leaf 4600978791)) (.branch 14 (.leaf 4480758952) (.leaf 4364640342))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4252438694) (.branch 17 (.leaf 4143980183) (.leaf 4039100703))) (.branch 20 (.branch 19 (.leaf 3937645202) (.leaf 3839467072)) (.branch 21 (.leaf 3744427596) (.leaf 3652395424)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3563246110) (.leaf 3476861665)) (.branch 25 (.leaf 3393130156) (.leaf 3311945334))) (.branch 28 (.branch 27 (.leaf 3233206285) (.leaf 3156817106)) (.branch 29 (.leaf 3082686611) (.leaf 3010728052)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2940858857) (.branch 32 (.leaf 2873000395) (.leaf 2807077746))) (.branch 35 (.branch 34 (.leaf 2743019495) (.leaf 2680757537)) (.branch 36 (.leaf 2620226890) (.leaf 2561365530)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2504114223) (.leaf 2448416383)) (.branch 40 (.leaf 2394217925) (.leaf 2341467136))) (.branch 43 (.branch 42 (.leaf 2290114550) (.leaf 2240112832)) (.branch 44 (.leaf 2191416668) (.leaf 2143982661))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2097769238) (.branch 47 (.leaf 2052736551) (.leaf 2008846400))) (.branch 50 (.branch 49 (.leaf 1966062145) (.leaf 1924348632)) (.branch 51 (.leaf 1883672120) (.leaf 1844000216)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1805301804) (.leaf 1767546990)) (.branch 55 (.leaf 1730707043) (.leaf 1694754339))) (.branch 58 (.branch 57 (.leaf 1659662310) (.leaf 1625405396)) (.branch 59 (.leaf 1591958998) (.leaf 1559299435))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1527403903) (.branch 62 (.leaf 1496250431) (.leaf 1465817853))) (.branch 65 (.branch 64 (.leaf 1436085763) (.leaf 1407034486)) (.branch 66 (.leaf 1378645048) (.leaf 1350899139)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1323779094) (.leaf 1297267855)) (.branch 70 (.leaf 1271348953) (.leaf 1246006481))) (.branch 73 (.branch 72 (.leaf 1221225068) (.leaf 1196989859)) (.branch 74 (.leaf 1173286496) (.leaf 1150101090))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1127420211) (.branch 77 (.leaf 1105230865) (.leaf 1083520474))) (.branch 80 (.branch 79 (.leaf 1062276865) (.leaf 1041488250)) (.branch 81 (.leaf 1021143211) (.leaf 1001230689)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 981739966) (.leaf 962660654)) (.branch 85 (.leaf 943982681) (.leaf 925696282))) (.branch 88 (.branch 87 (.leaf 907791983) (.leaf 890260594)) (.branch 89 (.leaf 873093196) (.leaf 856281134)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 839816001) (.branch 92 (.leaf 823689638) (.leaf 807894118))) (.branch 95 (.branch 94 (.leaf 792421739) (.leaf 777265020)) (.branch 96 (.leaf 762416686) (.leaf 747869669)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 733617095) (.leaf 719652279)) (.branch 100 (.leaf 705968718) (.leaf 692560086))) (.branch 103 (.branch 102 (.leaf 679420229) (.leaf 666543154)) (.branch 104 (.leaf 653923031) (.leaf 641554182))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 629431077) (.leaf 617548332)) (.branch 108 (.leaf 605900702) (.leaf 594483076))) (.branch 111 (.branch 110 (.leaf 583290474) (.leaf 572318042)) (.branch 112 (.leaf 561561050) (.leaf 551014886)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 540675051) (.leaf 530537161)) (.branch 116 (.leaf 520596937) (.leaf 510850207))) (.branch 119 (.branch 118 (.leaf 501292899) (.leaf 491921041)) (.branch 120 (.leaf 482730755) (.leaf 473718258)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1060).prefactor = (1005392621033017/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1060).cutoff/(generalMeanRows 1060).c)).2 =
    (72880458304811/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1060).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1060).q*(generalMeanRows 1060).cutoff/2-2 = (1060/551:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable346.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1060).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1060).criticalRate j.val*(generalMeanRows 1060).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1060).c*(generalMeanRows 1060).criticalPoint j.val)).2-
      (generalMeanRows 1060).J/2-(generalMeanRows 1060).error (generalMeanGrid j.val)+
      (generalMeanRows 1060).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1060).c)).2-
      (generalMeanRows 1060).J/2-(generalMeanRows 1060).error 4 := by
  have he : (generalMeanRows 1060).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1060) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1060)
    (generalMeanRows_prefactorDomain 1060) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1060

/-! Kernel-checked entropy margins for general spectral rectangle 1061. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1061
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6249176749) (.branch 2 (.leaf 6053870873) (.leaf 5866483944))) (.branch 5 (.branch 4 (.leaf 5686594234) (.leaf 5513809103)) (.branch 6 (.leaf 5347762442) (.leaf 5188112391)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5034539300) (.leaf 4886743910)) (.branch 10 (.leaf 4744445709) (.leaf 4607381466))) (.branch 13 (.branch 12 (.leaf 4475303893) (.leaf 4347980446)) (.branch 14 (.leaf 4225192230) (.leaf 4106733007))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3992408294) (.branch 17 (.leaf 3882034537) (.leaf 3775438356))) (.branch 20 (.branch 19 (.leaf 3672455855) (.leaf 3572931988)) (.branch 21 (.leaf 3476719976) (.leaf 3383680772)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3293682568) (.leaf 3206600335)) (.branch 25 (.leaf 3122315404) (.leaf 3040715075))) (.branch 28 (.branch 27 (.leaf 2961692257) (.leaf 2885145130)) (.branch 29 (.leaf 2810976834) (.leaf 2739095181)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2669412383) (.branch 32 (.leaf 2601844801) (.leaf 2536312713))) (.branch 35 (.branch 34 (.leaf 2472740092) (.leaf 2411054402)) (.branch 36 (.leaf 2351186409) (.leaf 2293070000)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2236642018) (.leaf 2181842099)) (.branch 40 (.leaf 2128612533) (.leaf 2076898119))) (.branch 43 (.branch 42 (.leaf 2026646037) (.leaf 1977805728)) (.branch 44 (.leaf 1930328776) (.leaf 1884168801))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1839281359) (.branch 47 (.leaf 1795623843) (.leaf 1753155396))) (.branch 50 (.branch 49 (.leaf 1711836822) (.leaf 1671630508)) (.branch 51 (.leaf 1632500347) (.leaf 1594411668)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1557331165) (.leaf 1521226837)) (.branch 55 (.leaf 1486067921) (.leaf 1451824843))) (.branch 58 (.branch 57 (.leaf 1418469155) (.leaf 1385973490)) (.branch 59 (.leaf 1354311511) (.leaf 1323457863))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1293388132) (.branch 62 (.leaf 1264078801) (.leaf 1235507212))) (.branch 65 (.branch 64 (.leaf 1207651528) (.leaf 1180490698)) (.branch 66 (.leaf 1154004421) (.leaf 1128173118)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1102977897) (.leaf 1078400526)) (.branch 70 (.leaf 1054423405) (.leaf 1031029541))) (.branch 73 (.branch 72 (.leaf 1008202522) (.leaf 985926490)) (.branch 74 (.leaf 964186126) (.leaf 942966619))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 922253653) (.branch 77 (.leaf 902033383) (.leaf 882292418))) (.branch 80 (.branch 79 (.leaf 863017803) (.leaf 844197001)) (.branch 81 (.leaf 825817879) (.leaf 807868687)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 790338051) (.leaf 773214953)) (.branch 85 (.leaf 756488720) (.leaf 740149009))) (.branch 88 (.branch 87 (.leaf 724185796) (.leaf 708589366)) (.branch 89 (.leaf 693350298) (.leaf 678459456)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 663907978) (.branch 92 (.leaf 649687269) (.leaf 635788986))) (.branch 95 (.branch 94 (.leaf 622205035) (.leaf 608927556)) (.branch 96 (.leaf 595948921) (.leaf 583261722)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 570858763) (.leaf 558733054)) (.branch 100 (.leaf 546877807) (.leaf 535286421))) (.branch 103 (.branch 102 (.leaf 523952485) (.leaf 512869766)) (.branch 104 (.leaf 502032202) (.leaf 491433901))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 481069133) (.leaf 470932324)) (.branch 108 (.leaf 461018052) (.leaf 451321042))) (.branch 111 (.branch 110 (.leaf 441836159) (.leaf 432558409)) (.branch 112 (.leaf 423482929) (.leaf 414604984)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 405919966) (.leaf 397423387)) (.branch 116 (.leaf 389110876) (.leaf 380978176))) (.branch 119 (.branch 118 (.leaf 373021140) (.leaf 365235729)) (.branch 120 (.leaf 357618005) (.leaf 350164133)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1061).prefactor = (5241519206417281/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1061).cutoff/(generalMeanRows 1061).c)).2 =
    (16662356187213/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1061).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1061).q*(generalMeanRows 1061).cutoff/2-2 = (1060/551:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable346.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1061).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1061).criticalRate j.val*(generalMeanRows 1061).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1061).c*(generalMeanRows 1061).criticalPoint j.val)).2-
      (generalMeanRows 1061).J/2-(generalMeanRows 1061).error (generalMeanGrid j.val)+
      (generalMeanRows 1061).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1061).c)).2-
      (generalMeanRows 1061).J/2-(generalMeanRows 1061).error 4 := by
  have he : (generalMeanRows 1061).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1061) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1061)
    (generalMeanRows_prefactorDomain 1061) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1061

/-! Kernel-checked entropy margins for general spectral rectangle 1062. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1062
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6209188302) (.branch 2 (.leaf 6021786500) (.leaf 5841950630))) (.branch 5 (.branch 4 (.leaf 5669272735) (.leaf 5503373268)) (.branch 6 (.leaf 5343898588) (.leaf 5190518730)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5042925415) (.leaf 4900830263)) (.branch 10 (.leaf 4763963193) (.leaf 4632070978))) (.branch 13 (.branch 12 (.leaf 4504915942) (.leaf 4382274776)) (.branch 14 (.leaf 4263937475) (.leaf 4149706357))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4039395183) (.branch 17 (.leaf 3932828342) (.leaf 3829840116))) (.branch 20 (.branch 19 (.leaf 3730274000) (.leaf 3633982080)) (.branch 21 (.leaf 3540824464) (.leaf 3450668754)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3363389559) (.leaf 3278868054)) (.branch 25 (.leaf 3196991563) (.leaf 3117653174))) (.branch 28 (.branch 27 (.leaf 3040751389) (.leaf 2966189796)) (.branch 29 (.leaf 2893876758) (.leaf 2823725136)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2755652021) (.branch 32 (.leaf 2689578489) (.leaf 2625429374))) (.branch 35 (.branch 34 (.leaf 2563133054) (.leaf 2502621247)) (.branch 36 (.leaf 2443828831) (.leaf 2386693666)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2331156432) (.leaf 2277160474)) (.branch 40 (.leaf 2224651661) (.leaf 2173578254))) (.branch 43 (.branch 42 (.leaf 2123890772) (.leaf 2075541882)) (.branch 44 (.leaf 2028486284) (.leaf 1982680606))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1938083306) (.branch 47 (.leaf 1894654579) (.leaf 1852356272))) (.branch 50 (.branch 49 (.leaf 1811151800) (.leaf 1771006067)) (.branch 51 (.leaf 1731885395) (.leaf 1693757456)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1656591204) (.leaf 1620356816)) (.branch 55 (.leaf 1585025631) (.leaf 1550570099))) (.branch 58 (.branch 57 (.leaf 1516963725) (.leaf 1484181022)) (.branch 59 (.leaf 1452197467) (.leaf 1420989450))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1390534239) (.branch 62 (.leaf 1360809937) (.leaf 1331795447))) (.branch 65 (.branch 64 (.leaf 1303470433) (.leaf 1275815289)) (.branch 66 (.leaf 1248811105) (.leaf 1222439641)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1196683292) (.leaf 1171525065)) (.branch 70 (.leaf 1146948551) (.leaf 1122937903))) (.branch 73 (.branch 72 (.leaf 1099477807) (.leaf 1076553466)) (.branch 74 (.leaf 1054150574) (.leaf 1032255299))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1010854262) (.branch 77 (.leaf 989934519) (.leaf 969483542))) (.branch 80 (.branch 79 (.leaf 949489205) (.leaf 929939769)) (.branch 81 (.leaf 910823861) (.leaf 892130466)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 873848911) (.leaf 855968849)) (.branch 85 (.leaf 838480252) (.leaf 821373395))) (.branch 88 (.branch 87 (.leaf 804638844) (.leaf 788267449)) (.branch 89 (.leaf 772250331) (.leaf 756578871)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 741244703) (.branch 92 (.leaf 726239703) (.leaf 711555981))) (.branch 95 (.branch 94 (.leaf 697185874) (.leaf 683121935)) (.branch 96 (.leaf 669356928) (.leaf 655883819)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 642695770) (.leaf 629786132)) (.branch 100 (.leaf 617148439) (.leaf 604776400))) (.branch 103 (.branch 102 (.leaf 592663897) (.leaf 580804973)) (.branch 104 (.leaf 569193834) (.leaf 557824838))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 546692493) (.leaf 535791450)) (.branch 108 (.leaf 525116501) (.leaf 514662573))) (.branch 111 (.branch 110 (.leaf 504424722) (.leaf 494398135)) (.branch 112 (.leaf 484578116) (.leaf 474960094)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 465539608) (.leaf 456312313)) (.branch 116 (.leaf 447273971) (.leaf 438420449))) (.branch 119 (.branch 118 (.leaf 429747715) (.leaf 421251839)) (.branch 120 (.leaf 412928983) (.leaf 404775407)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1062).prefactor = (2545512689266917/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1062).cutoff/(generalMeanRows 1062).c)).2 =
    (36833844355553/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1062).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1062).q*(generalMeanRows 1062).cutoff/2-2 = (800/399:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable347.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1062).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1062).criticalRate j.val*(generalMeanRows 1062).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1062).c*(generalMeanRows 1062).criticalPoint j.val)).2-
      (generalMeanRows 1062).J/2-(generalMeanRows 1062).error (generalMeanGrid j.val)+
      (generalMeanRows 1062).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1062).c)).2-
      (generalMeanRows 1062).J/2-(generalMeanRows 1062).error 4 := by
  have he : (generalMeanRows 1062).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1062) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1062)
    (generalMeanRows_prefactorDomain 1062) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1062

/-! Kernel-checked entropy margins for general spectral rectangle 1063. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1063
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5914499369) (.branch 2 (.leaf 5722230083) (.leaf 5537921014))) (.branch 5 (.branch 4 (.leaf 5361144434) (.leaf 5191502179)) (.branch 6 (.leaf 5028623052) (.leaf 4872160515)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4721790618) (.leaf 4577210151)) (.branch 10 (.leaf 4438134981) (.leaf 4304298552))) (.branch 13 (.branch 12 (.leaf 4175450534) (.leaf 4051355598)) (.branch 14 (.leaf 3931792303) (.leaf 3816552087))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3705438346) (.branch 17 (.leaf 3598265593) (.leaf 3494858691))) (.branch 20 (.branch 19 (.leaf 3395052146) (.leaf 3298689464)) (.branch 21 (.leaf 3205622555) (.leaf 3115711185)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3028822477) (.leaf 2944830439)) (.branch 25 (.leaf 2863615538) (.leaf 2785064302))) (.branch 28 (.branch 27 (.leaf 2709068948) (.leaf 2635527045)) (.branch 29 (.leaf 2564341190) (.leaf 2495418715)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2428671415) (.branch 32 (.leaf 2364015287) (.leaf 2301370293))) (.branch 35 (.branch 34 (.leaf 2240660137) (.leaf 2181812058)) (.branch 36 (.leaf 2124756632) (.leaf 2069427593)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2015761660) (.leaf 1963698379)) (.branch 40 (.leaf 1913179972) (.leaf 1864151196))) (.branch 43 (.branch 42 (.leaf 1816559211) (.leaf 1770353458)) (.branch 44 (.leaf 1725485538) (.leaf 1681909107))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1639579769) (.branch 47 (.leaf 1598454980) (.leaf 1558493957))) (.branch 50 (.branch 49 (.leaf 1519657590) (.leaf 1481908363)) (.branch 51 (.leaf 1445210273) (.leaf 1409528760)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1374830639) (.leaf 1341084033)) (.branch 55 (.leaf 1308258313) (.leaf 1276324039))) (.branch 58 (.branch 57 (.leaf 1245252905) (.leaf 1215017690)) (.branch 59 (.leaf 1185592203) (.leaf 1156951242))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1129070546) (.branch 62 (.leaf 1101926755) (.leaf 1075497369))) (.branch 65 (.branch 64 (.leaf 1049760711) (.leaf 1024695891)) (.branch 66 (.leaf 1000282771) (.leaf 976501934)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 953334654) (.leaf 930762863)) (.branch 70 (.leaf 908769128) (.leaf 887336620))) (.branch 73 (.branch 72 (.leaf 866449092) (.leaf 846090856)) (.branch 74 (.leaf 826246755) (.leaf 806902147))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 788042881) (.branch 77 (.leaf 769655279) (.leaf 751726114))) (.branch 80 (.branch 79 (.leaf 734242598) (.leaf 717192359)) (.branch 81 (.leaf 700563426) (.leaf 684344218)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 668523522) (.leaf 653090485)) (.branch 85 (.leaf 638034597) (.leaf 623345676))) (.branch 88 (.branch 87 (.leaf 609013864) (.leaf 595029604)) (.branch 89 (.leaf 581383639) (.leaf 568066993)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 555070965) (.branch 92 (.leaf 542387119) (.leaf 530007272))) (.branch 95 (.branch 94 (.leaf 517923489) (.leaf 506128069)) (.branch 96 (.leaf 494613540) (.leaf 483372654)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 472398370) (.leaf 461683856)) (.branch 100 (.leaf 451222478) (.leaf 441007792))) (.branch 103 (.branch 102 (.leaf 431033542) (.leaf 421293647)) (.branch 104 (.leaf 411782202) (.leaf 402493467))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 393421865) (.leaf 384561974)) (.branch 108 (.leaf 375908524) (.leaf 367456390))) (.branch 111 (.branch 110 (.leaf 359200591) (.leaf 351136280)) (.branch 112 (.leaf 343258743) (.leaf 335563398)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 328045781) (.leaf 320701555)) (.branch 116 (.leaf 313526495) (.leaf 306516491))) (.branch 119 (.branch 118 (.leaf 299667543) (.leaf 292975755)) (.branch 120 (.leaf 286437336) (.leaf 280048596)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1063).prefactor = (5292830785529023/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1063).cutoff/(generalMeanRows 1063).c)).2 =
    (332189929439219/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1063).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1063).q*(generalMeanRows 1063).cutoff/2-2 = (800/399:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable347.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1063).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1063).criticalRate j.val*(generalMeanRows 1063).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1063).c*(generalMeanRows 1063).criticalPoint j.val)).2-
      (generalMeanRows 1063).J/2-(generalMeanRows 1063).error (generalMeanGrid j.val)+
      (generalMeanRows 1063).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1063).c)).2-
      (generalMeanRows 1063).J/2-(generalMeanRows 1063).error 4 := by
  have he : (generalMeanRows 1063).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1063) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1063)
    (generalMeanRows_prefactorDomain 1063) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1063

/-! Kernel-checked entropy margins for general spectral rectangle 1064. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1064
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6003078722) (.branch 2 (.leaf 5818219727) (.leaf 5640918702))) (.branch 5 (.branch 4 (.leaf 5470764295) (.leaf 5307373941)) (.branch 6 (.leaf 5150391334) (.leaf 4999484166)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4854342108) (.leaf 4714675002)) (.branch 10 (.leaf 4580211232) (.leaf 4450696261))) (.branch 13 (.branch 12 (.leaf 4325891308) (.leaf 4205572146)) (.branch 14 (.leaf 4089528016) (.leaf 3977560640))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3869483313) (.branch 17 (.leaf 3765120090) (.leaf 3664305025))) (.branch 20 (.branch 19 (.leaf 3566881487) (.leaf 3472701525)) (.branch 21 (.leaf 3381625289) (.leaf 3293520494)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3208261927) (.leaf 3125730991)) (.branch 25 (.leaf 3045815290) (.leaf 2968408234))) (.branch 28 (.branch 27 (.leaf 2893408682) (.leaf 2820720610)) (.branch 29 (.leaf 2750252797) (.leaf 2681918539)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2615635383) (.branch 32 (.leaf 2551324877) (.leaf 2488912335))) (.branch 35 (.branch 34 (.leaf 2428326623) (.leaf 2369499959)) (.branch 36 (.leaf 2312367719) (.leaf 2256868265)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2202942778) (.leaf 2150535103)) (.branch 40 (.leaf 2099591607) (.leaf 2050061040))) (.branch 43 (.branch 42 (.leaf 2001894411) (.leaf 1955044864)) (.branch 44 (.leaf 1909467573) (.leaf 1865119628))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1821959945) (.branch 47 (.leaf 1779949163) (.leaf 1739049567))) (.branch 50 (.branch 49 (.leaf 1699224996) (.leaf 1660440771)) (.branch 51 (.leaf 1622663620) (.leaf 1585861608)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1550004073) (.leaf 1515061565)) (.branch 55 (.leaf 1481005786) (.leaf 1447809535))) (.branch 58 (.branch 57 (.leaf 1415446659) (.leaf 1383892003)) (.branch 59 (.leaf 1353121358) (.leaf 1323111428))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1293839778) (.branch 62 (.leaf 1265284800) (.leaf 1237425675))) (.branch 65 (.branch 64 (.leaf 1210242338) (.leaf 1183715443)) (.branch 66 (.leaf 1157826333) (.leaf 1132557007)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1107890097) (.leaf 1083808834)) (.branch 70 (.leaf 1060297027) (.leaf 1037339038))) (.branch 73 (.branch 72 (.leaf 1014919756) (.leaf 993024579)) (.branch 74 (.leaf 971639389) (.leaf 950750536))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 930344813) (.branch 77 (.leaf 910409446) (.leaf 890932070))) (.branch 80 (.branch 79 (.leaf 871900716) (.leaf 853303794)) (.branch 81 (.leaf 835130079) (.leaf 817368695)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 800009105) (.leaf 783041095)) (.branch 85 (.leaf 766454762) (.leaf 750240503))) (.branch 88 (.branch 87 (.leaf 734389005) (.leaf 718891230)) (.branch 89 (.leaf 703738411) (.leaf 688922037)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 674433845) (.branch 92 (.leaf 660265813) (.leaf 646410149))) (.branch 95 (.branch 94 (.leaf 632859284) (.leaf 619605864)) (.branch 96 (.leaf 606642743) (.leaf 593962974)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 581559805) (.leaf 569426670)) (.branch 100 (.leaf 557557182) (.leaf 545945132))) (.branch 103 (.branch 102 (.leaf 534584476) (.leaf 523469336)) (.branch 104 (.leaf 512593988) (.leaf 501952865))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 491540545) (.leaf 481351748)) (.branch 108 (.leaf 471381335) (.leaf 461624300))) (.branch 111 (.branch 110 (.leaf 452075765) (.leaf 442730981)) (.branch 112 (.leaf 433585317) (.leaf 424634263)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 415873423) (.leaf 407298511)) (.branch 116 (.leaf 398905350) (.leaf 390689867))) (.branch 119 (.branch 118 (.leaf 382648089) (.leaf 374776144)) (.branch 120 (.leaf 367070253) (.leaf 359526733)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1064).prefactor = (2564757930271951/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1064).cutoff/(generalMeanRows 1064).c)).2 =
    (188736468634023/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1064).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1064).q*(generalMeanRows 1064).cutoff/2-2 = (3220/1539:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable348.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1064).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1064).criticalRate j.val*(generalMeanRows 1064).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1064).c*(generalMeanRows 1064).criticalPoint j.val)).2-
      (generalMeanRows 1064).J/2-(generalMeanRows 1064).error (generalMeanGrid j.val)+
      (generalMeanRows 1064).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1064).c)).2-
      (generalMeanRows 1064).J/2-(generalMeanRows 1064).error 4 := by
  have he : (generalMeanRows 1064).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1064) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1064)
    (generalMeanRows_prefactorDomain 1064) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1064

/-! Kernel-checked entropy margins for general spectral rectangle 1065. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1065
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5786629388) (.branch 2 (.leaf 5597211721) (.leaf 5415708380))) (.branch 5 (.branch 4 (.leaf 5241689676) (.leaf 5074755803)) (.branch 6 (.leaf 4914534216) (.leaf 4760677296)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4612860261) (.leaf 4470779289)) (.branch 10 (.leaf 4334149838) (.leaf 4202705131))) (.branch 13 (.branch 12 (.leaf 4076194777) (.leaf 3954383540)) (.branch 14 (.leaf 3837050201) (.leaf 3723986545))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3614996418) (.branch 17 (.leaf 3509894878) (.leaf 3408507416))) (.branch 20 (.branch 19 (.leaf 3310669239) (.leaf 3216224619)) (.branch 21 (.leaf 3125026284) (.leaf 3036934866)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2951818394) (.leaf 2869551814)) (.branch 25 (.leaf 2790016560) (.leaf 2713100146))) (.branch 28 (.branch 27 (.leaf 2638695792) (.leaf 2566702082)) (.branch 29 (.leaf 2497022636) (.leaf 2429565814)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2364244437) (.branch 32 (.leaf 2300975529) (.leaf 2239680072))) (.branch 35 (.branch 34 (.leaf 2180282785) (.leaf 2122711909)) (.branch 36 (.leaf 2066899014) (.leaf 2012778814)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1960288994) (.leaf 1909370049)) (.branch 40 (.leaf 1859965136) (.leaf 1812019926))) (.branch 43 (.branch 42 (.leaf 1765482479) (.leaf 1720303113)) (.branch 44 (.leaf 1676434290) (.leaf 1633830504))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1592448178) (.branch 47 (.leaf 1552245568) (.leaf 1513182668))) (.branch 50 (.branch 49 (.leaf 1475221128) (.leaf 1438324166)) (.branch 51 (.leaf 1402456497) (.leaf 1367584258)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1333674939) (.leaf 1300697319)) (.branch 55 (.leaf 1268621405) (.leaf 1237418373))) (.branch 58 (.branch 57 (.leaf 1207060516) (.leaf 1177521189)) (.branch 59 (.leaf 1148774762) (.leaf 1120796575))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1093562890) (.branch 62 (.leaf 1067050853) (.leaf 1041238453))) (.branch 65 (.branch 64 (.leaf 1016104487) (.leaf 991628521)) (.branch 66 (.leaf 967790857) (.leaf 944572505)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 921955146) (.leaf 899921111)) (.branch 70 (.leaf 878453346) (.leaf 857535393))) (.branch 73 (.branch 72 (.leaf 837151358) (.leaf 817285894)) (.branch 74 (.leaf 797924176) (.leaf 779051877))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 760655153) (.branch 77 (.leaf 742720619) (.leaf 725235334))) (.branch 80 (.branch 79 (.leaf 708186781) (.leaf 691562851)) (.branch 81 (.leaf 675351828) (.leaf 659542372)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 644123506) (.leaf 629084602)) (.branch 85 (.leaf 614415367) (.leaf 600105830))) (.branch 88 (.branch 87 (.leaf 586146331) (.leaf 572527511)) (.branch 89 (.leaf 559240295) (.leaf 546275888)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 533625763) (.branch 92 (.leaf 521281649) (.leaf 509235524))) (.branch 95 (.branch 94 (.leaf 497479605) (.leaf 486006341)) (.branch 96 (.leaf 474808404) (.leaf 463878680)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 453210264) (.leaf 442796450)) (.branch 100 (.leaf 432630727) (.leaf 422706770))) (.branch 103 (.branch 102 (.leaf 413018437) (.leaf 403559758)) (.branch 104 (.leaf 394324932) (.leaf 385308324))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 376504454) (.leaf 367907997)) (.branch 108 (.leaf 359513773) (.leaf 351316749))) (.branch 111 (.branch 110 (.leaf 343312026) (.leaf 335494842)) (.branch 112 (.leaf 327860565) (.leaf 320404686)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 313122821) (.leaf 306010701)) (.branch 116 (.leaf 299064174) (.leaf 292279197))) (.branch 119 (.branch 118 (.leaf 285651836) (.leaf 279178259)) (.branch 120 (.leaf 272854736) (.leaf 266677637)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1065).prefactor = (5318874885607827/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1065).cutoff/(generalMeanRows 1065).c)).2 =
    (348059052061753/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1065).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1065).q*(generalMeanRows 1065).cutoff/2-2 = (3220/1539:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable348.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1065).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1065).criticalRate j.val*(generalMeanRows 1065).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1065).c*(generalMeanRows 1065).criticalPoint j.val)).2-
      (generalMeanRows 1065).J/2-(generalMeanRows 1065).error (generalMeanGrid j.val)+
      (generalMeanRows 1065).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1065).c)).2-
      (generalMeanRows 1065).J/2-(generalMeanRows 1065).error 4 := by
  have he : (generalMeanRows 1065).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1065) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1065)
    (generalMeanRows_prefactorDomain 1065) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1065

/-! Kernel-checked entropy margins for general spectral rectangle 1066. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1066
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5918943910) (.branch 2 (.leaf 5736958463) (.leaf 5562452285))) (.branch 5 (.branch 4 (.leaf 5395013838) (.leaf 5234260627)) (.branch 6 (.leaf 5079836642) (.leaf 4931410076)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4788671281) (.leaf 4651330946)) (.branch 10 (.leaf 4519118446) (.leaf 4391780358))) (.branch 13 (.branch 12 (.leaf 4269079128) (.leaf 4150791850)) (.branch 14 (.leaf 4036709168) (.leaf 3926634276))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3820381999) (.branch 17 (.leaf 3717777968) (.leaf 3618657850))) (.branch 20 (.branch 19 (.leaf 3522866657) (.leaf 3430258101)) (.branch 21 (.leaf 3340694007) (.leaf 3254043773)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3170183870) (.leaf 3088997384)) (.branch 25 (.leaf 3010373586) (.leaf 2934207547))) (.branch 28 (.branch 27 (.leaf 2860399768) (.leaf 2788855844)) (.branch 29 (.leaf 2719486155) (.leaf 2652205572)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2586933185) (.branch 32 (.leaf 2523592061) (.leaf 2462108999))) (.branch 35 (.branch 34 (.leaf 2402414321) (.leaf 2344441663)) (.branch 36 (.leaf 2288127790) (.leaf 2233412414)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2180238032) (.leaf 2128549773)) (.branch 40 (.leaf 2078295246) (.leaf 2029424412))) (.branch 43 (.branch 42 (.leaf 1981889452) (.leaf 1935644648)) (.branch 44 (.leaf 1890646276) (.leaf 1846852494))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1804223248) (.branch 47 (.leaf 1762720177) (.leaf 1722306529))) (.branch 50 (.branch 49 (.leaf 1682947074) (.leaf 1644608031)) (.branch 51 (.leaf 1607256996) (.leaf 1570862867)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1535395787) (.leaf 1500827081)) (.branch 55 (.leaf 1467129194) (.leaf 1434275645))) (.branch 58 (.branch 57 (.leaf 1402240969) (.leaf 1371000670)) (.branch 59 (.leaf 1340531180) (.leaf 1310809810))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1281814712) (.branch 62 (.leaf 1253524840) (.leaf 1225919913))) (.branch 65 (.branch 64 (.leaf 1198980384) (.leaf 1172687399)) (.branch 66 (.leaf 1147022776) (.leaf 1121968968)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1097509040) (.leaf 1073626637)) (.branch 70 (.leaf 1050305966) (.leaf 1027531767))) (.branch 73 (.branch 72 (.leaf 1005289292) (.leaf 983564284)) (.branch 74 (.leaf 962342955) (.leaf 941611970))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 921358423) (.branch 77 (.leaf 901569826) (.leaf 882234086))) (.branch 80 (.branch 79 (.leaf 863339495) (.leaf 844874712)) (.branch 81 (.leaf 826828745) (.leaf 809190945)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 791950988) (.leaf 775098862)) (.branch 85 (.leaf 758624858) (.leaf 742519556))) (.branch 88 (.branch 87 (.leaf 726773818) (.leaf 711378771)) (.branch 89 (.leaf 696325805) (.leaf 681606558)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 667212909) (.branch 92 (.leaf 653136969) (.leaf 639371073))) (.branch 95 (.branch 94 (.leaf 625907774) (.leaf 612739830)) (.branch 96 (.leaf 599860203) (.leaf 587262049)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 574938712) (.leaf 562883717)) (.branch 100 (.leaf 551090764) (.leaf 539553723))) (.branch 103 (.branch 102 (.leaf 528266629) (.leaf 517223675)) (.branch 104 (.leaf 506419208) (.leaf 495847722))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 485503857) (.leaf 475382391)) (.branch 108 (.leaf 465478238) (.leaf 455786442))) (.branch 111 (.branch 110 (.leaf 446302173) (.leaf 437020726)) (.branch 112 (.leaf 427937513) (.leaf 419048064)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 410348017) (.leaf 401833124)) (.branch 116 (.leaf 393499238) (.leaf 385342316))) (.branch 119 (.branch 118 (.leaf 377358416) (.leaf 369543690)) (.branch 120 (.leaf 361894386) (.leaf 354406841)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1066).prefactor = (5145045905700011/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1066).cutoff/(generalMeanRows 1066).c)).2 =
    (198730659896221/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1066).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1066).q*(generalMeanRows 1066).c/2-2 = (3253/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable349.value]
  have hcontinuation : (generalMeanRows 1066).q*(generalMeanRows 1066).cutoff/2-2 = (540/247:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable350.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1066).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1066).criticalRate j.val*(generalMeanRows 1066).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1066).c*(generalMeanRows 1066).criticalPoint j.val)).2-
      (generalMeanRows 1066).J/2-(generalMeanRows 1066).error (generalMeanGrid j.val)+
      (generalMeanRows 1066).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1066).c)).2-
      (generalMeanRows 1066).J/2-(generalMeanRows 1066).error 4 := by
  have he : (generalMeanRows 1066).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1066) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1066)
    (generalMeanRows_prefactorDomain 1066) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1066

/-! Kernel-checked entropy margins for general spectral rectangle 1067. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1067
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6122891597) (.branch 2 (.leaf 5934635520) (.leaf 5754116423))) (.branch 5 (.branch 4 (.leaf 5580908587) (.leaf 5414616340)) (.branch 6 (.leaf 5254871404) (.leaf 5101330537)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4953673425) (.leaf 4811600786)) (.branch 10 (.leaf 4674832670) (.leaf 4543106923))) (.branch 13 (.branch 12 (.leaf 4416177805) (.leaf 4293814729)) (.branch 14 (.leaf 4175801127) (.leaf 4061933409))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3952020022) (.branch 17 (.leaf 3845880588) (.leaf 3743345111))) (.branch 20 (.branch 19 (.leaf 3644253263) (.leaf 3548453715)) (.branch 21 (.leaf 3455803531) (.leaf 3366167610)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3279418166) (.leaf 3195434255)) (.branch 25 (.leaf 3114101336) (.leaf 3035310861))) (.branch 28 (.branch 27 (.leaf 2958959904) (.leaf 2884950808)) (.branch 29 (.leaf 2813190864) (.leaf 2743592008)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2676070547) (.branch 32 (.leaf 2610546892) (.leaf 2546945322))) (.branch 35 (.branch 34 (.leaf 2485193758) (.leaf 2425223550)) (.branch 36 (.leaf 2366969282) (.leaf 2310368591)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2255361992) (.leaf 2201892723)) (.branch 40 (.leaf 2149906587) (.leaf 2099351822))) (.branch 43 (.branch 42 (.leaf 2050178960) (.leaf 2002340710)) (.branch 44 (.leaf 1955791840) (.leaf 1910489065))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1866390953) (.branch 47 (.leaf 1823457820) (.leaf 1781651648))) (.branch 50 (.branch 49 (.leaf 1740935994) (.leaf 1701275912)) (.branch 51 (.leaf 1662637880) (.leaf 1624989727)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1588300566) (.leaf 1552540734)) (.branch 55 (.leaf 1517681727) (.leaf 1483696151))) (.branch 58 (.branch 57 (.leaf 1450557663) (.leaf 1418240925)) (.branch 59 (.leaf 1386721555) (.leaf 1355976082))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1325981906) (.branch 62 (.leaf 1296717256) (.leaf 1268161154))) (.branch 65 (.branch 64 (.leaf 1240293375) (.leaf 1213094419)) (.branch 66 (.leaf 1186545476) (.leaf 1160628395)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1135325656) (.leaf 1110620343)) (.branch 70 (.leaf 1086496117) (.leaf 1062937193))) (.branch 73 (.branch 72 (.leaf 1039928314) (.leaf 1017454732)) (.branch 74 (.leaf 995502185) (.leaf 974056877))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 953105458) (.branch 77 (.leaf 932635009) (.leaf 912633023))) (.branch 80 (.branch 79 (.leaf 893087386) (.leaf 873986365)) (.branch 81 (.leaf 855318593) (.leaf 837073051)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 819239061) (.leaf 801806265)) (.branch 85 (.leaf 784764620) (.leaf 768104382))) (.branch 88 (.branch 87 (.leaf 751816096) (.leaf 735890586)) (.branch 89 (.leaf 720318943) (.leaf 705092518)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 690202910) (.branch 92 (.leaf 675641959) (.leaf 661401735))) (.branch 95 (.branch 94 (.leaf 647474534) (.leaf 633852865)) (.branch 96 (.leaf 620529448) (.leaf 607497203)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 594749243) (.leaf 582278871)) (.branch 100 (.leaf 570079571) (.leaf 558145001))) (.branch 103 (.branch 102 (.leaf 546468991) (.leaf 535045533)) (.branch 104 (.leaf 523868778) (.leaf 512933033))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 502232752) (.leaf 491762533)) (.branch 108 (.leaf 481517114) (.leaf 471491370))) (.branch 111 (.branch 110 (.leaf 461680304) (.leaf 452079048)) (.branch 112 (.leaf 442682858) (.leaf 433487106)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 424487285) (.leaf 415678995)) (.branch 116 (.leaf 407057950) (.leaf 398619968))) (.branch 119 (.branch 118 (.leaf 390360968) (.leaf 382276972)) (.branch 120 (.leaf 374364097) (.leaf 366618556)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1067).prefactor = (665290946000257/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1067).cutoff/(generalMeanRows 1067).c)).2 =
    (198730659896221/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1067).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1067).q*(generalMeanRows 1067).c/2-2 = (3253/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable349.value]
  have hcontinuation : (generalMeanRows 1067).q*(generalMeanRows 1067).cutoff/2-2 = (540/247:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable350.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1067).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1067).criticalRate j.val*(generalMeanRows 1067).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1067).c*(generalMeanRows 1067).criticalPoint j.val)).2-
      (generalMeanRows 1067).J/2-(generalMeanRows 1067).error (generalMeanGrid j.val)+
      (generalMeanRows 1067).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1067).c)).2-
      (generalMeanRows 1067).J/2-(generalMeanRows 1067).error 4 := by
  have he : (generalMeanRows 1067).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1067) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1067)
    (generalMeanRows_prefactorDomain 1067) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1067

/-! Kernel-checked entropy margins for general spectral rectangle 1068. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1068
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6428147741) (.branch 2 (.leaf 6233028119) (.leaf 6045894157))) (.branch 5 (.branch 4 (.leaf 5866306074) (.leaf 5693855170)) (.branch 6 (.leaf 5528161081) (.leaf 5368869339)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5215649189) (.leaf 5068191627)) (.branch 10 (.leaf 4926207638) (.leaf 4789426615))) (.branch 13 (.branch 12 (.leaf 4657594916) (.leaf 4530474569)) (.branch 14 (.leaf 4407842095) (.leaf 4289487429))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4175212952) (.branch 17 (.leaf 4064832589) (.leaf 3958171002))) (.branch 20 (.branch 19 (.leaf 3855062837) (.leaf 3755352042)) (.branch 21 (.leaf 3658891237) (.leaf 3565541134)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3475170003) (.leaf 3387653180)) (.branch 25 (.leaf 3302872614) (.leaf 3220716444))) (.branch 28 (.branch 27 (.leaf 3141078612) (.leaf 3063858500)) (.branch 29 (.leaf 2988960600) (.leaf 2916294196)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2845773084) (.branch 32 (.leaf 2777315295) (.leaf 2710842853))) (.branch 35 (.branch 34 (.leaf 2646281535) (.leaf 2583560657)) (.branch 36 (.leaf 2522612874) (.leaf 2463373984)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2405782756) (.leaf 2349780763)) (.branch 40 (.leaf 2295312229) (.leaf 2242323880))) (.branch 43 (.branch 42 (.leaf 2190764809) (.leaf 2140586354)) (.branch 44 (.leaf 2091741971) (.leaf 2044187124))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1997879184) (.branch 47 (.leaf 1952777325) (.leaf 1908842431))) (.branch 50 (.branch 49 (.leaf 1866037012) (.leaf 1824325117)) (.branch 51 (.leaf 1783672262) (.leaf 1744045352)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1705412613) (.leaf 1667743529)) (.branch 55 (.leaf 1631008780) (.leaf 1595180183))) (.branch 58 (.branch 57 (.leaf 1560230639) (.leaf 1526134080)) (.branch 59 (.leaf 1492865423) (.leaf 1460400521))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1428716119) (.branch 62 (.leaf 1397789817) (.leaf 1367600027))) (.branch 65 (.branch 64 (.leaf 1338125939) (.leaf 1309347485)) (.branch 66 (.leaf 1281245304) (.leaf 1253800713)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1226995679) (.leaf 1200812785)) (.branch 70 (.leaf 1175235210) (.leaf 1150246700))) (.branch 73 (.branch 72 (.leaf 1125831543) (.leaf 1101974548)) (.branch 74 (.leaf 1078661026) (.leaf 1055876761))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1033608001) (.branch 77 (.leaf 1011841431) (.leaf 990564159))) (.branch 80 (.branch 79 (.leaf 969763699) (.leaf 949427953)) (.branch 81 (.leaf 929545200) (.leaf 910104075)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 891093561) (.leaf 872502974)) (.branch 85 (.leaf 854321947) (.leaf 836540423))) (.branch 88 (.branch 87 (.leaf 819148641) (.leaf 802137125)) (.branch 89 (.leaf 785496675) (.leaf 769218353)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 753293479) (.branch 92 (.leaf 737713619) (.leaf 722470576))) (.branch 95 (.branch 94 (.leaf 707556381) (.leaf 692963288)) (.branch 96 (.leaf 678683764) (.leaf 664710482)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 651036313) (.leaf 637654323)) (.branch 100 (.leaf 624557763) (.leaf 611740063))) (.branch 103 (.branch 102 (.leaf 599194828) (.leaf 586915831)) (.branch 104 (.leaf 574897009) (.leaf 563132454))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 551616413) (.leaf 540343281)) (.branch 108 (.leaf 529307595) (.leaf 518504031))) (.branch 111 (.branch 110 (.leaf 507927401) (.leaf 497572645)) (.branch 112 (.leaf 487434832) (.leaf 477509151)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 467790912) (.leaf 458275540)) (.branch 116 (.leaf 448958573) (.leaf 439835656))) (.branch 119 (.branch 118 (.leaf 430902540) (.leaf 422155080)) (.branch 120 (.leaf 413589230) (.leaf 405201041)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1068).prefactor = (550571778372901/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1068).cutoff/(generalMeanRows 1068).c)).2 =
    (403343689695511/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1068).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1068).q*(generalMeanRows 1068).c/2-2 = (3187/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable351.value]
  have hcontinuation : (generalMeanRows 1068).q*(generalMeanRows 1068).cutoff/2-2 = (540/247:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable350.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1068).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1068).criticalRate j.val*(generalMeanRows 1068).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1068).c*(generalMeanRows 1068).criticalPoint j.val)).2-
      (generalMeanRows 1068).J/2-(generalMeanRows 1068).error (generalMeanGrid j.val)+
      (generalMeanRows 1068).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1068).c)).2-
      (generalMeanRows 1068).J/2-(generalMeanRows 1068).error 4 := by
  have he : (generalMeanRows 1068).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1068) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1068)
    (generalMeanRows_prefactorDomain 1068) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1068

/-! Kernel-checked entropy margins for general spectral rectangle 1069. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1069
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6849917379) (.branch 2 (.leaf 6647392142) (.leaf 6453089117))) (.branch 5 (.branch 4 (.leaf 6266554562) (.leaf 6087366886)) (.branch 6 (.leaf 5915133816) (.leaf 5749489863)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5590094061) (.leaf 5436627938)) (.branch 10 (.leaf 5288793692) (.leaf 5146312550))) (.branch 13 (.branch 12 (.leaf 5008923276) (.leaf 4876380832)) (.branch 14 (.leaf 4748455154) (.leaf 4624930043))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4505602149) (.branch 17 (.leaf 4390280056) (.leaf 4278783431))) (.branch 20 (.branch 19 (.leaf 4170942251) (.leaf 4066596096)) (.branch 21 (.leaf 3965593499) (.leaf 3867791341)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3773054303) (.leaf 3681254355)) (.branch 25 (.leaf 3592270287) (.leaf 3505987271))) (.branch 28 (.branch 27 (.leaf 3422296463) (.leaf 3341094624)) (.branch 29 (.leaf 3262283781) (.leaf 3185770899)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3111467588) (.branch 32 (.leaf 3039289822) (.leaf 2969157679))) (.branch 35 (.branch 34 (.leaf 2900995106) (.leaf 2834729690)) (.branch 36 (.leaf 2770292447) (.leaf 2707617633)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2646642552) (.leaf 2587307395)) (.branch 40 (.leaf 2529555070) (.leaf 2473331061))) (.branch 43 (.branch 42 (.leaf 2418583281) (.leaf 2365261946)) (.branch 44 (.leaf 2313319445) (.leaf 2262710232))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2213390711) (.branch 47 (.leaf 2165319136) (.leaf 2118455517))) (.branch 50 (.branch 49 (.leaf 2072761526) (.leaf 2028200415)) (.branch 51 (.leaf 1984736935) (.leaf 1942337259)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1900968915) (.leaf 1860600715)) (.branch 55 (.leaf 1821202696) (.leaf 1782746056))) (.branch 58 (.branch 57 (.leaf 1745203101) (.leaf 1708547193)) (.branch 59 (.leaf 1672752695) (.leaf 1637794929))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1603650130) (.branch 62 (.leaf 1570295401) (.leaf 1537708675))) (.branch 65 (.branch 64 (.leaf 1505868678) (.leaf 1474754893)) (.branch 66 (.leaf 1444347525) (.leaf 1414627467)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1385576275) (.leaf 1357176134)) (.branch 70 (.leaf 1329409835) (.leaf 1302260743))) (.branch 73 (.branch 72 (.leaf 1275712780) (.leaf 1249750394)) (.branch 74 (.leaf 1224358544) (.leaf 1199522672))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1175228689) (.branch 77 (.leaf 1151462952) (.leaf 1128212247))) (.branch 80 (.branch 79 (.leaf 1105463772) (.leaf 1083205122)) (.branch 81 (.leaf 1061424270) (.leaf 1040109554)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1019249665) (.leaf 998833630)) (.branch 85 (.leaf 978850800) (.leaf 959290839))) (.branch 88 (.branch 87 (.leaf 940143712) (.leaf 921399673)) (.branch 89 (.leaf 903049256) (.leaf 885083260)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 867492749) (.branch 92 (.leaf 850269030) (.leaf 833403656))) (.branch 95 (.branch 94 (.leaf 816888411) (.leaf 800715301)) (.branch 96 (.leaf 784876552) (.leaf 769364596)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 754172069) (.leaf 739291802)) (.branch 100 (.leaf 724716815) (.leaf 710440308))) (.branch 103 (.branch 102 (.leaf 696455661) (.leaf 682756423)) (.branch 104 (.leaf 669336308) (.leaf 656189190))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 643309099) (.leaf 630690215)) (.branch 108 (.leaf 618326862) (.leaf 606213505))) (.branch 111 (.branch 110 (.leaf 594344748) (.leaf 582715325)) (.branch 112 (.leaf 571320100) (.leaf 560154060)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 549212314) (.leaf 538490089)) (.branch 116 (.leaf 527982725) (.leaf 517685673))) (.branch 119 (.branch 118 (.leaf 507594492) (.leaf 497704844)) (.branch 120 (.leaf 488012494) (.leaf 478513305)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1069).prefactor = (5695427033899951/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1069).cutoff/(generalMeanRows 1069).c)).2 =
    (415213265250893/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1069).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1069).q*(generalMeanRows 1069).cutoff/2-2 = (540/247:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable350.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1069).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1069).criticalRate j.val*(generalMeanRows 1069).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1069).c*(generalMeanRows 1069).criticalPoint j.val)).2-
      (generalMeanRows 1069).J/2-(generalMeanRows 1069).error (generalMeanGrid j.val)+
      (generalMeanRows 1069).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1069).c)).2-
      (generalMeanRows 1069).J/2-(generalMeanRows 1069).error 4 := by
  have he : (generalMeanRows 1069).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1069) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1069)
    (generalMeanRows_prefactorDomain 1069) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1069

/-! Kernel-checked entropy margins for general spectral rectangle 1070. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1070
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7192299270) (.branch 2 (.leaf 6982495604) (.leaf 6781176729))) (.branch 5 (.branch 4 (.leaf 6587873849) (.leaf 6402151432)) (.branch 6 (.leaf 6223604275) (.leaf 6051854884)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5886551133) (.leaf 5727364162)) (.branch 10 (.leaf 5573986495) (.leaf 5426130330))) (.branch 13 (.branch 12 (.leaf 5283526008) (.leaf 5145920617)) (.branch 14 (.leaf 5013076729) (.leaf 4884771252))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4760794383) (.branch 17 (.leaf 4640948649) (.leaf 4525048040))) (.branch 20 (.branch 19 (.leaf 4412917200) (.leaf 4304390699)) (.branch 21 (.leaf 4199312359) (.leaf 4097534629)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3998918016) (.leaf 3903330561)) (.branch 25 (.leaf 3810647346) (.leaf 3720750049))) (.branch 28 (.branch 27 (.leaf 3633526526) (.leaf 3548870423)) (.branch 29 (.leaf 3466680822) (.leaf 3386861904)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3309322645) (.branch 32 (.leaf 3233976526) (.leaf 3160741264))) (.branch 35 (.branch 34 (.leaf 3089538568) (.leaf 3020293902)) (.branch 36 (.leaf 2952936270) (.leaf 2887398014)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2823614626) (.leaf 2761524566)) (.branch 40 (.leaf 2701069105) (.leaf 2642192164))) (.branch 43 (.branch 42 (.leaf 2584840169) (.leaf 2528961919)) (.branch 44 (.leaf 2474508454) (.leaf 2421432940))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2369690551) (.branch 47 (.leaf 2319238369) (.leaf 2270035281))) (.branch 50 (.branch 49 (.leaf 2222041888) (.leaf 2175220417)) (.branch 51 (.leaf 2129534636) (.leaf 2084949779)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2041432472) (.leaf 1998950665)) (.branch 55 (.leaf 1957473563) (.leaf 1916971569))) (.branch 58 (.branch 57 (.leaf 1877416225) (.leaf 1838780157)) (.branch 59 (.leaf 1801037021) (.leaf 1764161459))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1728129048) (.branch 62 (.leaf 1692916261) (.leaf 1658500422))) (.branch 65 (.branch 64 (.leaf 1624859668) (.leaf 1591972916)) (.branch 66 (.leaf 1559819819) (.leaf 1528380745)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1497636734) (.leaf 1467569476)) (.branch 70 (.leaf 1438161280) (.leaf 1409395049))) (.branch 73 (.branch 72 (.leaf 1381254249) (.leaf 1353722895)) (.branch 74 (.leaf 1326785517) (.leaf 1300427147))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1274633295) (.branch 77 (.leaf 1249389926) (.leaf 1224683450))) (.branch 80 (.branch 79 (.leaf 1200500694) (.leaf 1176828895)) (.branch 81 (.leaf 1153655675) (.leaf 1130969033)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1108757325) (.leaf 1087009255)) (.branch 85 (.leaf 1065713858) (.leaf 1044860488))) (.branch 88 (.branch 87 (.leaf 1024438809) (.leaf 1004438779)) (.branch 89 (.leaf 984850643) (.leaf 965664921)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 946872397) (.branch 92 (.leaf 928464111) (.leaf 910431350))) (.branch 95 (.branch 94 (.leaf 892765639) (.leaf 875458731)) (.branch 96 (.leaf 858502602) (.leaf 841889442)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 825611647) (.leaf 809661814)) (.branch 100 (.leaf 794032730) (.leaf 778717373))) (.branch 103 (.branch 102 (.leaf 763708898) (.leaf 749000637)) (.branch 104 (.leaf 734586091) (.leaf 720458923))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 706612957) (.leaf 693042168)) (.branch 108 (.leaf 679740682) (.leaf 666702768))) (.branch 111 (.branch 110 (.leaf 653922835) (.leaf 641395428)) (.branch 112 (.leaf 629115223) (.leaf 617077024)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 605275760) (.leaf 593706478)) (.branch 116 (.leaf 582364343) (.leaf 571244633))) (.branch 119 (.branch 118 (.leaf 560342737) (.leaf 549654149)) (.branch 120 (.leaf 539174470) (.leaf 528899399)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1070).prefactor = (5891673052029967/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1070).cutoff/(generalMeanRows 1070).c)).2 =
    (210600653547759/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1070).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1070).q*(generalMeanRows 1070).c/2-2 = (2989/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable352.value]
  have hcontinuation : (generalMeanRows 1070).q*(generalMeanRows 1070).cutoff/2-2 = (540/247:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable350.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1070).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1070).criticalRate j.val*(generalMeanRows 1070).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1070).c*(generalMeanRows 1070).criticalPoint j.val)).2-
      (generalMeanRows 1070).J/2-(generalMeanRows 1070).error (generalMeanGrid j.val)+
      (generalMeanRows 1070).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1070).c)).2-
      (generalMeanRows 1070).J/2-(generalMeanRows 1070).error 4 := by
  have he : (generalMeanRows 1070).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1070) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1070)
    (generalMeanRows_prefactorDomain 1070) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1070

/-! Kernel-checked entropy margins for general spectral rectangle 1071. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1071
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7537316366) (.branch 2 (.leaf 7323432890) (.leaf 7118135537))) (.branch 5 (.branch 4 (.leaf 6920948601) (.leaf 6731430228)) (.branch 6 (.leaf 6549169420) (.leaf 6373783369)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6204915073) (.leaf 6042231195)) (.branch 10 (.leaf 5885420145) (.leaf 5734190342))) (.branch 13 (.branch 12 (.leaf 5588268648) (.leaf 5447398955)) (.branch 14 (.leaf 5311340894) (.leaf 5179868666))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5052769976) (.branch 17 (.leaf 4929845058) (.leaf 4810905791))) (.branch 20 (.branch 19 (.leaf 4695774876) (.leaf 4584285096)) (.branch 21 (.leaf 4476278625) (.leaf 4371606397)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4270127527) (.leaf 4171708772)) (.branch 25 (.leaf 4076224036) (.leaf 3983553911))) (.branch 28 (.branch 27 (.leaf 3893585257) (.leaf 3806210803)) (.branch 29 (.leaf 3721328790) (.leaf 3638842626)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3558660578) (.branch 32 (.leaf 3480695475) (.leaf 3404864439))) (.branch 35 (.branch 34 (.leaf 3331088629) (.leaf 3259293008)) (.branch 36 (.leaf 3189406122) (.leaf 3121359892)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3055089423) (.leaf 2990532826)) (.branch 40 (.leaf 2927631048) (.leaf 2866327716))) (.branch 43 (.branch 42 (.leaf 2806568987) (.leaf 2748303415)) (.branch 44 (.leaf 2691481815) (.leaf 2636057147))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2581984400) (.branch 47 (.leaf 2529220484) (.leaf 2477724129))) (.branch 50 (.branch 49 (.leaf 2427455794) (.leaf 2378377573)) (.branch 51 (.leaf 2330453117) (.leaf 2283647549)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2237927393) (.leaf 2193260506)) (.branch 55 (.leaf 2149616008) (.leaf 2106964222))) (.branch 58 (.branch 57 (.leaf 2065276617) (.leaf 2024525747)) (.branch 59 (.leaf 1984685206) (.leaf 1945729574))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1907634371) (.branch 62 (.leaf 1870376015) (.leaf 1833931776))) (.branch 65 (.branch 64 (.leaf 1798279743) (.leaf 1763398780)) (.branch 66 (.leaf 1729268497) (.leaf 1695869211)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1663181918) (.leaf 1631188262)) (.branch 70 (.leaf 1599870505) (.leaf 1569211504))) (.branch 73 (.branch 72 (.leaf 1539194681) (.leaf 1509804001)) (.branch 74 (.leaf 1481023949) (.leaf 1452839509))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1425236141) (.branch 77 (.leaf 1398199762) (.leaf 1371716729))) (.branch 80 (.branch 79 (.leaf 1345773819) (.leaf 1320358214)) (.branch 81 (.leaf 1295457483) (.leaf 1271059567)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1247152768) (.leaf 1223725729)) (.branch 85 (.leaf 1200767425) (.leaf 1178267149))) (.branch 88 (.branch 87 (.leaf 1156214501) (.leaf 1134599376)) (.branch 89 (.leaf 1113411953) (.leaf 1092642682)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1072282280) (.branch 92 (.leaf 1052321717) (.leaf 1032752206))) (.branch 95 (.branch 94 (.leaf 1013565200) (.leaf 994752378)) (.branch 96 (.leaf 976305638) (.leaf 958217093)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 940479059) (.leaf 923084054)) (.branch 100 (.leaf 906024784) (.leaf 889294142))) (.branch 103 (.branch 102 (.leaf 872885201) (.leaf 856791207)) (.branch 104 (.leaf 841005574) (.leaf 825521878))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 810333854) (.leaf 795435389)) (.branch 108 (.leaf 780820516) (.leaf 766483413))) (.branch 111 (.branch 110 (.leaf 752418398) (.leaf 738619921)) (.branch 112 (.leaf 725082566) (.leaf 711801040)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 698770175) (.leaf 685984924)) (.branch 116 (.leaf 673440354) (.leaf 661131646))) (.branch 119 (.branch 118 (.leaf 649054089) (.leaf 637203079)) (.branch 120 (.leaf 625574117) (.leaf 614162803)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1071).prefactor = (5992317435230421/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1071).cutoff/(generalMeanRows 1071).c)).2 =
    (108321511577647/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1071).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1071).q*(generalMeanRows 1071).cutoff/2-2 = (540/247:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable350.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1071).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1071).criticalRate j.val*(generalMeanRows 1071).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1071).c*(generalMeanRows 1071).criticalPoint j.val)).2-
      (generalMeanRows 1071).J/2-(generalMeanRows 1071).error (generalMeanGrid j.val)+
      (generalMeanRows 1071).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1071).c)).2-
      (generalMeanRows 1071).J/2-(generalMeanRows 1071).error 4 := by
  have he : (generalMeanRows 1071).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1071) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1071)
    (generalMeanRows_prefactorDomain 1071) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1071

/-! Kernel-checked entropy margins for general spectral rectangle 1072. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1072
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7094123517) (.branch 2 (.leaf 6889260933) (.leaf 6692373831))) (.branch 5 (.branch 4 (.leaf 6503044368) (.leaf 6320883470)) (.branch 6 (.leaf 6145528272) (.leaf 5976639852)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5813901207) (.leaf 5657015439)) (.branch 10 (.leaf 5505704134) (.leaf 5359705904))) (.branch 13 (.branch 12 (.leaf 5218775071) (.leaf 5082680473)) (.branch 14 (.leaf 4951204394) (.leaf 4824141579))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4701298347) (.branch 17 (.leaf 4582491781) (.leaf 4467548982))) (.branch 20 (.branch 19 (.leaf 4356306392) (.leaf 4248609174)) (.branch 21 (.leaf 4144310637) (.leaf 4043271711)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3945360465) (.leaf 3850451654)) (.branch 25 (.leaf 3758426312) (.leaf 3669171367))) (.branch 28 (.branch 27 (.leaf 3582579286) (.leaf 3498547747)) (.branch 29 (.leaf 3416979334) (.leaf 3337781253)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3260865068) (.branch 32 (.leaf 3186146455) (.leaf 3113544971))) (.branch 35 (.branch 34 (.leaf 3042983841) (.leaf 2974389756)) (.branch 36 (.leaf 2907692688) (.leaf 2842825712)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2779724843) (.leaf 2718328882)) (.branch 40 (.leaf 2658579269) (.leaf 2600419949))) (.branch 43 (.branch 42 (.leaf 2543797245) (.leaf 2488659736)) (.branch 44 (.leaf 2434958145) (.leaf 2382645232))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2331675693) (.branch 47 (.leaf 2282006068) (.leaf 2233594648))) (.branch 50 (.branch 49 (.leaf 2186401395) (.leaf 2140387858)) (.branch 51 (.leaf 2095517102) (.leaf 2051753634)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2009063337) (.leaf 1967413404)) (.branch 55 (.leaf 1926772284) (.leaf 1887109618))) (.branch 58 (.branch 57 (.leaf 1848396187) (.leaf 1810603865)) (.branch 59 (.leaf 1773705564) (.leaf 1737675191))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1702487605) (.branch 62 (.leaf 1668118575) (.leaf 1634544739))) (.branch 65 (.branch 64 (.leaf 1601743567) (.leaf 1569693328)) (.branch 66 (.leaf 1538373052) (.leaf 1507762501)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1477842136) (.leaf 1448593090)) (.branch 70 (.leaf 1419997138) (.leaf 1392036673))) (.branch 73 (.branch 72 (.leaf 1364694678) (.leaf 1337954705)) (.branch 74 (.leaf 1311800848) (.leaf 1286217727))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1261190462) (.branch 77 (.leaf 1236704653) (.leaf 1212746367))) (.branch 80 (.branch 79 (.leaf 1189302113) (.leaf 1166358828)) (.branch 81 (.leaf 1143903861) (.leaf 1121924956)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1100410236) (.leaf 1079348193)) (.branch 85 (.leaf 1058727667) (.leaf 1038537839))) (.branch 88 (.branch 87 (.leaf 1018768218) (.leaf 999408623)) (.branch 89 (.leaf 980449180) (.leaf 961880305)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 943692694) (.branch 92 (.leaf 925877315) (.leaf 908425399))) (.branch 95 (.branch 94 (.leaf 891328425) (.leaf 874578120)) (.branch 96 (.leaf 858166442) (.leaf 842085577)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 826327929) (.leaf 810886113)) (.branch 100 (.leaf 795752949) (.leaf 780921453))) (.branch 103 (.branch 102 (.leaf 766384831) (.leaf 752136474)) (.branch 104 (.leaf 738169950) (.leaf 724478999))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 711057528) (.leaf 697899603)) (.branch 108 (.leaf 684999447) (.leaf 672351434))) (.branch 111 (.branch 110 (.leaf 659950083) (.leaf 647790055)) (.branch 112 (.leaf 635866146) (.leaf 624173286)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 612706532) (.leaf 601461067)) (.branch 116 (.leaf 590432192) (.leaf 579615327))) (.branch 119 (.branch 118 (.leaf 569006005) (.leaf 558599867)) (.branch 120 (.leaf 548392662) (.leaf 538380242)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1072).prefactor = (1320329404766509/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1072).cutoff/(generalMeanRows 1072).c)).2 =
    (335509933825671/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1072).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1072).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1072).criticalRate j.val*(generalMeanRows 1072).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1072).c*(generalMeanRows 1072).criticalPoint j.val)).2-
      (generalMeanRows 1072).J/2-(generalMeanRows 1072).error (generalMeanGrid j.val)+
      (generalMeanRows 1072).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1072).c)).2-
      (generalMeanRows 1072).J/2-(generalMeanRows 1072).error 4 := by
  have he : (generalMeanRows 1072).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1072) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1072)
    (generalMeanRows_prefactorDomain 1072) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1072

/-! Kernel-checked entropy margins for general spectral rectangle 1073. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1073
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6756077899) (.branch 2 (.leaf 6561062462) (.leaf 6373696107))) (.branch 5 (.branch 4 (.leaf 6193574016) (.leaf 6020319362)) (.branch 6 (.leaf 5853580836) (.leaf 5693030436)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5538361505) (.leaf 5389286965)) (.branch 10 (.leaf 5245537744) (.leaf 5106861348))) (.branch 13 (.branch 12 (.leaf 4973020583) (.leaf 4843792399)) (.branch 14 (.leaf 4718966829) (.leaf 4598346047))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4481743489) (.branch 17 (.leaf 4368983066) (.leaf 4259898440))) (.branch 20 (.branch 19 (.leaf 4154332355) (.leaf 4052136037)) (.branch 21 (.leaf 3953168630) (.leaf 3857296682)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3764393673) (.leaf 3674339578)) (.branch 25 (.leaf 3587020462) (.leaf 3502328106))) (.branch 28 (.branch 27 (.leaf 3420159660) (.leaf 3340417325)) (.branch 29 (.leaf 3263008051) (.leaf 3187843260)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3114838589) (.branch 32 (.leaf 3043913650) (.leaf 2974991804))) (.branch 35 (.branch 34 (.leaf 2907999952) (.leaf 2842868340)) (.branch 36 (.leaf 2779530375) (.leaf 2717922454)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2657983805) (.leaf 2599656334)) (.branch 40 (.leaf 2542884487) (.leaf 2487615115))) (.branch 43 (.branch 42 (.leaf 2433797351) (.leaf 2381382493)) (.branch 44 (.leaf 2330323893) (.leaf 2280576854))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2232098535) (.branch 47 (.leaf 2184847855) (.leaf 2138785408))) (.branch 50 (.branch 49 (.leaf 2093873383) (.leaf 2050075485)) (.branch 51 (.leaf 2007356862) (.leaf 1965684038)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1925024846) (.leaf 1885348368)) (.branch 55 (.leaf 1846624877) (.leaf 1808825779))) (.branch 58 (.branch 57 (.leaf 1771923565) (.leaf 1735891760)) (.branch 59 (.leaf 1700704873) (.leaf 1666338360))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1632768573) (.branch 62 (.leaf 1599972728) (.leaf 1567928861))) (.branch 65 (.branch 64 (.leaf 1536615797) (.leaf 1506013111)) (.branch 66 (.leaf 1476101102) (.leaf 1446860753)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1418273712) (.leaf 1390322255)) (.branch 70 (.leaf 1362989266) (.leaf 1336258209))) (.branch 73 (.branch 72 (.leaf 1310113103) (.leaf 1284538501)) (.branch 74 (.leaf 1259519468) (.leaf 1235041559))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1211090800) (.branch 77 (.leaf 1187653670) (.leaf 1164717083))) (.branch 80 (.branch 79 (.leaf 1142268367) (.leaf 1120295252)) (.branch 81 (.leaf 1098785855) (.leaf 1077728660)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1057112510) (.leaf 1036926587)) (.branch 85 (.leaf 1017160405) (.leaf 997803794))) (.branch 88 (.branch 87 (.leaf 978846888) (.leaf 960280117)) (.branch 89 (.leaf 942094191) (.leaf 924280094)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 906829074) (.branch 92 (.leaf 889732629) (.leaf 872982504))) (.branch 95 (.branch 94 (.leaf 856570677) (.leaf 840489353)) (.branch 96 (.leaf 824730959) (.leaf 809288129)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 794153703) (.leaf 779320720)) (.branch 100 (.leaf 764782406) (.leaf 750532171))) (.branch 103 (.branch 102 (.leaf 736563605) (.leaf 722870468)) (.branch 104 (.leaf 709446685) (.leaf 696286344))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 683383685) (.leaf 670733100)) (.branch 108 (.leaf 658329127) (.leaf 646166443))) (.branch 111 (.branch 110 (.leaf 634239861) (.leaf 622544328)) (.branch 112 (.leaf 611074915) (.leaf 599826820)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 588795360) (.leaf 577975967)) (.branch 116 (.leaf 567364186) (.leaf 556955672))) (.branch 119 (.branch 118 (.leaf 546746185) (.leaf 536731588)) (.branch 120 (.leaf 526907844) (.leaf 517271013)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1073).prefactor = (2555795165954469/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1073).cutoff/(generalMeanRows 1073).c)).2 =
    (70671955298169/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1073).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1073).q*(generalMeanRows 1073).cutoff/2-2 = (1561/841:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable353.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1073).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1073).criticalRate j.val*(generalMeanRows 1073).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1073).c*(generalMeanRows 1073).criticalPoint j.val)).2-
      (generalMeanRows 1073).J/2-(generalMeanRows 1073).error (generalMeanGrid j.val)+
      (generalMeanRows 1073).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1073).c)).2-
      (generalMeanRows 1073).J/2-(generalMeanRows 1073).error 4 := by
  have he : (generalMeanRows 1073).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1073) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1073)
    (generalMeanRows_prefactorDomain 1073) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1073

/-! Kernel-checked entropy margins for general spectral rectangle 1074. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1074
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6591697650) (.branch 2 (.leaf 6388728293) (.leaf 6193872485))) (.branch 5 (.branch 4 (.leaf 6006702756) (.leaf 5826821013)) (.branch 6 (.leaf 5653855946) (.leaf 5487460717)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5327310902) (.leaf 5173102646)) (.branch 10 (.leaf 5024551014) (.leaf 4881388498))) (.branch 13 (.branch 12 (.leaf 4743363675) (.leaf 4610239997)) (.branch 14 (.leaf 4481794685) (.leaf 4357817732))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4238110992) (.branch 17 (.leaf 4122487350) (.leaf 4010769962))) (.branch 20 (.branch 19 (.leaf 3902791561) (.leaf 3798393818)) (.branch 21 (.leaf 3697426757) (.leaf 3599748218)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3505223356) (.leaf 3413724186)) (.branch 25 (.leaf 3325129156) (.leaf 3239322757))) (.branch 28 (.branch 27 (.leaf 3156195162) (.leaf 3075641880)) (.branch 29 (.leaf 2997563452) (.leaf 2921865156)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2848456734) (.branch 32 (.leaf 2777252142) (.leaf 2708169311))) (.branch 35 (.branch 34 (.leaf 2641129932) (.leaf 2576059245)) (.branch 36 (.leaf 2512885849) (.leaf 2451541522)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2391961051) (.leaf 2334082074)) (.branch 40 (.leaf 2277844933) (.leaf 2223192532))) (.branch 43 (.branch 42 (.leaf 2170070209) (.leaf 2118425608)) (.branch 44 (.leaf 2068208568) (.leaf 2019371013))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1971866844) (.branch 47 (.leaf 1925651848) (.leaf 1880683606))) (.branch 50 (.branch 49 (.leaf 1836921402) (.leaf 1794326146)) (.branch 51 (.leaf 1752860295) (.leaf 1712487781)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1673173942) (.leaf 1634885457)) (.branch 55 (.leaf 1597590281) (.leaf 1561257594))) (.branch 58 (.branch 57 (.leaf 1525857739) (.leaf 1491362172)) (.branch 59 (.leaf 1457743412) (.leaf 1424974995))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1393031427) (.branch 62 (.leaf 1361888145) (.leaf 1331521471))) (.branch 65 (.branch 64 (.leaf 1301908580) (.leaf 1273027461)) (.branch 66 (.leaf 1244856879) (.leaf 1217376349)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1190566098) (.leaf 1164407040)) (.branch 70 (.leaf 1138880745) (.leaf 1113969412))) (.branch 73 (.branch 72 (.leaf 1089655845) (.leaf 1065923427)) (.branch 74 (.leaf 1042756098) (.leaf 1020138329))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 998055107) (.branch 77 (.leaf 976491910) (.leaf 955434687))) (.branch 80 (.branch 79 (.leaf 934869845) (.leaf 914784225)) (.branch 81 (.leaf 895165090) (.leaf 876000105)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 857277324) (.leaf 838985177)) (.branch 85 (.leaf 821112451) (.leaf 803648281))) (.branch 88 (.branch 87 (.leaf 786582136) (.leaf 769903804)) (.branch 89 (.leaf 753603385) (.leaf 737671277)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 722098163) (.branch 92 (.leaf 706875006) (.leaf 691993035))) (.branch 95 (.branch 94 (.leaf 677443737) (.leaf 663218848)) (.branch 96 (.leaf 649310343) (.leaf 635710430)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 622411539) (.leaf 609406319)) (.branch 100 (.leaf 596687624) (.leaf 584248511))) (.branch 103 (.branch 102 (.leaf 572082233) (.leaf 560182229)) (.branch 104 (.leaf 548542122) (.leaf 537155709))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 526016958) (.leaf 515120002)) (.branch 108 (.leaf 504459133) (.leaf 494028797))) (.branch 111 (.branch 110 (.leaf 483823589) (.leaf 473838248)) (.branch 112 (.leaf 464067655) (.leaf 454506823)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 445150898) (.leaf 435995155)) (.branch 116 (.leaf 427034988) (.leaf 418265914))) (.branch 119 (.branch 118 (.leaf 409683564) (.leaf 401283683)) (.branch 120 (.leaf 393062121) (.leaf 385014838)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1074).prefactor = (268163465840821/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1074).cutoff/(generalMeanRows 1074).c)).2 =
    (322009246606769/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1074).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1074).q*(generalMeanRows 1074).c/2-2 = (1589/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable251.value]
  have hcontinuation : (generalMeanRows 1074).q*(generalMeanRows 1074).cutoff/2-2 = (1561/841:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable353.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1074).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1074).criticalRate j.val*(generalMeanRows 1074).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1074).c*(generalMeanRows 1074).criticalPoint j.val)).2-
      (generalMeanRows 1074).J/2-(generalMeanRows 1074).error (generalMeanGrid j.val)+
      (generalMeanRows 1074).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1074).c)).2-
      (generalMeanRows 1074).J/2-(generalMeanRows 1074).error 4 := by
  have he : (generalMeanRows 1074).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1074) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1074)
    (generalMeanRows_prefactorDomain 1074) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1074

/-! Kernel-checked entropy margins for general spectral rectangle 1075. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1075
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6603237037) (.branch 2 (.leaf 6409281193) (.leaf 6223024176))) (.branch 5 (.branch 4 (.leaf 6044054843) (.leaf 5871990590)) (.branch 6 (.leaf 5706474832) (.leaf 5547174754)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5393779315) (.leaf 5245997448)) (.branch 10 (.leaf 5103556453) (.leaf 4966200546))) (.branch 13 (.branch 12 (.leaf 4833689552) (.leaf 4705797720)) (.branch 14 (.leaf 4582312649) (.leaf 4463034316))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4347774182) (.branch 17 (.leaf 4236354386) (.leaf 4128607004))) (.branch 20 (.branch 19 (.leaf 4024373369) (.leaf 3923503447)) (.branch 21 (.leaf 3825855269) (.leaf 3731294403)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3639693467) (.leaf 3550931684)) (.branch 25 (.leaf 3464894469) (.leaf 3381473045))) (.branch 28 (.branch 27 (.leaf 3300564085) (.leaf 3222069390)) (.branch 29 (.leaf 3145895580) (.leaf 3071953808)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3000159500) (.branch 32 (.leaf 2930432107) (.leaf 2862694874))) (.branch 35 (.branch 34 (.leaf 2796874629) (.leaf 2732901582)) (.branch 36 (.leaf 2670709136) (.leaf 2610233716)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2551414602) (.leaf 2494193776)) (.branch 40 (.leaf 2438515780) (.leaf 2384327579))) (.branch 43 (.branch 42 (.leaf 2331578438) (.leaf 2280219796)) (.branch 44 (.leaf 2230205161) (.leaf 2181490002))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2134031648) (.branch 47 (.leaf 2087789199) (.leaf 2042723434))) (.branch 50 (.branch 49 (.leaf 1998796730) (.leaf 1955972984)) (.branch 51 (.leaf 1914217539) (.leaf 1873497114)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1833779736) (.leaf 1795034685)) (.branch 55 (.leaf 1757232425) (.leaf 1720344557))) (.branch 58 (.branch 57 (.leaf 1684343763) (.leaf 1649203754)) (.branch 59 (.leaf 1614899228) (.leaf 1581405821))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1548700064) (.branch 62 (.leaf 1516759349) (.leaf 1485561885))) (.branch 65 (.branch 64 (.leaf 1455086662) (.leaf 1425313420)) (.branch 66 (.leaf 1396222616) (.leaf 1367795389)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1340013536) (.leaf 1312859480)) (.branch 70 (.leaf 1286316247) (.leaf 1260367436))) (.branch 73 (.branch 72 (.leaf 1234997201) (.leaf 1210190222)) (.branch 74 (.leaf 1185931689) (.leaf 1162207276))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1139003125) (.branch 77 (.leaf 1116305826) (.leaf 1094102400))) (.branch 80 (.branch 79 (.leaf 1072380279) (.leaf 1051127293)) (.branch 81 (.leaf 1030331653) (.leaf 1009981937)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 990067075) (.leaf 970576335)) (.branch 85 (.leaf 951499313) (.leaf 932825916))) (.branch 88 (.branch 87 (.leaf 914546354) (.leaf 896651129)) (.branch 89 (.leaf 879131022) (.leaf 861977082)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 845180621) (.branch 92 (.leaf 828733198) (.leaf 812626618))) (.branch 95 (.branch 94 (.leaf 796852914) (.leaf 781404347)) (.branch 96 (.leaf 766273393) (.leaf 751452739)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 736935272) (.leaf 722714076)) (.branch 100 (.leaf 708782422) (.leaf 695133763))) (.branch 103 (.branch 102 (.leaf 681761729) (.leaf 668660119)) (.branch 104 (.leaf 655822898) (.leaf 643244189))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 630918268) (.leaf 618839562)) (.branch 108 (.leaf 607002640) (.leaf 595402211))) (.branch 111 (.branch 110 (.leaf 584033121) (.leaf 572890345)) (.branch 112 (.leaf 561968985) (.leaf 551264266)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 540771531) (.leaf 530486242)) (.branch 116 (.leaf 520403968) (.leaf 510520390))) (.branch 119 (.branch 118 (.leaf 500831294) (.leaf 491332567)) (.branch 120 (.leaf 482020196) (.leaf 472890263)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1075).prefactor = (161921738693773/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1075).cutoff/(generalMeanRows 1075).c)).2 =
    (363292536665959/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1075).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1075).q*(generalMeanRows 1075).c/2-2 = (737/1000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable090.value]
  have hcontinuation : (generalMeanRows 1075).q*(generalMeanRows 1075).cutoff/2-2 = (393/203:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable354.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1075).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1075).criticalRate j.val*(generalMeanRows 1075).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1075).c*(generalMeanRows 1075).criticalPoint j.val)).2-
      (generalMeanRows 1075).J/2-(generalMeanRows 1075).error (generalMeanGrid j.val)+
      (generalMeanRows 1075).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1075).c)).2-
      (generalMeanRows 1075).J/2-(generalMeanRows 1075).error 4 := by
  have he : (generalMeanRows 1075).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1075) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1075)
    (generalMeanRows_prefactorDomain 1075) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1075

/-! Kernel-checked entropy margins for general spectral rectangle 1076. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1076
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6235671890) (.branch 2 (.leaf 6035751147) (.leaf 5843994884))) (.branch 5 (.branch 4 (.leaf 5659969175) (.leaf 5483269951)) (.branch 6 (.leaf 5313520373) (.leaf 5150368491)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4993485157) (.leaf 4842562160)) (.branch 10 (.leaf 4697310539) (.leaf 4557459078))) (.branch 13 (.branch 12 (.leaf 4422752939) (.leaf 4292952425)) (.branch 14 (.leaf 4167831865) (.leaf 4047178592))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3930792017) (.branch 17 (.leaf 3818482783) (.leaf 3710071991))) (.branch 20 (.branch 19 (.leaf 3605390493) (.leaf 3504278239)) (.branch 21 (.leaf 3406583682) (.leaf 3312163227)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3220880722) (.leaf 3132606995)) (.branch 25 (.leaf 3047219416) (.leaf 2964601498))) (.branch 28 (.branch 27 (.leaf 2884642529) (.leaf 2807237222)) (.branch 29 (.leaf 2732285401) (.leaf 2659691699)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2589365283) (.branch 32 (.leaf 2521219598) (.leaf 2455172121))) (.branch 35 (.branch 34 (.leaf 2391144141) (.leaf 2329060547)) (.branch 36 (.leaf 2268849634) (.leaf 2210442914)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2153774949) (.leaf 2098783188)) (.branch 40 (.leaf 2045407816) (.leaf 1993591608))) (.branch 43 (.branch 42 (.leaf 1943279803) (.leaf 1894419970)) (.branch 44 (.leaf 1846961898) (.leaf 1800857477))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1756060600) (.branch 47 (.leaf 1712527060) (.leaf 1670214459))) (.branch 50 (.branch 49 (.leaf 1629082121) (.leaf 1589091006)) (.branch 51 (.leaf 1550203635) (.leaf 1512384014)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1475597565) (.leaf 1439811062)) (.branch 55 (.leaf 1404992562) (.leaf 1371111355))) (.branch 58 (.branch 57 (.leaf 1338137900) (.leaf 1306043777)) (.branch 59 (.leaf 1274801633) (.leaf 1244385137))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1214768934) (.branch 62 (.leaf 1185928601) (.leaf 1157840609))) (.branch 65 (.branch 64 (.leaf 1130482281) (.leaf 1103831755)) (.branch 66 (.leaf 1077867954) (.leaf 1052570546)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1027919920) (.leaf 1003897147)) (.branch 70 (.leaf 980483960) (.leaf 957662722))) (.branch 73 (.branch 72 (.leaf 935416399) (.leaf 913728541)) (.branch 74 (.leaf 892583251) (.leaf 871965170))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 851859449) (.branch 77 (.leaf 832251734) (.leaf 813128143))) (.branch 80 (.branch 79 (.leaf 794475249) (.leaf 776280062)) (.branch 81 (.leaf 758530012) (.leaf 741212933)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 724317047) (.leaf 707830951)) (.branch 85 (.leaf 691743601) (.leaf 676044298))) (.branch 88 (.branch 87 (.leaf 660722677) (.leaf 645768697)) (.branch 89 (.leaf 631172621) (.leaf 616925013)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 603016724) (.branch 92 (.leaf 589438882) (.leaf 576182881))) (.branch 95 (.branch 94 (.leaf 563240371) (.leaf 550603254)) (.branch 96 (.leaf 538263668) (.leaf 526213984)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 514446796) (.leaf 502954913)) (.branch 100 (.leaf 491731353) (.leaf 480769333))) (.branch 103 (.branch 102 (.leaf 470062267) (.leaf 459603755)) (.branch 104 (.leaf 449387577) (.leaf 439407692))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 429658225) (.leaf 420133468)) (.branch 108 (.leaf 410827869) (.leaf 401736032))) (.branch 111 (.branch 110 (.leaf 392852707) (.leaf 384172790)) (.branch 112 (.leaf 375691316) (.leaf 367403453)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 359304502) (.leaf 351389888)) (.branch 116 (.leaf 343655161) (.leaf 336095988))) (.branch 119 (.branch 118 (.leaf 328708151) (.leaf 321487546)) (.branch 120 (.leaf 314430174) (.leaf 307532144)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1076).prefactor = (5415502222660643/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1076).cutoff/(generalMeanRows 1076).c)).2 =
    (64146584449433/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1076).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1076).q*(generalMeanRows 1076).c/2-2 = (107/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable344.value]
  have hcontinuation : (generalMeanRows 1076).q*(generalMeanRows 1076).cutoff/2-2 = (393/203:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable354.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1076).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1076).criticalRate j.val*(generalMeanRows 1076).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1076).c*(generalMeanRows 1076).criticalPoint j.val)).2-
      (generalMeanRows 1076).J/2-(generalMeanRows 1076).error (generalMeanGrid j.val)+
      (generalMeanRows 1076).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1076).c)).2-
      (generalMeanRows 1076).J/2-(generalMeanRows 1076).error 4 := by
  have he : (generalMeanRows 1076).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1076) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1076)
    (generalMeanRows_prefactorDomain 1076) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1076

/-! Kernel-checked entropy margins for general spectral rectangle 1077. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1077
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6383281720) (.branch 2 (.leaf 6191733471) (.leaf 6007888456))) (.branch 5 (.branch 4 (.leaf 5831331513) (.leaf 5661676420)) (.branch 6 (.leaf 5498563347) (.leaf 5341656582)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5190642499) (.leaf 5045227742)) (.branch 10 (.leaf 4905137586) (.leaf 4770114470))) (.branch 13 (.branch 12 (.leaf 4639916666) (.leaf 4514317076)) (.branch 14 (.leaf 4393102140) (.leaf 4276070845))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4163033822) (.branch 17 (.leaf 4053812521) (.leaf 3948238454))) (.branch 20 (.branch 19 (.leaf 3846152511) (.leaf 3747404319)) (.branch 21 (.leaf 3651851666) (.leaf 3559359959)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3469801736) (.leaf 3383056210)) (.branch 25 (.leaf 3299008843) (.leaf 3217550960))) (.branch 28 (.branch 27 (.leaf 3138579390) (.leaf 3061996127)) (.branch 29 (.leaf 2987708023) (.leaf 2915626498)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2845667269) (.branch 32 (.leaf 2777750105) (.leaf 2711798591))) (.branch 35 (.branch 34 (.leaf 2647739910) (.leaf 2585504642)) (.branch 36 (.leaf 2525026572) (.leaf 2466242514)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2409092148) (.leaf 2353517857)) (.branch 40 (.leaf 2299464589) (.leaf 2246879718))) (.branch 43 (.branch 42 (.leaf 2195712912) (.leaf 2145916018)) (.branch 44 (.leaf 2097442948) (.leaf 2050249569))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2004293607) (.branch 47 (.leaf 1959534551) (.leaf 1915933565))) (.branch 50 (.branch 49 (.leaf 1873453403) (.leaf 1832058333)) (.branch 51 (.leaf 1791714063) (.leaf 1752387666)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1714047518) (.leaf 1676663238)) (.branch 55 (.leaf 1640205622) (.leaf 1604646594))) (.branch 58 (.branch 57 (.leaf 1569959148) (.leaf 1536117304)) (.branch 59 (.leaf 1503096053) (.leaf 1470871320))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1439419918) (.branch 62 (.leaf 1408719507) (.leaf 1378748560))) (.branch 65 (.branch 64 (.leaf 1349486321) (.leaf 1320912776)) (.branch 66 (.leaf 1293008620) (.leaf 1265755223)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1239134603) (.leaf 1213129399)) (.branch 70 (.leaf 1187722844) (.leaf 1162898739))) (.branch 73 (.branch 72 (.leaf 1138641429) (.leaf 1114935783)) (.branch 74 (.leaf 1091767170) (.leaf 1069121438))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1046984898) (.branch 77 (.leaf 1025344300) (.leaf 1004186822))) (.branch 80 (.branch 79 (.leaf 983500047) (.leaf 963271951)) (.branch 81 (.leaf 943490884) (.leaf 924145560)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 905225039) (.leaf 886718715)) (.branch 85 (.leaf 868616306) (.leaf 850907838))) (.branch 88 (.branch 87 (.leaf 833583633) (.leaf 816634303)) (.branch 89 (.leaf 800050735) (.leaf 783824083)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 767945755) (.branch 92 (.leaf 752407409) (.leaf 737200942))) (.branch 95 (.branch 94 (.leaf 722318477) (.leaf 707752364)) (.branch 96 (.leaf 693495165) (.leaf 679539647)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 665878779) (.leaf 652505723)) (.branch 100 (.leaf 639413825) (.leaf 626596615))) (.branch 103 (.branch 102 (.leaf 614047793) (.leaf 601761230)) (.branch 104 (.leaf 589730958) (.leaf 577951169))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 566416205) (.leaf 555120555)) (.branch 108 (.leaf 544058855) (.leaf 533225874))) (.branch 111 (.branch 110 (.leaf 522616519) (.leaf 512225824)) (.branch 112 (.leaf 502048951) (.leaf 492081182)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 482317919) (.leaf 472754677)) (.branch 116 (.leaf 463387084) (.leaf 454210873))) (.branch 119 (.branch 118 (.leaf 445221885) (.leaf 436416060)) (.branch 120 (.leaf 427789437) (.leaf 419338153)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1077).prefactor = (5223606393455581/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1077).cutoff/(generalMeanRows 1077).c)).2 =
    (372093351004181/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1077).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1077).q*(generalMeanRows 1077).c/2-2 = (6177/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable342.value]
  have hcontinuation : (generalMeanRows 1077).q*(generalMeanRows 1077).cutoff/2-2 = (1583/783:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable355.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1077).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1077).criticalRate j.val*(generalMeanRows 1077).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1077).c*(generalMeanRows 1077).criticalPoint j.val)).2-
      (generalMeanRows 1077).J/2-(generalMeanRows 1077).error (generalMeanGrid j.val)+
      (generalMeanRows 1077).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1077).c)).2-
      (generalMeanRows 1077).J/2-(generalMeanRows 1077).error 4 := by
  have he : (generalMeanRows 1077).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1077) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1077)
    (generalMeanRows_prefactorDomain 1077) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1077

/-! Kernel-checked entropy margins for general spectral rectangle 1078. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1078
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6094792522) (.branch 2 (.leaf 5897844085) (.leaf 5709019057))) (.branch 5 (.branch 4 (.leaf 5527881190) (.leaf 5354024416)) (.branch 6 (.leaf 5187070199) (.leaf 5026665168)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4872479008) (.leaf 4724202573)) (.branch 10 (.leaf 4581546181) (.leaf 4444238091))) (.branch 13 (.branch 12 (.leaf 4312023115) (.leaf 4184661370)) (.branch 14 (.leaf 4061927142) (.leaf 3943607852))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3829503122) (.branch 17 (.leaf 3719423908) (.leaf 3613191722))) (.branch 20 (.branch 19 (.leaf 3510637910) (.leaf 3411602992)) (.branch 21 (.leaf 3315936056) (.leaf 3223494201)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3134142020) (.leaf 3047751127)) (.branch 25 (.leaf 2964199716) (.leaf 2883372158))) (.branch 28 (.branch 27 (.leaf 2805158621) (.leaf 2729454722)) (.branch 29 (.leaf 2656161203) (.leaf 2585183630)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2516432111) (.branch 32 (.leaf 2449821036) (.leaf 2385268831))) (.branch 35 (.branch 34 (.leaf 2322697735) (.leaf 2262033583)) (.branch 36 (.leaf 2203205609) (.leaf 2146146262)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2090791028) (.leaf 2037078272)) (.branch 40 (.leaf 1984949083) (.leaf 1934347129))) (.branch 43 (.branch 42 (.leaf 1885218524) (.leaf 1837511703)) (.branch 44 (.leaf 1791177299) (.leaf 1746168037))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1702438622) (.branch 47 (.leaf 1659945648) (.leaf 1618647494))) (.branch 50 (.branch 49 (.leaf 1578504248) (.leaf 1539477614)) (.branch 51 (.leaf 1501530840) (.leaf 1464628640)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1428737126) (.leaf 1393823744)) (.branch 55 (.leaf 1359857205) (.leaf 1326807435))) (.branch 58 (.branch 57 (.leaf 1294645512) (.leaf 1263343614)) (.branch 59 (.leaf 1232874974) (.leaf 1203213826))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1174335364) (.branch 62 (.leaf 1146215699) (.leaf 1118831815))) (.branch 65 (.branch 64 (.leaf 1092161537) (.leaf 1066183488)) (.branch 66 (.leaf 1040877060) (.leaf 1016222376)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 992200263) (.leaf 968792219)) (.branch 70 (.leaf 945980387) (.leaf 923747527))) (.branch 73 (.branch 72 (.leaf 902076992) (.leaf 880952702)) (.branch 74 (.leaf 860359120) (.leaf 840281233))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 820704529) (.branch 77 (.leaf 801614976) (.leaf 782999005))) (.branch 80 (.branch 79 (.leaf 764843492) (.leaf 747135737)) (.branch 81 (.leaf 729863451) (.leaf 713014742)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 696578092) (.leaf 680542351)) (.branch 85 (.leaf 664896719) (.leaf 649630733))) (.branch 88 (.branch 87 (.leaf 634734256) (.leaf 620197465)) (.branch 89 (.leaf 606010835) (.leaf 592165134)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 578651410) (.branch 92 (.leaf 565460981) (.leaf 552585424))) (.branch 95 (.branch 94 (.leaf 540016567) (.leaf 527746482)) (.branch 96 (.leaf 515767472) (.leaf 504072066)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 492653014) (.leaf 481503270)) (.branch 100 (.leaf 470615997) (.leaf 459984551))) (.branch 103 (.branch 102 (.leaf 449602477) (.leaf 439463505)) (.branch 104 (.leaf 429561540) (.leaf 419890660))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 410445108) (.leaf 401219286)) (.branch 108 (.leaf 392207753) (.leaf 383405216))) (.branch 111 (.branch 110 (.leaf 374806529) (.leaf 366406683)) (.branch 112 (.leaf 358200810) (.leaf 350184169)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 342352151) (.leaf 334700267)) (.branch 116 (.leaf 327224149) (.leaf 319919548))) (.branch 119 (.branch 118 (.leaf 312782322) (.leaf 305808443)) (.branch 120 (.leaf 298993988) (.leaf 292335134)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1078).prefactor = (5441052114046083/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1078).cutoff/(generalMeanRows 1078).c)).2 =
    (42060159901913/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1078).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1078).q*(generalMeanRows 1078).cutoff/2-2 = (1583/783:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable355.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1078).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1078).criticalRate j.val*(generalMeanRows 1078).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1078).c*(generalMeanRows 1078).criticalPoint j.val)).2-
      (generalMeanRows 1078).J/2-(generalMeanRows 1078).error (generalMeanGrid j.val)+
      (generalMeanRows 1078).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1078).c)).2-
      (generalMeanRows 1078).J/2-(generalMeanRows 1078).error 4 := by
  have he : (generalMeanRows 1078).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1078) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1078)
    (generalMeanRows_prefactorDomain 1078) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1078

/-! Kernel-checked entropy margins for general spectral rectangle 1079. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1079
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6198778751) (.branch 2 (.leaf 6010484159) (.leaf 5829838876))) (.branch 5 (.branch 4 (.leaf 5656426427) (.leaf 5489859554)) (.branch 6 (.leaf 5329777640) (.leaf 5175844414)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5027745903) (.leaf 4885188592)) (.branch 10 (.leaf 4747897768) (.leaf 4615616037))) (.branch 13 (.branch 12 (.leaf 4488101975) (.leaf 4365128914)) (.branch 14 (.leaf 4246483832) (.leaf 4131966350))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4021387821) (.branch 17 (.leaf 3914570487) (.leaf 3811346722))) (.branch 20 (.branch 19 (.leaf 3711558326) (.leaf 3615055890)) (.branch 21 (.leaf 3521698199) (.leaf 3431351693)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3343889967) (.leaf 3259193308)) (.branch 25 (.leaf 3177148271) (.leaf 3097647283))) (.branch 28 (.branch 27 (.leaf 3020588276) (.leaf 2945874354)) (.branch 29 (.leaf 2873413472) (.leaf 2803118151)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2734905201) (.branch 32 (.leaf 2668695472) (.leaf 2604413619))) (.branch 35 (.branch 34 (.leaf 2541987879) (.leaf 2481349870)) (.branch 36 (.leaf 2422434400) (.leaf 2365179285)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2309525184) (.leaf 2255415446)) (.branch 40 (.leaf 2202795957) (.leaf 2151615008))) (.branch 43 (.branch 42 (.leaf 2101823165) (.leaf 2053373146)) (.branch 44 (.leaf 2006219713) (.leaf 1960319559))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1915631213) (.branch 47 (.leaf 1872114945) (.leaf 1829732674))) (.branch 50 (.branch 49 (.leaf 1788447890) (.leaf 1748225570)) (.branch 51 (.leaf 1709032111) (.leaf 1670835252)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1633604015) (.leaf 1597308639)) (.branch 55 (.leaf 1561920524) (.leaf 1527412173))) (.branch 58 (.branch 57 (.leaf 1493757144) (.leaf 1460929994)) (.branch 59 (.leaf 1428906238) (.leaf 1397662305))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1367175491) (.branch 62 (.leaf 1337423923) (.leaf 1308386523))) (.branch 65 (.branch 64 (.leaf 1280042969) (.leaf 1252373662)) (.branch 66 (.leaf 1225359698) (.leaf 1198982832)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1173225453) (.leaf 1148070556)) (.branch 70 (.leaf 1123501714) (.leaf 1099503059))) (.branch 73 (.branch 72 (.leaf 1076059252) (.leaf 1053155464)) (.branch 74 (.leaf 1030777355) (.leaf 1008911056))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 987543143) (.branch 77 (.leaf 966660628) (.leaf 946250934))) (.branch 80 (.branch 79 (.leaf 926301882) (.leaf 906801676)) (.branch 81 (.leaf 887738888) (.leaf 869102440)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 850881595) (.leaf 833065941)) (.branch 85 (.leaf 815645383) (.leaf 798610125))) (.branch 88 (.branch 87 (.leaf 781950662) (.leaf 765657771)) (.branch 89 (.leaf 749722497) (.leaf 734136147)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 718890277) (.branch 92 (.leaf 703976685) (.leaf 689387402))) (.branch 95 (.branch 94 (.leaf 675114685) (.leaf 661151008)) (.branch 96 (.leaf 647489053) (.leaf 634121704)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 621042044) (.leaf 608243341)) (.branch 100 (.leaf 595719048) (.leaf 583462793))) (.branch 103 (.branch 102 (.leaf 571468375) (.leaf 559729758)) (.branch 104 (.leaf 548241066) (.leaf 536996576))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 525990718) (.leaf 515218063)) (.branch 108 (.leaf 504673325) (.leaf 494351351))) (.branch 111 (.branch 110 (.leaf 484247123) (.leaf 474355748)) (.branch 112 (.leaf 464672458) (.leaf 455192604)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 445911655) (.leaf 436825191)) (.branch 116 (.leaf 427928903) (.leaf 419218586))) (.branch 119 (.branch 118 (.leaf 410690140) (.leaf 402339566)) (.branch 120 (.leaf 394162960) (.leaf 386156514)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1079).prefactor = (2620467953117103/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1079).cutoff/(generalMeanRows 1079).c)).2 =
    (9648798674591/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1079).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1079).q*(generalMeanRows 1079).c/2-2 = (3187/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable351.value]
  have hcontinuation : (generalMeanRows 1079).q*(generalMeanRows 1079).cutoff/2-2 = (797/377:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable356.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1079).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1079).criticalRate j.val*(generalMeanRows 1079).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1079).c*(generalMeanRows 1079).criticalPoint j.val)).2-
      (generalMeanRows 1079).J/2-(generalMeanRows 1079).error (generalMeanGrid j.val)+
      (generalMeanRows 1079).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1079).c)).2-
      (generalMeanRows 1079).J/2-(generalMeanRows 1079).error 4 := by
  have he : (generalMeanRows 1079).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1079) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1079)
    (generalMeanRows_prefactorDomain 1079) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1079

/-! Kernel-checked entropy margins for general spectral rectangle 1080. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1080
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5900341421) (.branch 2 (.leaf 5707497233) (.leaf 5522694783))) (.branch 5 (.branch 4 (.leaf 5345497596) (.leaf 5175499579)) (.branch 6 (.leaf 5012322354) (.leaf 4855612881)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4705041331) (.leaf 4560299183)) (.branch 10 (.leaf 4421097510) (.leaf 4287165437))) (.branch 13 (.branch 12 (.leaf 4158248743) (.leaf 4034108603)) (.branch 14 (.leaf 3914520437) (.leaf 3799272872))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3688166788) (.branch 17 (.leaf 3581014455) (.leaf 3477638737))) (.branch 20 (.branch 19 (.leaf 3377872366) (.leaf 3281557275)) (.branch 21 (.leaf 3188543987) (.leaf 3098691048)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3011864511) (.leaf 2927937451)) (.branch 25 (.leaf 2846789528) (.leaf 2768306570))) (.branch 28 (.branch 27 (.leaf 2692380199) (.leaf 2618907475)) (.branch 29 (.leaf 2547790569) (.leaf 2478936461)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2412256655) (.branch 32 (.leaf 2347666918) (.leaf 2285087032))) (.branch 35 (.branch 34 (.leaf 2224440568) (.leaf 2165654670)) (.branch 36 (.leaf 2108659854) (.leaf 2053389828)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1999781309) (.leaf 1947773864)) (.branch 40 (.leaf 1897309759) (.leaf 1848333809))) (.branch 43 (.branch 42 (.leaf 1800793248) (.leaf 1754637602)) (.branch 44 (.leaf 1709818568) (.leaf 1666289903))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1624007322) (.branch 47 (.leaf 1582928393) (.leaf 1543012451))) (.branch 50 (.branch 49 (.leaf 1504220503) (.leaf 1466515152)) (.branch 51 (.leaf 1429860515) (.leaf 1394222150)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1359566988) (.leaf 1325863265)) (.branch 55 (.leaf 1293080463) (.leaf 1261189250))) (.branch 58 (.branch 57 (.leaf 1230161425) (.leaf 1199969864)) (.branch 59 (.leaf 1170588472) (.leaf 1141992138))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1114156686) (.branch 62 (.leaf 1087058838) (.leaf 1060676169))) (.branch 65 (.branch 64 (.leaf 1034987073) (.leaf 1009970725)) (.branch 66 (.leaf 985607050) (.leaf 961876686)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 938760956) (.leaf 916241841)) (.branch 70 (.leaf 894301946) (.leaf 872924482))) (.branch 73 (.branch 72 (.leaf 852093233) (.leaf 831792537)) (.branch 74 (.leaf 812007263) (.leaf 792722786))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 773924972) (.branch 77 (.leaf 755600154) (.leaf 737735113))) (.branch 80 (.branch 79 (.leaf 720317064) (.leaf 703333637)) (.branch 81 (.leaf 686772860) (.leaf 670623145)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 654873272) (.leaf 639512375)) (.branch 85 (.leaf 624529932) (.leaf 609915747))) (.branch 88 (.branch 87 (.leaf 595659941) (.leaf 581752938)) (.branch 89 (.leaf 568185458) (.leaf 554948502)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 542033344) (.branch 92 (.leaf 529431519) (.leaf 517134816))) (.branch 95 (.branch 94 (.leaf 505135269) (.leaf 493425148)) (.branch 96 (.leaf 481996948) (.leaf 470843385)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 459957387) (.leaf 449332087)) (.branch 100 (.leaf 438960814) (.leaf 428837089))) (.branch 103 (.branch 102 (.leaf 418954618) (.leaf 409307284)) (.branch 104 (.leaf 399889145) (.leaf 390694424))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 381717505) (.leaf 372952928)) (.branch 108 (.leaf 364395387) (.leaf 356039718))) (.branch 111 (.branch 110 (.leaf 347880902) (.leaf 339914056)) (.branch 112 (.leaf 332134428) (.leaf 324537398)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 317118468) (.leaf 309873261)) (.branch 116 (.leaf 302797518) (.leaf 295887093))) (.branch 119 (.branch 118 (.leaf 289137951) (.leaf 282546161)) (.branch 120 (.leaf 276107900) (.leaf 269819440)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1080).prefactor = (5442810421700479/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1080).cutoff/(generalMeanRows 1080).c)).2 =
    (21947864431139/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1080).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1080).q*(generalMeanRows 1080).cutoff/2-2 = (797/377:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable356.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1080).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1080).criticalRate j.val*(generalMeanRows 1080).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1080).c*(generalMeanRows 1080).criticalPoint j.val)).2-
      (generalMeanRows 1080).J/2-(generalMeanRows 1080).error (generalMeanGrid j.val)+
      (generalMeanRows 1080).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1080).c)).2-
      (generalMeanRows 1080).J/2-(generalMeanRows 1080).error 4 := by
  have he : (generalMeanRows 1080).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1080) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1080)
    (generalMeanRows_prefactorDomain 1080) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1080

/-! Kernel-checked entropy margins for general spectral rectangle 1081. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1081
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6007640334) (.branch 2 (.leaf 5823401147) (.leaf 5646712361))) (.branch 5 (.branch 4 (.leaf 5477158538) (.leaf 5314353607)) (.branch 6 (.leaf 5157938273) (.leaf 5007577707)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4862959483) (.leaf 4723791727)) (.branch 10 (.leaf 4589801448) (.leaf 4460733038))) (.branch 13 (.branch 12 (.leaf 4336346918) (.leaf 4216418308)) (.branch 14 (.leaf 4100736111) (.leaf 3989101903))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3881329005) (.branch 17 (.leaf 3777241642) (.leaf 3676674171))) (.branch 20 (.branch 19 (.leaf 3579470379) (.leaf 3485482829)) (.branch 21 (.leaf 3394572271) (.leaf 3306607089)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3221462803) (.leaf 3139021599)) (.branch 25 (.leaf 3059171901) (.leaf 2981807978))) (.branch 28 (.branch 27 (.leaf 2906829569) (.leaf 2834141547)) (.branch 29 (.leaf 2763653606) (.leaf 2695279961)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2628939080) (.branch 32 (.leaf 2564553430) (.leaf 2502049241))) (.branch 35 (.branch 34 (.leaf 2441356286) (.leaf 2382407675)) (.branch 36 (.leaf 2325139665) (.leaf 2269491481)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2215405151) (.leaf 2162825346)) (.branch 40 (.leaf 2111699238) (.leaf 2061976359))) (.branch 43 (.branch 42 (.leaf 2013608478) (.leaf 1966549477)) (.branch 44 (.leaf 1920755239) (.leaf 1876183544))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1832793969) (.branch 47 (.leaf 1790547792) (.leaf 1749407909))) (.branch 50 (.branch 49 (.leaf 1709338748) (.leaf 1670306193)) (.branch 51 (.leaf 1632277509) (.leaf 1595221277)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1559107325) (.leaf 1523906669)) (.branch 55 (.leaf 1489591455) (.leaf 1456134905))) (.branch 58 (.branch 57 (.leaf 1423511265) (.leaf 1391695756)) (.branch 59 (.leaf 1360664531) (.leaf 1330394626))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1300863926) (.branch 62 (.leaf 1272051121) (.leaf 1243935671))) (.branch 65 (.branch 64 (.leaf 1216497774) (.leaf 1189718329)) (.branch 66 (.leaf 1163578905) (.leaf 1138061715)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1113149587) (.leaf 1088825935)) (.branch 70 (.leaf 1065074735) (.leaf 1041880503))) (.branch 73 (.branch 72 (.leaf 1019228269) (.leaf 997103560)) (.branch 74 (.leaf 975492375) (.leaf 954381168))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 933756829) (.branch 77 (.leaf 913606665) (.leaf 893918386))) (.branch 80 (.branch 79 (.leaf 874680088) (.leaf 855880238)) (.branch 81 (.leaf 837507656) (.leaf 819551508)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 802001288) (.leaf 784846805)) (.branch 85 (.leaf 768078175) (.leaf 751685807))) (.branch 88 (.branch 87 (.leaf 735660392) (.leaf 719992894)) (.branch 89 (.leaf 704674538) (.leaf 689696802)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 675051410) (.branch 92 (.leaf 660730319) (.leaf 646725713))) (.branch 95 (.branch 94 (.leaf 633029996) (.leaf 619635783)) (.branch 96 (.leaf 606535893) (.leaf 593723342)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 581191336) (.leaf 568933268)) (.branch 100 (.leaf 556942706) (.leaf 545213392))) (.branch 103 (.branch 102 (.leaf 533739234) (.leaf 522514302)) (.branch 104 (.leaf 511532819) (.leaf 500789164))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 490277860) (.leaf 479993570)) (.branch 108 (.leaf 469931096) (.leaf 460085374))) (.branch 111 (.branch 110 (.leaf 450451468) (.leaf 441024567)) (.branch 112 (.leaf 431799981) (.leaf 422773139)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 413939583) (.leaf 405294967)) (.branch 116 (.leaf 396835050) (.leaf 388555699))) (.branch 119 (.branch 118 (.leaf 380452880) (.leaf 372522659)) (.branch 120 (.leaf 364761196) (.leaf 357164745)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1081).prefactor = (81816922758559/15625000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1081).cutoff/(generalMeanRows 1081).c)).2 =
    (25115499223157/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1081).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1081).q*(generalMeanRows 1081).c/2-2 = (1311/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable357.value]
  have hcontinuation : (generalMeanRows 1081).q*(generalMeanRows 1081).cutoff/2-2 = (321/145:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable358.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1081).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1081).criticalRate j.val*(generalMeanRows 1081).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1081).c*(generalMeanRows 1081).criticalPoint j.val)).2-
      (generalMeanRows 1081).J/2-(generalMeanRows 1081).error (generalMeanGrid j.val)+
      (generalMeanRows 1081).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1081).c)).2-
      (generalMeanRows 1081).J/2-(generalMeanRows 1081).error 4 := by
  have he : (generalMeanRows 1081).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1081) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1081)
    (generalMeanRows_prefactorDomain 1081) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1081

/-! Kernel-checked entropy margins for general spectral rectangle 1082. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1082
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6222437499) (.branch 2 (.leaf 6031611024) (.leaf 5848604908))) (.branch 5 (.branch 4 (.leaf 5672988858) (.leaf 5504363000)) (.branch 6 (.leaf 5342355192) (.leaf 5186618634)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5036829731) (.leaf 4892686171)) (.branch 10 (.leaf 4753905203) (.leaf 4620222081))) (.branch 13 (.branch 12 (.leaf 4491388660) (.leaf 4367172123)) (.branch 14 (.leaf 4247353825) (.leaf 4131728248))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4020102038) (.branch 17 (.leaf 3912293135) (.leaf 3808129975))) (.branch 20 (.branch 19 (.leaf 3707450759) (.leaf 3610102778)) (.branch 21 (.leaf 3515941804) (.leaf 3424831515)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3336642980) (.leaf 3251254173)) (.branch 25 (.leaf 3168549530) (.leaf 3088419537))) (.branch 28 (.branch 27 (.leaf 3010760349) (.leaf 2935473441)) (.branch 29 (.leaf 2862465274) (.leaf 2791646997)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2722934164) (.branch 32 (.leaf 2656246470) (.leaf 2591507507))) (.branch 35 (.branch 34 (.leaf 2528644536) (.leaf 2467588276)) (.branch 36 (.leaf 2408272705) (.leaf 2350634877)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2294614744) (.leaf 2240155001)) (.branch 40 (.leaf 2187200930) (.leaf 2135700259))) (.branch 43 (.branch 42 (.leaf 2085603033) (.leaf 2036861484)) (.branch 44 (.leaf 1989429919) (.leaf 1943264608))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1898323682) (.branch 47 (.leaf 1854567036) (.leaf 1811956237))) (.branch 50 (.branch 49 (.leaf 1770454443) (.leaf 1730026318)) (.branch 51 (.leaf 1690637957) (.leaf 1652256816)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1614851646) (.leaf 1578392426)) (.branch 55 (.leaf 1542850306) (.leaf 1508197551))) (.branch 58 (.branch 57 (.leaf 1474407485) (.leaf 1441454445)) (.branch 59 (.leaf 1409313729) (.leaf 1377961554))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1347375013) (.branch 62 (.leaf 1317532035) (.leaf 1288411346))) (.branch 65 (.branch 64 (.leaf 1259992434) (.leaf 1232255516)) (.branch 66 (.leaf 1205181503) (.leaf 1178751973)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1152949136) (.leaf 1127755816)) (.branch 70 (.leaf 1103155416) (.leaf 1079131897))) (.branch 73 (.branch 72 (.leaf 1055669756) (.leaf 1032754000)) (.branch 74 (.leaf 1010370129) (.leaf 988504111))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 967142369) (.branch 77 (.leaf 946271756) (.leaf 925879543))) (.branch 80 (.branch 79 (.leaf 905953399) (.leaf 886481379)) (.branch 81 (.leaf 867451904) (.leaf 848853752)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 830676041) (.leaf 812908217)) (.branch 85 (.leaf 795540042) (.leaf 778561581))) (.branch 88 (.branch 87 (.leaf 761963193) (.leaf 745735519)) (.branch 89 (.leaf 729869470) (.leaf 714356221)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 699187198) (.branch 92 (.leaf 684354070) (.leaf 669848744))) (.branch 95 (.branch 94 (.leaf 655663350) (.leaf 641790240)) (.branch 96 (.leaf 628221976) (.leaf 614951325)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 601971251) (.leaf 589274908)) (.branch 100 (.leaf 576855635) (.leaf 564706951))) (.branch 103 (.branch 102 (.leaf 552822546) (.leaf 541196277)) (.branch 104 (.leaf 529822163) (.leaf 518694380))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 507807254) (.leaf 497155259)) (.branch 108 (.leaf 486733012) (.leaf 476535266))) (.branch 111 (.branch 110 (.leaf 466556909) (.leaf 456792959)) (.branch 112 (.leaf 447238557) (.leaf 437888970)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 428739579) (.leaf 419785882)) (.branch 116 (.leaf 411023490) (.leaf 402448119))) (.branch 119 (.branch 118 (.leaf 394055592) (.leaf 385841834)) (.branch 120 (.leaf 377802867) (.leaf 369934813)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1082).prefactor = (2711750557378687/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1082).cutoff/(generalMeanRows 1082).c)).2 =
    (25115499223157/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1082).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1082).q*(generalMeanRows 1082).c/2-2 = (1311/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable357.value]
  have hcontinuation : (generalMeanRows 1082).q*(generalMeanRows 1082).cutoff/2-2 = (321/145:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable358.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1082).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1082).criticalRate j.val*(generalMeanRows 1082).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1082).c*(generalMeanRows 1082).criticalPoint j.val)).2-
      (generalMeanRows 1082).J/2-(generalMeanRows 1082).error (generalMeanGrid j.val)+
      (generalMeanRows 1082).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1082).c)).2-
      (generalMeanRows 1082).J/2-(generalMeanRows 1082).error 4 := by
  have he : (generalMeanRows 1082).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1082) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1082)
    (generalMeanRows_prefactorDomain 1082) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1082

/-! Kernel-checked entropy margins for general spectral rectangle 1083. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1083
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6540215882) (.branch 2 (.leaf 6342181620) (.leaf 6152228787))) (.branch 5 (.branch 4 (.leaf 5969912350) (.leaf 5794818780)) (.branch 6 (.leaf 5626563269) (.leaf 5464787252)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5309156193) (.leaf 5159357592)) (.branch 10 (.leaf 5015099203) (.leaf 4876107420))) (.branch 13 (.branch 12 (.leaf 4742125821) (.leaf 4612913853)) (.branch 14 (.leaf 4488245631) (.leaf 4367908853))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4251703810) (.branch 17 (.leaf 4139442477) (.leaf 4030947689))) (.branch 20 (.branch 19 (.leaf 3926052385) (.leaf 3824598908)) (.branch 21 (.leaf 3726438370) (.leaf 3631430065)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3539440929) (.leaf 3450345037)) (.branch 25 (.leaf 3364023145) (.leaf 3280362267))) (.branch 28 (.branch 27 (.leaf 3199255274) (.leaf 3120600537)) (.branch 29 (.leaf 3044301580) (.leaf 2970266773)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2898409033) (.branch 32 (.leaf 2828645558) (.leaf 2760897572))) (.branch 35 (.branch 34 (.leaf 2695090088) (.leaf 2631151689)) (.branch 36 (.leaf 2569014323) (.leaf 2508613115)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2449886181) (.leaf 2392774468)) (.branch 40 (.leaf 2337221591) (.leaf 2283173694))) (.branch 43 (.branch 42 (.leaf 2230579304) (.leaf 2179389211)) (.branch 44 (.leaf 2129556340) (.leaf 2081035643))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2033783989) (.branch 47 (.leaf 1987760068) (.leaf 1942924293))) (.branch 50 (.branch 49 (.leaf 1899238714) (.leaf 1856666935)) (.branch 51 (.leaf 1815174033) (.leaf 1774726491)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1735292119) (.leaf 1696839998)) (.branch 55 (.leaf 1659340412) (.leaf 1622764793))) (.branch 58 (.branch 57 (.leaf 1587085663) (.leaf 1552276587)) (.branch 59 (.leaf 1518312119) (.leaf 1485167759))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1452819907) (.branch 62 (.leaf 1421245824) (.leaf 1390423591))) (.branch 65 (.branch 64 (.leaf 1360332071) (.leaf 1330950879)) (.branch 66 (.leaf 1302260340) (.leaf 1274241468)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1246875927) (.leaf 1220146008)) (.branch 70 (.leaf 1194034601) (.leaf 1168525168))) (.branch 73 (.branch 72 (.leaf 1143601721) (.leaf 1119248797)) (.branch 74 (.leaf 1095451437) (.leaf 1072195168))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1049465979) (.branch 77 (.leaf 1027250302) (.leaf 1005534998))) (.branch 80 (.branch 79 (.leaf 984307341) (.leaf 963554993)) (.branch 81 (.leaf 943266001) (.leaf 923428771)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 904032061) (.leaf 885064967)) (.branch 85 (.leaf 866516907) (.leaf 848377612))) (.branch 88 (.branch 87 (.leaf 830637114) (.leaf 813285733)) (.branch 89 (.leaf 796314067) (.leaf 779712987)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 763473619) (.branch 92 (.leaf 747587340) (.leaf 732045769))) (.branch 95 (.branch 94 (.leaf 716840758) (.leaf 701964383)) (.branch 96 (.leaf 687408937) (.leaf 673166922)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 659231046) (.leaf 645594208)) (.branch 100 (.leaf 632249501) (.leaf 619190197))) (.branch 103 (.branch 102 (.leaf 606409749) (.leaf 593901779)) (.branch 104 (.leaf 581660076) (.leaf 569678589))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 557951425) (.leaf 546472838)) (.branch 108 (.leaf 535237231) (.leaf 524239148))) (.branch 111 (.branch 110 (.leaf 513473270) (.leaf 502934412)) (.branch 112 (.leaf 492617516) (.leaf 482517653)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 472630012) (.leaf 462949902)) (.branch 116 (.leaf 453472747) (.leaf 444194080))) (.branch 119 (.branch 118 (.leaf 435109544) (.leaf 426214887)) (.branch 120 (.leaf 417505959) (.leaf 408978709)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1083).prefactor = (224696518687949/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1083).cutoff/(generalMeanRows 1083).c)).2 =
    (407628350486011/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1083).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1083).q*(generalMeanRows 1083).c/2-2 = (257/320:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable359.value]
  have hcontinuation : (generalMeanRows 1083).q*(generalMeanRows 1083).cutoff/2-2 = (321/145:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable358.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1083).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1083).criticalRate j.val*(generalMeanRows 1083).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1083).c*(generalMeanRows 1083).criticalPoint j.val)).2-
      (generalMeanRows 1083).J/2-(generalMeanRows 1083).error (generalMeanGrid j.val)+
      (generalMeanRows 1083).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1083).c)).2-
      (generalMeanRows 1083).J/2-(generalMeanRows 1083).error 4 := by
  have he : (generalMeanRows 1083).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1083) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1083)
    (generalMeanRows_prefactorDomain 1083) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1083

/-! Kernel-checked entropy margins for general spectral rectangle 1084. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1084
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6874487922) (.branch 2 (.leaf 6669006191) (.leaf 6471875095))) (.branch 5 (.branch 4 (.leaf 6282634335) (.leaf 6100856244)) (.branch 6 (.leaf 5926142900) (.leaf 5758123560)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5596452363) (.leaf 5440806266)) (.branch 10 (.leaf 5290883200) (.leaf 5146400393))) (.branch 13 (.branch 12 (.leaf 5007092863) (.leaf 4872712056)) (.branch 14 (.leaf 4743024603) (.leaf 4617811192))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4496865543) (.branch 17 (.leaf 4379993470) (.leaf 4267012025))) (.branch 20 (.branch 19 (.leaf 4157748711) (.leaf 4052040763)) (.branch 21 (.leaf 3949734487) (.leaf 3850684653)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3754753930) (.leaf 3661812376)) (.branch 25 (.leaf 3571736957) (.leaf 3484411103))) (.branch 28 (.branch 27 (.leaf 3399724308) (.leaf 3317571744)) (.branch 29 (.leaf 3237853912) (.leaf 3160476321)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3085349179) (.branch 32 (.leaf 3012387117) (.leaf 2941508922))) (.branch 35 (.branch 34 (.leaf 2872637299) (.leaf 2805698637)) (.branch 36 (.leaf 2740622802) (.leaf 2677342938)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2615795278) (.leaf 2555918977)) (.branch 40 (.leaf 2497655944) (.leaf 2440950696))) (.branch 43 (.branch 42 (.leaf 2385750212) (.leaf 2332003800)) (.branch 44 (.leaf 2279662976) (.leaf 2228681342))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2179014480) (.branch 47 (.leaf 2130619845) (.leaf 2083456673))) (.branch 50 (.branch 49 (.leaf 2037485885) (.leaf 1992670001)) (.branch 51 (.leaf 1948973064) (.leaf 1906360560)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1864799346) (.leaf 1824257584)) (.branch 55 (.leaf 1784704678) (.leaf 1746111212))) (.branch 58 (.branch 57 (.leaf 1708448894) (.leaf 1671690502)) (.branch 59 (.leaf 1635809836) (.leaf 1600781665))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1566581687) (.branch 62 (.leaf 1533186485) (.leaf 1500573483))) (.branch 65 (.branch 64 (.leaf 1468720914) (.leaf 1437607778)) (.branch 66 (.leaf 1407213811) (.leaf 1377519452)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1348505812) (.leaf 1320154643)) (.branch 70 (.leaf 1292448314) (.leaf 1265369782))) (.branch 73 (.branch 72 (.leaf 1238902569) (.leaf 1213030736)) (.branch 74 (.leaf 1187738862) (.leaf 1163012022))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1138835768) (.branch 77 (.leaf 1115196109) (.leaf 1092079492))) (.branch 80 (.branch 79 (.leaf 1069472784) (.leaf 1047363260)) (.branch 81 (.leaf 1025738579) (.leaf 1004586776)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 983896246) (.leaf 963655729)) (.branch 85 (.leaf 943854295) (.leaf 924481338))) (.branch 88 (.branch 87 (.leaf 905526557) (.leaf 886979951)) (.branch 89 (.leaf 868831801) (.leaf 851072667)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 833693375) (.branch 92 (.leaf 816685005) (.leaf 800038886))) (.branch 95 (.branch 94 (.leaf 783746585) (.leaf 767799902)) (.branch 96 (.leaf 752190856) (.leaf 736911684)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 721954830) (.leaf 707312938)) (.branch 100 (.leaf 692978848) (.leaf 678945586))) (.branch 103 (.branch 102 (.leaf 665206362) (.leaf 651754562)) (.branch 104 (.leaf 638583739) (.leaf 625687614))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 613060068) (.leaf 600695136)) (.branch 108 (.leaf 588587002) (.leaf 576729997))) (.branch 111 (.branch 110 (.leaf 565118592) (.leaf 553747396)) (.branch 112 (.leaf 542611149) (.leaf 531704721)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 521023106) (.leaf 510561421)) (.branch 116 (.leaf 500314900) (.leaf 490278889))) (.branch 119 (.branch 118 (.leaf 480448849) (.leaf 470820346)) (.branch 120 (.leaf 461389054) (.leaf 452150745)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1084).prefactor = (5818257943782877/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1084).cutoff/(generalMeanRows 1084).c)).2 =
    (413442320351431/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1084).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1084).q*(generalMeanRows 1084).cutoff/2-2 = (321/145:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable358.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1084).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1084).criticalRate j.val*(generalMeanRows 1084).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1084).c*(generalMeanRows 1084).criticalPoint j.val)).2-
      (generalMeanRows 1084).J/2-(generalMeanRows 1084).error (generalMeanGrid j.val)+
      (generalMeanRows 1084).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1084).c)).2-
      (generalMeanRows 1084).J/2-(generalMeanRows 1084).error 4 := by
  have he : (generalMeanRows 1084).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1084) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1084)
    (generalMeanRows_prefactorDomain 1084) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1084

/-! Kernel-checked entropy margins for general spectral rectangle 1085. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1085
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7333819304) (.branch 2 (.leaf 7120334494) (.leaf 6915456410))) (.branch 5 (.branch 4 (.leaf 6718709568) (.leaf 6529652285)) (.branch 6 (.leaf 6347873688) (.leaf 6172991053)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6004647422) (.leaf 5842509468)) (.branch 10 (.leaf 5686265571) (.leaf 5535624093))) (.branch 13 (.branch 12 (.leaf 5390311807) (.leaf 5250072486)) (.branch 14 (.leaf 5114665614) (.leaf 4983865223))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4857458821) (.branch 17 (.leaf 4735246424) (.leaf 4617039670))) (.branch 20 (.branch 19 (.leaf 4502661002) (.leaf 4391942920)) (.branch 21 (.leaf 4284727303) (.leaf 4180864772)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4080214110) (.leaf 3982641732)) (.branch 25 (.leaf 3888021182) (.leaf 3796232685))) (.branch 28 (.branch 27 (.leaf 3707162718) (.leaf 3620703620)) (.branch 29 (.leaf 3536753229) (.leaf 3455214547)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3375995421) (.branch 32 (.leaf 3299008257) (.leaf 3224169748))) (.branch 35 (.branch 34 (.leaf 3151400619) (.leaf 3080625393)) (.branch 36 (.leaf 3011772174) (.leaf 2944772436)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2879560838) (.leaf 2816075041)) (.branch 40 (.leaf 2754255543) (.leaf 2694045519))) (.branch 43 (.branch 42 (.leaf 2635390677) (.leaf 2578239120)) (.branch 44 (.leaf 2522541217) (.leaf 2468249481))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2415318455) (.branch 47 (.leaf 2363704610) (.leaf 2313366236))) (.branch 50 (.branch 49 (.leaf 2264263358) (.leaf 2216357640)) (.branch 51 (.leaf 2169612302) (.leaf 2123992048)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2079462985) (.leaf 2035992554)) (.branch 55 (.leaf 1993549470) (.leaf 1952103654))) (.branch 58 (.branch 57 (.leaf 1911626177) (.leaf 1872089205)) (.branch 59 (.leaf 1833465947) (.leaf 1795730605))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1758858328) (.branch 62 (.leaf 1722825167) (.leaf 1687608038))) (.branch 65 (.branch 64 (.leaf 1653184675) (.leaf 1619533600)) (.branch 66 (.leaf 1586634084) (.leaf 1554466113)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1523010360) (.leaf 1492248152)) (.branch 70 (.leaf 1462161442) (.leaf 1432732785))) (.branch 73 (.branch 72 (.leaf 1403945308) (.leaf 1375782688)) (.branch 74 (.leaf 1348229129) (.leaf 1321269342))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1294888519) (.branch 77 (.leaf 1269072320) (.leaf 1243806847))) (.branch 80 (.branch 79 (.leaf 1219078634) (.leaf 1194874623)) (.branch 81 (.leaf 1171182152) (.leaf 1147988938)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1125283064) (.leaf 1103052962)) (.branch 85 (.leaf 1081287404) (.leaf 1059975484))) (.branch 88 (.branch 87 (.leaf 1039106611) (.leaf 1018670495)) (.branch 89 (.leaf 998657136) (.leaf 979056812)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 959860075) (.branch 92 (.leaf 941057732) (.leaf 922640845))) (.branch 95 (.branch 94 (.leaf 904600717) (.leaf 886928884)) (.branch 96 (.leaf 869617109) (.leaf 852657373)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 836041867) (.leaf 819762986)) (.branch 100 (.leaf 803813325) (.leaf 788185665))) (.branch 103 (.branch 102 (.leaf 772872975) (.leaf 757868400)) (.branch 104 (.leaf 743165261) (.leaf 728757044))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 714637397) (.leaf 700800126)) (.branch 108 (.leaf 687239190) (.leaf 673948695))) (.branch 111 (.branch 110 (.leaf 660922890) (.leaf 648156162)) (.branch 112 (.leaf 635643035) (.leaf 623378163)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 611356326) (.leaf 599572427)) (.branch 116 (.leaf 588021492) (.leaf 576698659))) (.branch 119 (.branch 118 (.leaf 565599182) (.leaf 554718425)) (.branch 120 (.leaf 544051857) (.leaf 533595052)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1085).prefactor = (3013141965711117/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1085).cutoff/(generalMeanRows 1085).c)).2 =
    (10629316503423/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1085).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1085).q*(generalMeanRows 1085).cutoff/2-2 = (321/145:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable358.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1085).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1085).criticalRate j.val*(generalMeanRows 1085).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1085).c*(generalMeanRows 1085).criticalPoint j.val)).2-
      (generalMeanRows 1085).J/2-(generalMeanRows 1085).error (generalMeanGrid j.val)+
      (generalMeanRows 1085).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1085).c)).2-
      (generalMeanRows 1085).J/2-(generalMeanRows 1085).error 4 := by
  have he : (generalMeanRows 1085).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1085) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1085)
    (generalMeanRows_prefactorDomain 1085) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1085

/-! Kernel-checked entropy margins for general spectral rectangle 1086. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1086
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7709536751) (.branch 2 (.leaf 7488135642) (.leaf 7275626205))) (.branch 5 (.branch 4 (.leaf 7071516577) (.leaf 6875349904)) (.branch 6 (.leaf 6686701255) (.leaf 6505174850)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6330401600) (.leaf 6162036887)) (.branch 10 (.leaf 5999758577) (.leaf 5843265226))) (.branch 13 (.branch 12 (.leaf 5692274456) (.leaf 5546521490)) (.branch 14 (.leaf 5405757821) (.leaf 5269749997))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5138278521) (.branch 17 (.leaf 5011136845) (.leaf 4888130443))) (.branch 20 (.branch 19 (.leaf 4769075977) (.leaf 4653800517)) (.branch 21 (.leaf 4542140834) (.leaf 4433942745)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4329060515) (.leaf 4227356298)) (.branch 25 (.leaf 4128699626) (.leaf 4032966938))) (.branch 28 (.branch 27 (.leaf 3940041139) (.leaf 3849811198)) (.branch 29 (.leaf 3762171764) (.leaf 3677022828)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3594269387) (.branch 32 (.leaf 3513821151) (.leaf 3435592258))) (.branch 35 (.branch 34 (.leaf 3359501014) (.leaf 3285469648)) (.branch 36 (.leaf 3213424085) (.leaf 3143293735)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3075011294) (.leaf 3008512559)) (.branch 40 (.leaf 2943736252) (.leaf 2880623863))) (.branch 43 (.branch 42 (.leaf 2819119493) (.leaf 2759169716)) (.branch 44 (.leaf 2700723441) (.leaf 2643731790))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2588147981) (.branch 47 (.leaf 2533927214) (.leaf 2481026572))) (.branch 50 (.branch 49 (.leaf 2429404920) (.leaf 2379022815)) (.branch 51 (.leaf 2329842418) (.leaf 2281827417)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2234942945) (.leaf 2189155512)) (.branch 55 (.leaf 2144432936) (.leaf 2100744280))) (.branch 58 (.branch 57 (.leaf 2058059787) (.leaf 2016350831)) (.branch 59 (.leaf 1975589856) (.leaf 1935750329))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1896806692) (.branch 62 (.leaf 1858734312) (.leaf 1821509448))) (.branch 65 (.branch 64 (.leaf 1785109198) (.leaf 1749511471)) (.branch 66 (.leaf 1714694945) (.leaf 1680639035)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1647323859) (.leaf 1614730208)) (.branch 70 (.leaf 1582839517) (.leaf 1551633835))) (.branch 73 (.branch 72 (.leaf 1521095803) (.leaf 1491208625)) (.branch 74 (.leaf 1461956045) (.leaf 1433322327))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1405292232) (.branch 77 (.leaf 1377850995) (.leaf 1350984311))) (.branch 80 (.branch 79 (.leaf 1324678314) (.leaf 1298919556)) (.branch 81 (.leaf 1273694999) (.leaf 1248991989)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1224798250) (.leaf 1201101864)) (.branch 85 (.leaf 1177891257) (.leaf 1155155192))) (.branch 88 (.branch 87 (.leaf 1132882749) (.leaf 1111063319)) (.branch 89 (.leaf 1089686589) (.leaf 1068742534)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1048221404) (.branch 92 (.leaf 1028113715) (.leaf 1008410243))) (.branch 95 (.branch 94 (.leaf 989102008) (.leaf 970180273)) (.branch 96 (.leaf 951636531) (.leaf 933462498)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 915650107) (.leaf 898191498)) (.branch 100 (.leaf 881079015) (.leaf 864305196))) (.branch 103 (.branch 102 (.leaf 847862768) (.leaf 831744641)) (.branch 104 (.leaf 815943903) (.leaf 800453811))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 785267790) (.leaf 770379426)) (.branch 108 (.leaf 755782460) (.leaf 741470786))) (.branch 111 (.branch 110 (.leaf 727438441) (.leaf 713679610)) (.branch 112 (.leaf 700188610) (.leaf 686959896)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 673988053) (.leaf 661267790)) (.branch 116 (.leaf 648793941) (.leaf 636561458))) (.branch 119 (.branch 118 (.leaf 624565410) (.leaf 612800976)) (.branch 120 (.leaf 601263449) (.leaf 589948225)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1086).prefactor = (195054614999299/31250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1086).cutoff/(generalMeanRows 1086).c)).2 =
    (43108983716501/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1086).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1086).q*(generalMeanRows 1086).c/2-2 = (1181/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable360.value]
  have hcontinuation : (generalMeanRows 1086).q*(generalMeanRows 1086).cutoff/2-2 = (321/145:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable358.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1086).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1086).criticalRate j.val*(generalMeanRows 1086).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1086).c*(generalMeanRows 1086).criticalPoint j.val)).2-
      (generalMeanRows 1086).J/2-(generalMeanRows 1086).error (generalMeanGrid j.val)+
      (generalMeanRows 1086).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1086).c)).2-
      (generalMeanRows 1086).J/2-(generalMeanRows 1086).error 4 := by
  have he : (generalMeanRows 1086).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1086) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1086)
    (generalMeanRows_prefactorDomain 1086) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1086

/-! Kernel-checked entropy margins for general spectral rectangle 1087. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1087
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7025929247) (.branch 2 (.leaf 6822565690) (.leaf 6627167275))) (.branch 5 (.branch 4 (.leaf 6439312956) (.leaf 6258610807)) (.branch 6 (.leaf 6084695439) (.leaf 5917225708)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5755882667) (.leaf 5600367734)) (.branch 10 (.leaf 5450401050) (.leaf 5305720002))) (.branch 13 (.branch 12 (.leaf 5166077885) (.leaf 5031242699)) (.branch 14 (.leaf 4900996056) (.leaf 4775132185))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4653457029) (.branch 17 (.leaf 4535787423) (.leaf 4421950335))) (.branch 20 (.branch 19 (.leaf 4311782182) (.leaf 4205128194)) (.branch 21 (.leaf 4101841833) (.leaf 4001784259)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3904823838) (.leaf 3810835685)) (.branch 25 (.leaf 3719701246) (.leaf 3631307909))) (.branch 28 (.branch 27 (.leaf 3545548643) (.leaf 3462321663)) (.branch 29 (.leaf 3381530122) (.leaf 3303081822)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3226888943) (.branch 32 (.leaf 3152867796) (.leaf 3080938590))) (.branch 35 (.branch 34 (.leaf 3011025210) (.leaf 2943055018)) (.branch 36 (.leaf 2876958663) (.leaf 2812669898)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2750125420) (.leaf 2689264707)) (.branch 40 (.leaf 2630029879) (.leaf 2572365553))) (.branch 43 (.branch 42 (.leaf 2516218719) (.leaf 2461538615)) (.branch 44 (.leaf 2408276616) (.leaf 2356386125))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2305822469) (.branch 47 (.leaf 2256542810) (.leaf 2208506048))) (.branch 50 (.branch 49 (.leaf 2161672742) (.leaf 2116005027)) (.branch 51 (.leaf 2071466536) (.leaf 2028022336)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1985638853) (.leaf 1944283810)) (.branch 55 (.leaf 1903926171) (.leaf 1864536078))) (.branch 58 (.branch 57 (.leaf 1826084800) (.leaf 1788544682)) (.branch 59 (.leaf 1751889094) (.leaf 1716092388))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1681129852) (.branch 62 (.leaf 1646977669) (.leaf 1613612880))) (.branch 65 (.branch 64 (.leaf 1581013342) (.leaf 1549157697)) (.branch 66 (.leaf 1518025336) (.leaf 1487596369)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1457851591) (.leaf 1428772457)) (.branch 70 (.leaf 1400341051) (.leaf 1372540063))) (.branch 73 (.branch 72 (.leaf 1345352762) (.leaf 1318762971)) (.branch 74 (.leaf 1292755050) (.leaf 1267313868))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1242424784) (.branch 77 (.leaf 1218073630) (.leaf 1194246693))) (.branch 80 (.branch 79 (.leaf 1170930690) (.leaf 1148112760)) (.branch 81 (.leaf 1125780442) (.leaf 1103921662)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1082524717) (.leaf 1061578262)) (.branch 85 (.leaf 1041071295) (.leaf 1020993146))) (.branch 88 (.branch 87 (.leaf 1001333463) (.leaf 982082201)) (.branch 89 (.leaf 963229611) (.leaf 944766228)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 926682863) (.branch 92 (.leaf 908970590) (.leaf 891620740))) (.branch 95 (.branch 94 (.leaf 874624888) (.leaf 857974848)) (.branch 96 (.leaf 841662663) (.leaf 825680598)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 810021129) (.leaf 794676941)) (.branch 100 (.leaf 779640918) (.leaf 764906135))) (.branch 103 (.branch 102 (.leaf 750465853) (.leaf 736313516)) (.branch 104 (.leaf 722442738) (.leaf 708847304))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 695521160) (.leaf 682458411)) (.branch 108 (.leaf 669653314) (.leaf 657100272))) (.branch 111 (.branch 110 (.leaf 644793834) (.leaf 632728684)) (.branch 112 (.leaf 620899643) (.leaf 609301660)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 597929811) (.leaf 586779293)) (.branch 116 (.leaf 575845421) (.leaf 565123628))) (.branch 119 (.branch 118 (.leaf 554609455) (.leaf 544298552)) (.branch 120 (.leaf 534186673) (.leaf 524269676)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1087).prefactor = (2677637476739247/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1087).cutoff/(generalMeanRows 1087).c)).2 =
    (176214326528649/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1087).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1087).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1087).criticalRate j.val*(generalMeanRows 1087).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1087).c*(generalMeanRows 1087).criticalPoint j.val)).2-
      (generalMeanRows 1087).J/2-(generalMeanRows 1087).error (generalMeanGrid j.val)+
      (generalMeanRows 1087).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1087).c)).2-
      (generalMeanRows 1087).J/2-(generalMeanRows 1087).error 4 := by
  have he : (generalMeanRows 1087).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1087) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1087)
    (generalMeanRows_prefactorDomain 1087) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1087

/-! Kernel-checked entropy margins for general spectral rectangle 1088. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1088
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6650906070) (.branch 2 (.leaf 6459169355) (.leaf 6274989246))) (.branch 5 (.branch 4 (.leaf 6097961777) (.leaf 5927711093)) (.branch 6 (.leaf 5763886960) (.leaf 5606162557)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5454232499) (.leaf 5307811068)) (.branch 10 (.leaf 5166630627) (.leaf 5030440187))) (.branch 13 (.branch 12 (.leaf 4899004120) (.leaf 4772100991)) (.branch 14 (.leaf 4649522501) (.leaf 4531072521))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4416566223) (.branch 17 (.leaf 4305829273) (.leaf 4198697109))) (.branch 20 (.branch 19 (.leaf 4095014267) (.leaf 3994633766)) (.branch 21 (.leaf 3897416552) (.leaf 3803230971)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3711952297) (.leaf 3623462287)) (.branch 25 (.leaf 3537648778) (.leaf 3454405306))) (.branch 28 (.branch 27 (.leaf 3373630759) (.leaf 3295229051)) (.branch 29 (.leaf 3219108826) (.leaf 3145183172)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3073369368) (.branch 32 (.leaf 3003588637) (.leaf 2935765919))) (.branch 35 (.branch 34 (.leaf 2869829668) (.leaf 2805711647)) (.branch 36 (.leaf 2743346750) (.leaf 2682672824)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2623630517) (.leaf 2566163118)) (.branch 40 (.leaf 2510216422) (.leaf 2455738594))) (.branch 43 (.branch 42 (.leaf 2402680047) (.leaf 2350993321)) (.branch 44 (.leaf 2300632981) (.leaf 2251555503))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2203719186) (.branch 47 (.leaf 2157084056) (.leaf 2111611781))) (.branch 50 (.branch 49 (.leaf 2067265589) (.leaf 2024010191)) (.branch 51 (.leaf 1981811710) (.leaf 1940637612)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1900456642) (.leaf 1861238763)) (.branch 55 (.leaf 1822955096) (.leaf 1785577871))) (.branch 58 (.branch 57 (.leaf 1749080370) (.leaf 1713436880)) (.branch 59 (.leaf 1678622650) (.leaf 1644613841))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1611387492) (.branch 62 (.leaf 1578921475) (.leaf 1547194459))) (.branch 65 (.branch 64 (.leaf 1516185877) (.leaf 1485875890)) (.branch 66 (.leaf 1456245357) (.leaf 1427275804)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1398949394) (.leaf 1371248902)) (.branch 70 (.leaf 1344157688) (.leaf 1317659674))) (.branch 73 (.branch 72 (.leaf 1291739317) (.leaf 1266381589)) (.branch 74 (.leaf 1241571958) (.leaf 1217296363))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1193541199) (.branch 77 (.leaf 1170293296) (.leaf 1147539903))) (.branch 80 (.branch 79 (.leaf 1125268670) (.leaf 1103467636)) (.branch 81 (.leaf 1082125208) (.leaf 1061230150)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1040771571) (.leaf 1020738908)) (.branch 85 (.leaf 1001121916) (.leaf 981910654))) (.branch 88 (.branch 87 (.leaf 963095477) (.leaf 944667021)) (.branch 89 (.leaf 926616197) (.leaf 908934175)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 891612382) (.branch 92 (.leaf 874642486) (.leaf 858016391))) (.branch 95 (.branch 94 (.leaf 841726229) (.leaf 825764349)) (.branch 96 (.leaf 810123314) (.leaf 794795887)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 779775032) (.leaf 765053900)) (.branch 100 (.leaf 750625828) (.leaf 736484329))) (.branch 103 (.branch 102 (.leaf 722623089) (.leaf 709035957)) (.branch 104 (.leaf 695716947) (.leaf 682660225))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 669860108) (.leaf 657311058)) (.branch 108 (.leaf 645007678) (.leaf 632944710))) (.branch 111 (.branch 110 (.leaf 621117022) (.leaf 609519617)) (.branch 112 (.leaf 598147616) (.leaf 586996263)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 576060919) (.leaf 565337056)) (.branch 116 (.leaf 554820258) (.leaf 544506213))) (.branch 119 (.branch 118 (.leaf 534390713) (.leaf 524469650)) (.branch 120 (.leaf 514739014) (.leaf 505194889)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1088).prefactor = (1027598602802119/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1088).cutoff/(generalMeanRows 1088).c)).2 =
    (373292110692207/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1088).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1088).q*(generalMeanRows 1088).cutoff/2-2 = (3112/1593:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable361.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1088).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1088).criticalRate j.val*(generalMeanRows 1088).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1088).c*(generalMeanRows 1088).criticalPoint j.val)).2-
      (generalMeanRows 1088).J/2-(generalMeanRows 1088).error (generalMeanGrid j.val)+
      (generalMeanRows 1088).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1088).c)).2-
      (generalMeanRows 1088).J/2-(generalMeanRows 1088).error 4 := by
  have he : (generalMeanRows 1088).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1088) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1088)
    (generalMeanRows_prefactorDomain 1088) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1088

/-! Kernel-checked entropy margins for general spectral rectangle 1089. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1089
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6673079538) (.branch 2 (.leaf 6472991610) (.leaf 6280879792))) (.branch 5 (.branch 4 (.leaf 6096319019) (.leaf 5918913689)) (.branch 6 (.leaf 5748295063) (.leaf 5584118944)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5426063612) (.leaf 5273827973)) (.branch 10 (.leaf 5127129902) (.leaf 4985704736))) (.branch 13 (.branch 12 (.leaf 4849303935) (.leaf 4717693852)) (.branch 14 (.leaf 4590654629) (.leaf 4467979191))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4349472325) (.branch 17 (.leaf 4234949847) (.leaf 4124237834))) (.branch 20 (.branch 19 (.leaf 4017171929) (.leaf 3913596692)) (.branch 21 (.leaf 3813365013) (.leaf 3716337571)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3622382328) (.leaf 3531374073)) (.branch 25 (.leaf 3443193988) (.leaf 3357729260))) (.branch 28 (.branch 27 (.leaf 3274872713) (.leaf 3194522463)) (.branch 29 (.leaf 3116581612) (.leaf 3040957948)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2967563676) (.branch 32 (.leaf 2896315161) (.leaf 2827132694))) (.branch 35 (.branch 34 (.leaf 2759940271) (.leaf 2694665384)) (.branch 36 (.leaf 2631238831) (.leaf 2569594533)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2509669369) (.leaf 2451403012)) (.branch 40 (.leaf 2394737785) (.leaf 2339618521))) (.branch 43 (.branch 42 (.leaf 2285992430) (.leaf 2233808978)) (.branch 44 (.leaf 2183019773) (.leaf 2133578452))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2085440583) (.branch 47 (.leaf 2038563565) (.leaf 1992906541))) (.branch 50 (.branch 49 (.leaf 1948430310) (.leaf 1905097245)) (.branch 51 (.leaf 1862871222) (.leaf 1821717541)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1781602865) (.leaf 1742495151)) (.branch 55 (.leaf 1704363590) (.leaf 1667178551))) (.branch 58 (.branch 57 (.leaf 1630911527) (.leaf 1595535082)) (.branch 59 (.leaf 1561022801) (.leaf 1527349249))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1494489920) (.branch 62 (.leaf 1462421203) (.leaf 1431120336))) (.branch 65 (.branch 64 (.leaf 1400565374) (.leaf 1370735149)) (.branch 66 (.leaf 1341609241) (.leaf 1313167940)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1285392223) (.leaf 1258263719)) (.branch 70 (.leaf 1231764683) (.leaf 1205877973))) (.branch 73 (.branch 72 (.leaf 1180587021) (.leaf 1155875811)) (.branch 74 (.leaf 1131728858) (.leaf 1108131184))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1085068299) (.branch 77 (.leaf 1062526181) (.leaf 1040491258))) (.branch 80 (.branch 79 (.leaf 1018950389) (.leaf 997890850)) (.branch 81 (.leaf 977300315) (.leaf 957166839)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 937478851) (.leaf 918225130)) (.branch 85 (.leaf 899394801) (.leaf 880977313))) (.branch 88 (.branch 87 (.leaf 862962435) (.leaf 845340240)) (.branch 89 (.leaf 828101094) (.leaf 811235647)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 794734821) (.branch 92 (.leaf 778589800) (.leaf 762792025))) (.branch 95 (.branch 94 (.leaf 747333179) (.leaf 732205180)) (.branch 96 (.leaf 717400177) (.leaf 702910537)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 688728841) (.leaf 674847872)) (.branch 100 (.leaf 661260615) (.leaf 647960245))) (.branch 103 (.branch 102 (.leaf 634940121) (.leaf 622193784)) (.branch 104 (.leaf 609714944) (.leaf 597497484))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 585535443) (.leaf 573823023)) (.branch 108 (.leaf 562354572) (.leaf 551124590))) (.branch 111 (.branch 110 (.leaf 540127715) (.leaf 529358728)) (.branch 112 (.leaf 518812539) (.leaf 508484189)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 498368846) (.leaf 488461799)) (.branch 116 (.leaf 478758454) (.leaf 469254333))) (.branch 119 (.branch 118 (.leaf 459945068) (.leaf 450826398)) (.branch 120 (.leaf 441894170) (.leaf 433144329)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1089).prefactor = (673161881210051/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1089).cutoff/(generalMeanRows 1089).c)).2 =
    (177499458822441/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1089).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1089).q*(generalMeanRows 1089).c/2-2 = (6177/8000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable342.value]
  have hcontinuation : (generalMeanRows 1089).q*(generalMeanRows 1089).cutoff/2-2 = (3112/1593:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable361.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1089).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1089).criticalRate j.val*(generalMeanRows 1089).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1089).c*(generalMeanRows 1089).criticalPoint j.val)).2-
      (generalMeanRows 1089).J/2-(generalMeanRows 1089).error (generalMeanGrid j.val)+
      (generalMeanRows 1089).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1089).c)).2-
      (generalMeanRows 1089).J/2-(generalMeanRows 1089).error 4 := by
  have he : (generalMeanRows 1089).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1089) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1089)
    (generalMeanRows_prefactorDomain 1089) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1089

/-! Kernel-checked entropy margins for general spectral rectangle 1090. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1090
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6467129869) (.branch 2 (.leaf 6278152250) (.leaf 6096701227))) (.branch 5 (.branch 4 (.leaf 5922370381) (.leaf 5754781730)) (.branch 6 (.leaf 5593583222) (.leaf 5438446493)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5289064872) (.leaf 5145151591)) (.branch 10 (.leaf 5006438173) (.leaf 4872672988))) (.branch 13 (.branch 12 (.leaf 4743619942) (.leaf 4619057295)) (.branch 14 (.leaf 4498776588) (.leaf 4382581661))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4270287773) (.branch 17 (.leaf 4161720785) (.leaf 4056716417))) (.branch 20 (.branch 19 (.leaf 3955119576) (.leaf 3856783722)) (.branch 21 (.leaf 3761570308) (.leaf 3669348242)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3579993410) (.leaf 3493388222)) (.branch 25 (.leaf 3409421204) (.leaf 3327986609))) (.branch 28 (.branch 27 (.leaf 3248984070) (.leaf 3172318264)) (.branch 29 (.leaf 3097898612) (.leaf 3025638993)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2955457483) (.branch 32 (.leaf 2887276106) (.leaf 2821020609))) (.branch 35 (.branch 34 (.leaf 2756620248) (.leaf 2694007587)) (.branch 36 (.leaf 2633118313) (.leaf 2573891064)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2516267264) (.leaf 2460190974)) (.branch 40 (.leaf 2405608744) (.leaf 2352469485))) (.branch 43 (.branch 42 (.leaf 2300724342) (.leaf 2250326572)) (.branch 44 (.leaf 2201231442) (.leaf 2153396116))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2106779562) (.branch 47 (.leaf 2061342462) (.leaf 2017047121))) (.branch 50 (.branch 49 (.leaf 1973857387) (.leaf 1931738576)) (.branch 51 (.leaf 1890657399) (.leaf 1850581890)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1811481348) (.leaf 1773326271)) (.branch 55 (.leaf 1736088301) (.leaf 1699740169))) (.branch 58 (.branch 57 (.leaf 1664255643) (.leaf 1629609483)) (.branch 59 (.leaf 1595777389) (.leaf 1562735964))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1530462667) (.branch 62 (.leaf 1498935781) (.leaf 1468134367))) (.branch 65 (.branch 64 (.leaf 1438038239) (.leaf 1408627923)) (.branch 66 (.leaf 1379884630) (.leaf 1351790224)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1324327194) (.leaf 1297478630)) (.branch 70 (.leaf 1271228192) (.leaf 1245560090))) (.branch 73 (.branch 72 (.leaf 1220459061) (.leaf 1195910345)) (.branch 74 (.leaf 1171899664) (.leaf 1148413204))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1125437596) (.branch 77 (.leaf 1102959896) (.leaf 1080967572))) (.branch 80 (.branch 79 (.leaf 1059448481) (.leaf 1038390862)) (.branch 81 (.leaf 1017783313) (.leaf 997614783)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 977874556) (.leaf 958552237)) (.branch 85 (.leaf 939637743) (.leaf 921121288))) (.branch 88 (.branch 87 (.leaf 902993375) (.leaf 885244782)) (.branch 89 (.leaf 867866556) (.leaf 850849998)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 834186660) (.branch 92 (.leaf 817868329) (.leaf 801887024))) (.branch 95 (.branch 94 (.leaf 786234988) (.leaf 770904675)) (.branch 96 (.leaf 755888749) (.leaf 741180070)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 726771696) (.leaf 712656866)) (.branch 100 (.leaf 698829004) (.leaf 685281706))) (.branch 103 (.branch 102 (.leaf 672008735) (.leaf 659004019)) (.branch 104 (.leaf 646261643) (.leaf 633775845))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 621541009) (.leaf 609551663)) (.branch 108 (.leaf 597802475) (.leaf 586288244))) (.branch 111 (.branch 110 (.leaf 575003900) (.leaf 563944500)) (.branch 112 (.leaf 553105223) (.leaf 542481365)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 532068337) (.leaf 521861664)) (.branch 116 (.leaf 511856974) (.leaf 502050006))) (.branch 119 (.branch 118 (.leaf 492436596) (.leaf 483012682)) (.branch 120 (.leaf 473774295) (.leaf 464717563)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1090).prefactor = (645695299926601/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1090).cutoff/(generalMeanRows 1090).c)).2 =
    (386715131024349/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1090).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1090).q*(generalMeanRows 1090).c/2-2 = (2989/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable352.value]
  have hcontinuation : (generalMeanRows 1090).q*(generalMeanRows 1090).cutoff/2-2 = (1568/767:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable362.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1090).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1090).criticalRate j.val*(generalMeanRows 1090).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1090).c*(generalMeanRows 1090).criticalPoint j.val)).2-
      (generalMeanRows 1090).J/2-(generalMeanRows 1090).error (generalMeanGrid j.val)+
      (generalMeanRows 1090).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1090).c)).2-
      (generalMeanRows 1090).J/2-(generalMeanRows 1090).error 4 := by
  have he : (generalMeanRows 1090).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1090) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1090)
    (generalMeanRows_prefactorDomain 1090) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1090

/-! Kernel-checked entropy margins for general spectral rectangle 1091. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1091
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6462557555) (.branch 2 (.leaf 6266246096) (.leaf 6077847105))) (.branch 5 (.branch 4 (.leaf 5896934553) (.leaf 5723112105)) (.branch 6 (.leaf 5556010497) (.leaf 5395285210)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5240614379) (.leaf 5091696934)) (.branch 10 (.leaf 4948250920) (.leaf 4810011988))) (.branch 13 (.branch 12 (.leaf 4676732029) (.leaf 4548177944)) (.branch 14 (.leaf 4424130520) (.leaf 4304383414))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4188742226) (.branch 17 (.leaf 4077023651) (.leaf 3969054710))) (.branch 20 (.branch 19 (.leaf 3864672036) (.leaf 3763721225)) (.branch 21 (.leaf 3666056242) (.leaf 3571538868)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3480038194) (.leaf 3391430157)) (.branch 25 (.leaf 3305597103) (.leaf 3222427390))) (.branch 28 (.branch 27 (.leaf 3141815018) (.leaf 3063659286)) (.branch 29 (.leaf 2987864474) (.leaf 2914339543)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2842997867) (.branch 32 (.leaf 2773756969) (.leaf 2706538286))) (.branch 35 (.branch 34 (.leaf 2641266946) (.leaf 2577871561)) (.branch 36 (.leaf 2516284028) (.leaf 2456439354)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2398275479) (.leaf 2341733122)) (.branch 40 (.leaf 2286755629) (.leaf 2233288834))) (.branch 43 (.branch 42 (.leaf 2181280928) (.leaf 2130682335)) (.branch 44 (.leaf 2081445596) (.leaf 2033525261))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1986877785) (.branch 47 (.leaf 1941461436) (.leaf 1897236196))) (.branch 50 (.branch 49 (.leaf 1854163685) (.leaf 1812207073)) (.branch 51 (.leaf 1771331007) (.leaf 1731501542)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1692686068) (.leaf 1654853248)) (.branch 55 (.leaf 1617972960) (.leaf 1582016237))) (.branch 58 (.branch 57 (.leaf 1546955215) (.leaf 1512763080)) (.branch 59 (.leaf 1479414021) (.leaf 1446883185))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1415146632) (.branch 62 (.leaf 1384181294) (.leaf 1353964939))) (.branch 65 (.branch 64 (.leaf 1324476128) (.leaf 1295694187)) (.branch 66 (.leaf 1267599171) (.leaf 1240171829)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1213393580) (.leaf 1187246481)) (.branch 70 (.leaf 1161713200) (.leaf 1136776993))) (.branch 73 (.branch 72 (.leaf 1112421676) (.leaf 1088631604)) (.branch 74 (.leaf 1065391649) (.leaf 1042687177))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1020504032) (.branch 77 (.leaf 998828511) (.leaf 977647351))) (.branch 80 (.branch 79 (.leaf 956947710) (.leaf 936717151)) (.branch 81 (.leaf 916943624) (.leaf 897615453)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 878721323) (.leaf 860250263)) (.branch 85 (.leaf 842191635) (.leaf 824535123))) (.branch 88 (.branch 87 (.leaf 807270716) (.leaf 790388703)) (.branch 89 (.leaf 773879657) (.leaf 757734429)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 741944133) (.branch 92 (.leaf 726500142) (.leaf 711394074))) (.branch 95 (.branch 94 (.leaf 696617788) (.leaf 682163370)) (.branch 96 (.leaf 668023131) (.leaf 654189595)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 640655494) (.leaf 627413760)) (.branch 100 (.leaf 614457518) (.leaf 601780080))) (.branch 103 (.branch 102 (.leaf 589374941) (.leaf 577235767)) (.branch 104 (.leaf 565356396) (.leaf 553730829))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 542353225) (.leaf 531217897)) (.branch 108 (.leaf 520319306) (.leaf 509652058))) (.branch 111 (.branch 110 (.leaf 499210896) (.leaf 488990699)) (.branch 112 (.leaf 478986479) (.leaf 469193372)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 459606638) (.leaf 450221656)) (.branch 116 (.leaf 441033921) (.leaf 432039042))) (.branch 119 (.branch 118 (.leaf 423232733) (.leaf 414610817)) (.branch 120 (.leaf 406169218) (.leaf 397903962)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1091).prefactor = (5392530305655533/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1091).cutoff/(generalMeanRows 1091).c)).2 =
    (184428756812171/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1091).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1091).q*(generalMeanRows 1091).c/2-2 = (3187/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable351.value]
  have hcontinuation : (generalMeanRows 1091).q*(generalMeanRows 1091).cutoff/2-2 = (1568/767:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable362.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1091).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1091).criticalRate j.val*(generalMeanRows 1091).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1091).c*(generalMeanRows 1091).criticalPoint j.val)).2-
      (generalMeanRows 1091).J/2-(generalMeanRows 1091).error (generalMeanGrid j.val)+
      (generalMeanRows 1091).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1091).c)).2-
      (generalMeanRows 1091).J/2-(generalMeanRows 1091).error 4 := by
  have he : (generalMeanRows 1091).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1091) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1091)
    (generalMeanRows_prefactorDomain 1091) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1091

/-! Kernel-checked entropy margins for general spectral rectangle 1092. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1092
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6274155029) (.branch 2 (.leaf 6088827813) (.leaf 5910950551))) (.branch 5 (.branch 4 (.leaf 5740116710) (.leaf 5575948400)) (.branch 6 (.leaf 5418093852) (.leaf 5266225156)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5120036254) (.leaf 4979241126)) (.branch 10 (.leaf 4843572172) (.leaf 4712778745))) (.branch 13 (.branch 12 (.leaf 4586625835) (.leaf 4464892867)) (.branch 14 (.leaf 4347372622) (.leaf 4233870242))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4124202339) (.branch 17 (.leaf 4018196170) (.leaf 3915688889))) (.branch 20 (.branch 19 (.leaf 3816526859) (.leaf 3720565021)) (.branch 21 (.leaf 3627666317) (.leaf 3537701157)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3450546930) (.leaf 3366087546)) (.branch 25 (.leaf 3284213024) (.leaf 3204819103))) (.branch 28 (.branch 27 (.leaf 3127806886) (.leaf 3053082503)) (.branch 29 (.leaf 2980556811) (.leaf 2910145103)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2841766844) (.branch 32 (.leaf 2775345424) (.leaf 2710807927))) (.branch 35 (.branch 34 (.leaf 2648084919) (.leaf 2587110245)) (.branch 36 (.leaf 2527820845) (.leaf 2470156577)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2414060055) (.leaf 2359476497)) (.branch 40 (.leaf 2306353582) (.leaf 2254641315))) (.branch 43 (.branch 42 (.leaf 2204291904) (.leaf 2155259639)) (.branch 44 (.leaf 2107500785) (.leaf 2060973477))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2015637623) (.branch 47 (.leaf 1971454809) (.leaf 1928388219))) (.branch 50 (.branch 49 (.leaf 1886402550) (.leaf 1845463936)) (.branch 51 (.leaf 1805539879) (.leaf 1766599176)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1728611861) (.leaf 1691549141)) (.branch 55 (.leaf 1655383341) (.leaf 1620087848))) (.branch 58 (.branch 57 (.leaf 1585637065) (.leaf 1552006359)) (.branch 59 (.leaf 1519172016) (.leaf 1487111201))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1455801916) (.branch 62 (.leaf 1425222960) (.leaf 1395353896))) (.branch 65 (.branch 64 (.leaf 1366175016) (.leaf 1337667305)) (.branch 66 (.leaf 1309812416) (.leaf 1282592636)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1255990860) (.leaf 1229990566)) (.branch 70 (.leaf 1204575788) (.leaf 1179731094))) (.branch 73 (.branch 72 (.leaf 1155441561) (.leaf 1131692758)) (.branch 74 (.leaf 1108470722) (.leaf 1085761940))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1063553331) (.branch 77 (.leaf 1041832226) (.leaf 1020586357))) (.branch 80 (.branch 79 (.leaf 999803836) (.leaf 979473142)) (.branch 81 (.leaf 959583105) (.leaf 940122896)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 921082011) (.leaf 902450259)) (.branch 85 (.leaf 884217751) (.leaf 866374887))) (.branch 88 (.branch 87 (.leaf 848912349) (.leaf 831821085)) (.branch 89 (.leaf 815092306) (.leaf 798717469)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 782688275) (.branch 92 (.leaf 766996657) (.leaf 751634771))) (.branch 95 (.branch 94 (.leaf 736594991) (.leaf 721869898)) (.branch 96 (.leaf 707452277) (.leaf 693335107)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 679511553) (.leaf 665974967)) (.branch 100 (.leaf 652718872) (.leaf 639736964))) (.branch 103 (.branch 102 (.leaf 627023102) (.leaf 614571306)) (.branch 104 (.leaf 602375749) (.leaf 590430754))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 578730786) (.leaf 567270453)) (.branch 108 (.leaf 556044499) (.leaf 545047796))) (.branch 111 (.branch 110 (.leaf 534275347) (.leaf 523722276)) (.branch 112 (.leaf 513383828) (.leaf 503255365)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 493332360) (.leaf 483610398)) (.branch 116 (.leaf 474085168) (.leaf 464752464))) (.branch 119 (.branch 118 (.leaf 455608177) (.leaf 446648301)) (.branch 120 (.leaf 437868919) (.leaf 429266209)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1092).prefactor = (5170331226466067/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1092).cutoff/(generalMeanRows 1092).c)).2 =
    (80439171374911/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1092).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1092).q*(generalMeanRows 1092).c/2-2 = (1233/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable363.value]
  have hcontinuation : (generalMeanRows 1092).q*(generalMeanRows 1092).cutoff/2-2 = (632/295:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable364.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1092).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1092).criticalRate j.val*(generalMeanRows 1092).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1092).c*(generalMeanRows 1092).criticalPoint j.val)).2-
      (generalMeanRows 1092).J/2-(generalMeanRows 1092).error (generalMeanGrid j.val)+
      (generalMeanRows 1092).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1092).c)).2-
      (generalMeanRows 1092).J/2-(generalMeanRows 1092).error 4 := by
  have he : (generalMeanRows 1092).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1092) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1092)
    (generalMeanRows_prefactorDomain 1092) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1092

/-! Kernel-checked entropy margins for general spectral rectangle 1093. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1093
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6339384883) (.branch 2 (.leaf 6147245595) (.leaf 5962893586))) (.branch 5 (.branch 4 (.leaf 5785904719) (.leaf 5615884664)) (.branch 6 (.leaf 5452466265) (.leaf 5295307199)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5144087884) (.leaf 4998509596)) (.branch 10 (.leaf 4858292786) (.leaf 4723175561))) (.branch 13 (.branch 12 (.leaf 4592912305) (.leaf 4467272440)) (.branch 14 (.leaf 4346039298) (.leaf 4229009091))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4115989982) (.branch 17 (.leaf 4006801226) (.leaf 3901272396))) (.branch 20 (.branch 19 (.leaf 3799242664) (.leaf 3700560147)) (.branch 21 (.leaf 3605081308) (.leaf 3512670399)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3423198950) (.leaf 3336545301)) (.branch 25 (.leaf 3252594166) (.leaf 3171236230))) (.branch 28 (.branch 27 (.leaf 3092367780) (.leaf 3015890355)) (.branch 29 (.leaf 2941710429) (.leaf 2869739114)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2799891880) (.branch 32 (.leaf 2732088303) (.leaf 2666251823))) (.branch 35 (.branch 34 (.leaf 2602309517) (.leaf 2540191897)) (.branch 36 (.leaf 2479832712) (.leaf 2421168767)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2364139751) (.leaf 2308688083)) (.branch 40 (.leaf 2254758757) (.leaf 2202299208))) (.branch 43 (.branch 42 (.leaf 2151259177) (.leaf 2101590592)) (.branch 44 (.leaf 2053247449) (.leaf 2006185706))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1960363184) (.branch 47 (.leaf 1915739466) (.leaf 1872275810))) (.branch 50 (.branch 49 (.leaf 1829935065) (.leaf 1788681592)) (.branch 51 (.leaf 1748481184) (.leaf 1709301002)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1671109504) (.leaf 1633876383)) (.branch 55 (.leaf 1597572509) (.leaf 1562169870))) (.branch 58 (.branch 57 (.leaf 1527641523) (.leaf 1493961541)) (.branch 59 (.leaf 1461104964) (.leaf 1429047760))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1397766777) (.branch 62 (.leaf 1367239709) (.leaf 1337445048))) (.branch 65 (.branch 64 (.leaf 1308362061) (.leaf 1279970744)) (.branch 66 (.leaf 1252251799) (.leaf 1225186595)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1198757149) (.leaf 1172946087)) (.branch 70 (.leaf 1147736627) (.leaf 1123112549))) (.branch 73 (.branch 72 (.leaf 1099058175) (.leaf 1075558343)) (.branch 74 (.leaf 1052598387) (.leaf 1030164118))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1008241804) (.branch 77 (.leaf 986818151) (.leaf 965880285))) (.branch 80 (.branch 79 (.leaf 945415736) (.leaf 925412425)) (.branch 81 (.leaf 905858644) (.leaf 886743044)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 868054621) (.leaf 849782705)) (.branch 85 (.leaf 831916943) (.leaf 814447291))) (.branch 88 (.branch 87 (.leaf 797364001) (.leaf 780657611)) (.branch 89 (.leaf 764318931) (.leaf 748339041)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 732709272) (.branch 92 (.leaf 717421203) (.leaf 702466653))) (.branch 95 (.branch 94 (.leaf 687837667) (.leaf 673526514)) (.branch 96 (.leaf 659525675) (.leaf 645827840)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 632425896) (.leaf 619312925)) (.branch 100 (.leaf 606482194) (.leaf 593927152))) (.branch 103 (.branch 102 (.leaf 581641420) (.leaf 569618792)) (.branch 104 (.leaf 557853220) (.leaf 546338818))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 535069853) (.leaf 524040737)) (.branch 108 (.leaf 513246029) (.leaf 502680427))) (.branch 111 (.branch 110 (.leaf 492338761) (.leaf 482215996)) (.branch 112 (.leaf 472307219) (.leaf 462607645)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 453112606) (.leaf 443817548)) (.branch 116 (.leaf 434718032) (.leaf 425809727))) (.branch 119 (.branch 118 (.leaf 417088409) (.leaf 408549956)) (.branch 120 (.leaf 400190346) (.leaf 392005653)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1093).prefactor = (5378886383274843/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1093).cutoff/(generalMeanRows 1093).c)).2 =
    (390533917126711/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1093).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1093).q*(generalMeanRows 1093).c/2-2 = (257/320:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable359.value]
  have hcontinuation : (generalMeanRows 1093).q*(generalMeanRows 1093).cutoff/2-2 = (632/295:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable364.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1093).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1093).criticalRate j.val*(generalMeanRows 1093).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1093).c*(generalMeanRows 1093).criticalPoint j.val)).2-
      (generalMeanRows 1093).J/2-(generalMeanRows 1093).error (generalMeanGrid j.val)+
      (generalMeanRows 1093).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1093).c)).2-
      (generalMeanRows 1093).J/2-(generalMeanRows 1093).error 4 := by
  have he : (generalMeanRows 1093).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1093) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1093)
    (generalMeanRows_prefactorDomain 1093) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1093

/-! Kernel-checked entropy margins for general spectral rectangle 1094. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1094
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6047702388) (.branch 2 (.leaf 5850580831) (.leaf 5661662764))) (.branch 5 (.branch 4 (.leaf 5480502740) (.leaf 5306686370)) (.branch 6 (.leaf 5139827587) (.leaf 4979566223)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4825565826) (.leaf 4677511717)) (.branch 10 (.leaf 4535109238) (.leaf 4398082170))) (.branch 13 (.branch 12 (.leaf 4266171306) (.leaf 4139133163)) (.branch 14 (.leaf 4016738806) (.leaf 3898772784))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3785032156) (.branch 17 (.leaf 3675325605) (.leaf 3569472629))) (.branch 20 (.branch 19 (.leaf 3467302794) (.leaf 3368655054)) (.branch 21 (.leaf 3273377126) (.leaf 3181324910)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3092361961) (.leaf 3006358996)) (.branch 25 (.leaf 2923193441) (.leaf 2842749014))) (.branch 28 (.branch 27 (.leaf 2764915334) (.leaf 2689587564)) (.branch 29 (.leaf 2616666072) (.leaf 2546056127)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2477667605) (.branch 32 (.leaf 2411414722) (.leaf 2347215783))) (.branch 35 (.branch 34 (.leaf 2284992951) (.leaf 2224672025)) (.branch 36 (.leaf 2166182239) (.leaf 2109456071)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2054429064) (.leaf 2001039661)) (.branch 40 (.leaf 1949229048) (.leaf 1898941006))) (.branch 43 (.branch 42 (.leaf 1850121777) (.leaf 1802719932)) (.branch 44 (.leaf 1756686252) (.leaf 1711973611))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1668536874) (.branch 47 (.leaf 1626332791) (.leaf 1585319909))) (.branch 50 (.branch 49 (.leaf 1545458473) (.leaf 1506710351)) (.branch 51 (.leaf 1469038950) (.leaf 1432409143)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1396787198) (.leaf 1362140709)) (.branch 55 (.leaf 1328438537) (.leaf 1295650748))) (.branch 58 (.branch 57 (.leaf 1263748558) (.leaf 1232704279)) (.branch 59 (.leaf 1202491268) (.leaf 1173083881))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1144457426) (.branch 62 (.leaf 1116588125) (.leaf 1089453065))) (.branch 65 (.branch 64 (.leaf 1063030167) (.leaf 1037298148)) (.branch 66 (.leaf 1012236483) (.leaf 987825376)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 964045728) (.leaf 940879106)) (.branch 70 (.leaf 918307716) (.leaf 896314378))) (.branch 73 (.branch 72 (.leaf 874882495) (.leaf 853996035)) (.branch 74 (.leaf 833639507) (.leaf 813797933))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 794456837) (.branch 77 (.leaf 775602217) (.leaf 757220528))) (.branch 80 (.branch 79 (.leaf 739298669) (.leaf 721823959)) (.branch 81 (.leaf 704784123) (.leaf 688167278)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 671961917) (.leaf 656156894)) (.branch 85 (.leaf 640741411) (.leaf 625705006))) (.branch 88 (.branch 87 (.leaf 611037538) (.leaf 596729179)) (.branch 89 (.leaf 582770397) (.leaf 569151951)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 555864879) (.branch 92 (.leaf 542900484) (.leaf 530250330))) (.branch 95 (.branch 94 (.leaf 517906229) (.leaf 505860236)) (.branch 96 (.leaf 494104637) (.leaf 482631941)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 471434876) (.leaf 460506380)) (.branch 100 (.leaf 449839589) (.leaf 439427840))) (.branch 103 (.branch 102 (.leaf 429264654) (.leaf 419343738)) (.branch 104 (.leaf 409658975) (.leaf 400204417))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 390974284) (.leaf 381962954)) (.branch 108 (.leaf 373164962) (.leaf 364574991))) (.branch 111 (.branch 110 (.leaf 356187869) (.leaf 347998567)) (.branch 112 (.leaf 340002190) (.leaf 332193976)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324569290) (.leaf 317123622)) (.branch 116 (.leaf 309852583) (.leaf 302751898))) (.branch 119 (.branch 118 (.leaf 295817408) (.leaf 289045060)) (.branch 120 (.leaf 282430912) (.leaf 275971121)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1094).prefactor = (2797927004761251/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1094).cutoff/(generalMeanRows 1094).c)).2 =
    (5567852380913/15625000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1094).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1094).q*(generalMeanRows 1094).cutoff/2-2 = (632/295:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable364.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1094).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1094).criticalRate j.val*(generalMeanRows 1094).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1094).c*(generalMeanRows 1094).criticalPoint j.val)).2-
      (generalMeanRows 1094).J/2-(generalMeanRows 1094).error (generalMeanGrid j.val)+
      (generalMeanRows 1094).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1094).c)).2-
      (generalMeanRows 1094).J/2-(generalMeanRows 1094).error 4 := by
  have he : (generalMeanRows 1094).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1094) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1094)
    (generalMeanRows_prefactorDomain 1094) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1094

/-! Kernel-checked entropy margins for general spectral rectangle 1095. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1095
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6121980359) (.branch 2 (.leaf 5934991373) (.leaf 5755642176))) (.branch 5 (.branch 4 (.leaf 5583512092) (.leaf 5418210256)) (.branch 6 (.leaf 5259372979) (.leaf 5106661403)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4959759402) (.leaf 4818371698)) (.branch 10 (.leaf 4682222167) (.leaf 4551052317))) (.branch 13 (.branch 12 (.leaf 4424619904) (.leaf 4302697690)) (.branch 14 (.leaf 4185072303) (.leaf 4071543213))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3961921787) (.branch 17 (.leaf 3856030439) (.leaf 3753701841))) (.branch 20 (.branch 19 (.leaf 3654778210) (.leaf 3559110649)) (.branch 21 (.leaf 3466558540) (.leaf 3376988993)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3290276331) (.leaf 3206301620)) (.branch 25 (.leaf 3124952232) (.leaf 3046121441))) (.branch 28 (.branch 27 (.leaf 2969708054) (.leaf 2895616063)) (.branch 29 (.leaf 2823754324) (.leaf 2754036264)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2686379600) (.branch 32 (.leaf 2620706085) (.leaf 2556941269))) (.branch 35 (.branch 34 (.leaf 2495014276) (.leaf 2434857596)) (.branch 36 (.leaf 2376406893) (.leaf 2319600824)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2264380867) (.leaf 2210691169)) (.branch 40 (.leaf 2158478393) (.leaf 2107691584))) (.branch 43 (.branch 42 (.leaf 2058282037) (.leaf 2010203176)) (.branch 44 (.leaf 1963410441) (.leaf 1917861183))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1873514558) (.branch 47 (.leaf 1830331441) (.leaf 1788274329))) (.branch 50 (.branch 49 (.leaf 1747307267) (.leaf 1707395761)) (.branch 51 (.leaf 1668506710) (.leaf 1630608336)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1593670116) (.leaf 1557662723)) (.branch 55 (.leaf 1522557967) (.leaf 1488328741))) (.branch 58 (.branch 57 (.leaf 1454948968) (.leaf 1422393552)) (.branch 59 (.leaf 1390638336) (.leaf 1359660052))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1329436285) (.branch 62 (.leaf 1299945432) (.leaf 1271166665))) (.branch 65 (.branch 64 (.leaf 1243079897) (.leaf 1215665748)) (.branch 66 (.leaf 1188905515) (.leaf 1162781141)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1137275189) (.leaf 1112370812)) (.branch 70 (.leaf 1088051730) (.leaf 1064302208))) (.branch 73 (.branch 72 (.leaf 1041107029) (.leaf 1018451475)) (.branch 74 (.leaf 996321305) (.leaf 974702739))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 953582432) (.branch 77 (.leaf 932947467) (.leaf 912785328))) (.branch 80 (.branch 79 (.leaf 893083891) (.leaf 873831404)) (.branch 81 (.leaf 855016476) (.leaf 836628063)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 818655451) (.leaf 801088249)) (.branch 85 (.leaf 783916372) (.leaf 767130033))) (.branch 88 (.branch 87 (.leaf 750719732) (.leaf 734676242)) (.branch 89 (.leaf 718990603) (.leaf 703654112)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 688658310) (.branch 92 (.leaf 673994980) (.leaf 659656133))) (.branch 95 (.branch 94 (.leaf 645634003) (.leaf 631921036)) (.branch 96 (.leaf 618509889) (.leaf 605393416)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 592564666) (.leaf 580016876)) (.branch 100 (.leaf 567743462) (.leaf 555738017))) (.branch 103 (.branch 102 (.leaf 543994301) (.leaf 532506241)) (.branch 104 (.leaf 521267921) (.leaf 510273578))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 499517600) (.leaf 488994518)) (.branch 108 (.leaf 478699004) (.leaf 468625864))) (.branch 111 (.branch 110 (.leaf 458770038) (.leaf 449126591)) (.branch 112 (.leaf 439690713) (.leaf 430457714)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 421423021) (.leaf 412582174)) (.branch 116 (.leaf 403930821) (.leaf 395464720))) (.branch 119 (.branch 118 (.leaf 387179730) (.leaf 379071812)) (.branch 120 (.leaf 371137025) (.leaf 363371522)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1095).prefactor = (5346509833599933/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1095).cutoff/(generalMeanRows 1095).c)).2 =
    (408432271745029/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1095).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1095).q*(generalMeanRows 1095).c/2-2 = (103/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable365.value]
  have hcontinuation : (generalMeanRows 1095).q*(generalMeanRows 1095).cutoff/2-2 = (398/177:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable366.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1095).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1095).criticalRate j.val*(generalMeanRows 1095).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1095).c*(generalMeanRows 1095).criticalPoint j.val)).2-
      (generalMeanRows 1095).J/2-(generalMeanRows 1095).error (generalMeanGrid j.val)+
      (generalMeanRows 1095).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1095).c)).2-
      (generalMeanRows 1095).J/2-(generalMeanRows 1095).error 4 := by
  have he : (generalMeanRows 1095).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1095) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1095)
    (generalMeanRows_prefactorDomain 1095) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1095

/-! Kernel-checked entropy margins for general spectral rectangle 1096. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1096
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6079018975) (.branch 2 (.leaf 5886373410) (.leaf 5701704434))) (.branch 5 (.branch 4 (.leaf 5524573644) (.leaf 5354573572)) (.branch 6 (.leaf 5191324961) (.leaf 5034474335)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4883691823) (.leaf 4738669208)) (.branch 10 (.leaf 4599118173) (.leaf 4464768723))) (.branch 13 (.branch 12 (.leaf 4335367753) (.leaf 4210677755)) (.branch 14 (.leaf 4090475646) (.leaf 3974551694))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3862708554) (.branch 17 (.leaf 3754760372) (.leaf 3650531976))) (.branch 20 (.branch 19 (.leaf 3549858134) (.leaf 3452582868)) (.branch 21 (.leaf 3358558830) (.leaf 3267646725)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3179714780) (.leaf 3094638255)) (.branch 25 (.leaf 3012298988) (.leaf 2932584981))) (.branch 28 (.branch 27 (.leaf 2855390008) (.leaf 2780613261)) (.branch 29 (.leaf 2708159017) (.leaf 2637936326)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2569858726) (.branch 32 (.leaf 2503843977) (.leaf 2439813813))) (.branch 35 (.branch 34 (.leaf 2377693708) (.leaf 2317412662)) (.branch 36 (.leaf 2258903000) (.leaf 2202100184)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2146942634) (.leaf 2093371571)) (.branch 40 (.leaf 2041330854) (.leaf 1990766844))) (.branch 43 (.branch 42 (.leaf 1941628265) (.leaf 1893866079)) (.branch 44 (.leaf 1847433365) (.leaf 1802285213))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1758378613) (.branch 47 (.leaf 1715672361) (.leaf 1674126965))) (.branch 50 (.branch 49 (.leaf 1633704559) (.leaf 1594368820)) (.branch 51 (.leaf 1556084895) (.leaf 1518819320)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1482539961) (.leaf 1447215945)) (.branch 55 (.leaf 1412817599) (.leaf 1379316392))) (.branch 58 (.branch 57 (.leaf 1346684885) (.leaf 1314896676)) (.branch 59 (.leaf 1283926353) (.leaf 1253749446))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1224342388) (.branch 62 (.leaf 1195682472) (.leaf 1167747811))) (.branch 65 (.branch 64 (.leaf 1140517303) (.leaf 1113970596)) (.branch 66 (.leaf 1088088054) (.leaf 1062850728)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1038240324) (.leaf 1014239177)) (.branch 70 (.leaf 990830223) (.leaf 967996974))) (.branch 73 (.branch 72 (.leaf 945723493) (.leaf 923994376)) (.branch 74 (.leaf 902794721) (.leaf 882110118))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 861926621) (.branch 77 (.leaf 842230734) (.leaf 823009391))) (.branch 80 (.branch 79 (.leaf 804249942) (.leaf 785940132)) (.branch 81 (.leaf 768068090) (.leaf 750622312)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 733591648) (.leaf 716965290)) (.branch 85 (.leaf 700732755) (.leaf 684883877))) (.branch 88 (.branch 87 (.leaf 669408794) (.leaf 654297937)) (.branch 89 (.leaf 639542020) (.leaf 625132026)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 611059204) (.branch 92 (.leaf 597315055) (.leaf 583891325))) (.branch 95 (.branch 94 (.leaf 570779995) (.leaf 557973273)) (.branch 96 (.leaf 545463590) (.leaf 533243587)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 521306110) (.leaf 509644206)) (.branch 100 (.leaf 498251113) (.leaf 487120252))) (.branch 103 (.branch 102 (.leaf 476245229) (.leaf 465619818)) (.branch 104 (.leaf 455237965) (.leaf 445093778))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 435181522) (.leaf 425495616)) (.branch 108 (.leaf 416030625) (.leaf 406781259))) (.branch 111 (.branch 110 (.leaf 397742366) (.leaf 388908931)) (.branch 112 (.leaf 380276066) (.leaf 371839012)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 363593133) (.leaf 355533911)) (.branch 116 (.leaf 347656944) (.leaf 339957944))) (.branch 119 (.branch 118 (.leaf 332432730) (.leaf 325077227)) (.branch 120 (.leaf 317887465) (.leaf 310859570)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1096).prefactor = (2772682599691677/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1096).cutoff/(generalMeanRows 1096).c)).2 =
    (391577940190047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1096).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1096).q*(generalMeanRows 1096).cutoff/2-2 = (398/177:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable366.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1096).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1096).criticalRate j.val*(generalMeanRows 1096).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1096).c*(generalMeanRows 1096).criticalPoint j.val)).2-
      (generalMeanRows 1096).J/2-(generalMeanRows 1096).error (generalMeanGrid j.val)+
      (generalMeanRows 1096).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1096).c)).2-
      (generalMeanRows 1096).J/2-(generalMeanRows 1096).error 4 := by
  have he : (generalMeanRows 1096).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1096) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1096)
    (generalMeanRows_prefactorDomain 1096) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1096

/-! Kernel-checked entropy margins for general spectral rectangle 1097. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1097
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6397105799) (.branch 2 (.leaf 6196818520) (.leaf 6004786873))) (.branch 5 (.branch 4 (.leaf 5820556884) (.leaf 5643706659)) (.branch 6 (.leaf 5473843556) (.leaf 5310601660)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5153639529) (.leaf 5002638168)) (.branch 10 (.leaf 4857299211) (.leaf 4717343280))) (.branch 13 (.branch 12 (.leaf 4582508502) (.leaf 4452549169)) (.branch 14 (.leaf 4327234518) (.leaf 4206347621))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4089684383) (.branch 17 (.leaf 3977052612) (.leaf 3868271182))) (.branch 20 (.branch 19 (.leaf 3763169261) (.leaf 3661585602)) (.branch 21 (.leaf 3563367893) (.leaf 3468372161)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3376462220) (.leaf 3287509165)) (.branch 25 (.leaf 3201390900) (.leaf 3117991706))) (.branch 28 (.branch 27 (.leaf 3037201840) (.leaf 2958917165)) (.branch 29 (.leaf 2883038800) (.leaf 2809472808)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2738129890) (.branch 32 (.leaf 2668925116) (.leaf 2601777661))) (.branch 35 (.branch 34 (.leaf 2536610570) (.leaf 2473350535)) (.branch 36 (.leaf 2411927681) (.leaf 2352275377)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2294330050) (.leaf 2238031017)) (.branch 40 (.leaf 2183320325) (.leaf 2130142604))) (.branch 43 (.branch 42 (.leaf 2078444923) (.leaf 2028176663)) (.branch 44 (.leaf 1979289393) (.leaf 1931736754))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1885474352) (.branch 47 (.leaf 1840459656) (.leaf 1796651902))) (.branch 50 (.branch 49 (.leaf 1754012002) (.leaf 1712502463)) (.branch 51 (.leaf 1672087304) (.leaf 1632731983)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1594403324) (.leaf 1557069453)) (.branch 55 (.leaf 1520699735) (.leaf 1485264711))) (.branch 58 (.branch 57 (.leaf 1450736048) (.leaf 1417086481)) (.branch 59 (.leaf 1384289765) (.leaf 1352320629))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1321154729) (.branch 62 (.leaf 1290768608) (.leaf 1261139653))) (.branch 65 (.branch 64 (.leaf 1232246062) (.leaf 1204066802)) (.branch 66 (.leaf 1176581582) (.leaf 1149770813)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1123615586) (.leaf 1098097634)) (.branch 70 (.leaf 1073199313) (.leaf 1048903570))) (.branch 73 (.branch 72 (.leaf 1025193922) (.leaf 1002054428)) (.branch 74 (.leaf 979469673) (.leaf 957424740))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 935905195) (.branch 77 (.leaf 914897065) (.leaf 894386819))) (.branch 80 (.branch 79 (.leaf 874361355) (.leaf 854807978)) (.branch 81 (.leaf 835714387) (.leaf 817068660)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 798859239) (.leaf 781074915)) (.branch 85 (.leaf 763704817) (.leaf 746738401))) (.branch 88 (.branch 87 (.leaf 730165432) (.leaf 713975980)) (.branch 89 (.leaf 698160402) (.leaf 682709339)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 667613699) (.branch 92 (.leaf 652864652) (.leaf 638453621))) (.branch 95 (.branch 94 (.leaf 624372269) (.leaf 610612496)) (.branch 96 (.leaf 597166427) (.leaf 584026407)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 571184991) (.leaf 558634940)) (.branch 100 (.leaf 546369213) (.leaf 534380959))) (.branch 103 (.branch 102 (.leaf 522663512) (.leaf 511210387)) (.branch 104 (.leaf 500015270) (.leaf 489072016))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 478374643) (.leaf 467917326)) (.branch 108 (.leaf 457694392) (.leaf 447700317))) (.branch 111 (.branch 110 (.leaf 437929720) (.leaf 428377358)) (.branch 112 (.leaf 419038125) (.leaf 409907044)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 400979264) (.leaf 392250060)) (.branch 116 (.leaf 383714825) (.leaf 375369066))) (.branch 119 (.branch 118 (.leaf 367208407) (.leaf 359228578)) (.branch 120 (.leaf 351425416) (.leaf 343794861)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1097).prefactor = (5751616690439443/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1097).cutoff/(generalMeanRows 1097).c)).2 =
    (397164546898687/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1097).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1097).q*(generalMeanRows 1097).c/2-2 = (107/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable344.value]
  have hcontinuation : (generalMeanRows 1097).q*(generalMeanRows 1097).cutoff/2-2 = (398/177:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable366.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1097).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1097).criticalRate j.val*(generalMeanRows 1097).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1097).c*(generalMeanRows 1097).criticalPoint j.val)).2-
      (generalMeanRows 1097).J/2-(generalMeanRows 1097).error (generalMeanGrid j.val)+
      (generalMeanRows 1097).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1097).c)).2-
      (generalMeanRows 1097).J/2-(generalMeanRows 1097).error 4 := by
  have he : (generalMeanRows 1097).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1097) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1097)
    (generalMeanRows_prefactorDomain 1097) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1097

/-! Kernel-checked entropy margins for general spectral rectangle 1098. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1098
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6732082182) (.branch 2 (.leaf 6523879633) (.leaf 6324220886))) (.branch 5 (.branch 4 (.leaf 6132635830) (.leaf 5948687621)) (.branch 6 (.leaf 5771969744) (.leaf 5602103400)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5438735158) (.leaf 5281534861)) (.branch 10 (.leaf 5130193735) (.leaf 4984422689))) (.branch 13 (.branch 12 (.leaf 4843950776) (.leaf 4708523799)) (.branch 14 (.leaf 4577903049) (.leaf 4451864158))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4330196045) (.branch 17 (.leaf 4212699969) (.leaf 4099188647))) (.branch 20 (.branch 19 (.leaf 3989485461) (.leaf 3883423720)) (.branch 21 (.leaf 3780845985) (.leaf 3681603453)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3585555383) (.leaf 3492568571)) (.branch 25 (.leaf 3402516862) (.leaf 3315280701))) (.branch 28 (.branch 27 (.leaf 3230746720) (.leaf 3148807346)) (.branch 29 (.leaf 3069360452) (.leaf 2992309017)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2917560826) (.branch 32 (.leaf 2845028175) (.leaf 2774627612))) (.branch 35 (.branch 34 (.leaf 2706279682) (.leaf 2639908702)) (.branch 36 (.leaf 2575442536) (.leaf 2512812404)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2451952684) (.leaf 2392800741)) (.branch 40 (.leaf 2335296762) (.leaf 2279383597))) (.branch 43 (.branch 42 (.leaf 2225006622) (.leaf 2172113596)) (.branch 44 (.leaf 2120654539) (.leaf 2070581610))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2021848996) (.branch 47 (.leaf 1974412807) (.leaf 1928230976))) (.branch 50 (.branch 49 (.leaf 1883263169) (.leaf 1839470693)) (.branch 51 (.leaf 1796816415) (.leaf 1755264690)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1714781278) (.leaf 1675333284)) (.branch 55 (.leaf 1636889088) (.leaf 1599418285))) (.branch 58 (.branch 57 (.leaf 1562891629) (.leaf 1527280975)) (.branch 59 (.leaf 1492559230) (.leaf 1458700302))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1425679056) (.branch 62 (.leaf 1393471272) (.leaf 1362053597))) (.branch 65 (.branch 64 (.leaf 1331403514) (.leaf 1301499299)) (.branch 66 (.leaf 1272319989) (.leaf 1243845348)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1216055835) (.leaf 1188932577)) (.branch 70 (.leaf 1162457334) (.leaf 1136612481))) (.branch 73 (.branch 72 (.leaf 1111380975) (.leaf 1086746335)) (.branch 74 (.leaf 1062692616) (.leaf 1039204390))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1016266725) (.branch 77 (.leaf 993865161) (.leaf 971985696))) (.branch 80 (.branch 79 (.leaf 950614767) (.leaf 929739230)) (.branch 81 (.leaf 909346347) (.leaf 889423770)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 869959524) (.leaf 850941995)) (.branch 85 (.leaf 832359917) (.leaf 814202356))) (.branch 88 (.branch 87 (.leaf 796458701) (.leaf 779118652)) (.branch 89 (.leaf 762172206) (.leaf 745609650)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 729421547) (.branch 92 (.leaf 713598731) (.leaf 698132292))) (.branch 95 (.branch 94 (.leaf 683013572) (.leaf 668234154)) (.branch 96 (.leaf 653785852) (.leaf 639660708)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 625850981) (.leaf 612349139)) (.branch 100 (.leaf 599147856) (.leaf 586240001))) (.branch 103 (.branch 102 (.leaf 573618635) (.leaf 561277003)) (.branch 104 (.leaf 549208527) (.leaf 537406803))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 525865597) (.leaf 514578832)) (.branch 108 (.leaf 503540594) (.leaf 492745117))) (.branch 111 (.branch 110 (.leaf 482186785) (.leaf 471860124)) (.branch 112 (.leaf 461759800) (.leaf 451880614)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 442217498) (.leaf 432765509)) (.branch 116 (.leaf 423519830) (.leaf 414475763))) (.branch 119 (.branch 118 (.leaf 405628724) (.leaf 396974246)) (.branch 120 (.leaf 388507969) (.leaf 380225639)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1098).prefactor = (37284621215547/6250000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1098).cutoff/(generalMeanRows 1098).c)).2 =
    (40278253920291/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1098).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1098).q*(generalMeanRows 1098).cutoff/2-2 = (398/177:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable366.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1098).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1098).criticalRate j.val*(generalMeanRows 1098).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1098).c*(generalMeanRows 1098).criticalPoint j.val)).2-
      (generalMeanRows 1098).J/2-(generalMeanRows 1098).error (generalMeanGrid j.val)+
      (generalMeanRows 1098).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1098).c)).2-
      (generalMeanRows 1098).J/2-(generalMeanRows 1098).error 4 := by
  have he : (generalMeanRows 1098).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1098) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1098)
    (generalMeanRows_prefactorDomain 1098) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1098

/-! Kernel-checked entropy margins for general spectral rectangle 1099. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1099
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7189002746) (.branch 2 (.leaf 6972182938) (.leaf 6764183746))) (.branch 5 (.branch 4 (.leaf 6564519065) (.leaf 6372737286)) (.branch 6 (.leaf 6188418245) (.leaf 6011170511)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5840628948) (.leaf 5676452541)) (.branch 10 (.leaf 5518322433) (.leaf 5365940160))) (.branch 13 (.branch 12 (.leaf 5219026055) (.leaf 5077317799)) (.branch 14 (.leaf 4940569114) (.leaf 4808548567))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4681038485) (.branch 17 (.leaf 4557833963) (.leaf 4438741958))) (.branch 20 (.branch 19 (.leaf 4323580458) (.leaf 4212177719)) (.branch 21 (.leaf 4104371569) (.leaf 4000008766)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3898944399) (.leaf 3801041348)) (.branch 25 (.leaf 3706169779) (.leaf 3614206675))) (.branch 28 (.branch 27 (.leaf 3525035408) (.leaf 3438545337)) (.branch 29 (.leaf 3354631440) (.leaf 3273193967)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3194138125) (.branch 32 (.leaf 3117373777) (.leaf 3042815167))) (.branch 35 (.branch 34 (.leaf 2970380666) (.leaf 2899992525)) (.branch 36 (.leaf 2831576657) (.leaf 2765062429)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2700382460) (.leaf 2637472446)) (.branch 40 (.leaf 2576270985) (.leaf 2516719420))) (.branch 43 (.branch 42 (.leaf 2458761686) (.leaf 2402344174)) (.branch 44 (.leaf 2347415597) (.leaf 2293926867))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2241830979) (.branch 47 (.leaf 2191082904) (.leaf 2141639485))) (.branch 50 (.branch 49 (.leaf 2093459343) (.leaf 2046502785)) (.branch 51 (.leaf 2000731717) (.leaf 1956109570)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1912601220) (.leaf 1870172916)) (.branch 55 (.leaf 1828792217) (.leaf 1788427927))) (.branch 58 (.branch 57 (.leaf 1749050035) (.leaf 1710629658)) (.branch 59 (.leaf 1673138991) (.leaf 1636551252))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1600840640) (.branch 62 (.leaf 1565982285) (.leaf 1531952211))) (.branch 65 (.branch 64 (.leaf 1498727289) (.leaf 1466285205)) (.branch 66 (.leaf 1434604422) (.leaf 1403664144)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1373444288) (.leaf 1343925449)) (.branch 70 (.leaf 1315088871) (.leaf 1286916425))) (.branch 73 (.branch 72 (.leaf 1259390576) (.leaf 1232494361)) (.branch 74 (.leaf 1206211366) (.leaf 1180525704))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1155421992) (.branch 77 (.leaf 1130885330) (.leaf 1106901284))) (.branch 80 (.branch 79 (.leaf 1083455868) (.leaf 1060535522)) (.branch 81 (.leaf 1038127103) (.leaf 1016217862)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 994795430) (.leaf 973847809)) (.branch 85 (.leaf 953363353) (.leaf 933330755))) (.branch 88 (.branch 87 (.leaf 913739038) (.leaf 894577539)) (.branch 89 (.leaf 875835902) (.leaf 857504062)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 839572238) (.branch 92 (.leaf 822030925) (.leaf 804870877))) (.branch 95 (.branch 94 (.leaf 788083107) (.leaf 771658872)) (.branch 96 (.leaf 755589667) (.leaf 739867216)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 724483465) (.leaf 709430576)) (.branch 100 (.leaf 694700918) (.leaf 680287061))) (.branch 103 (.branch 102 (.leaf 666181768) (.leaf 652377991)) (.branch 104 (.leaf 638868866) (.leaf 625647703))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 612707984) (.leaf 600043358)) (.branch 108 (.leaf 587647632) (.leaf 575514771))) (.branch 111 (.branch 110 (.leaf 563638889) (.leaf 552014249)) (.branch 112 (.leaf 540635255) (.leaf 529496447)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 518592504) (.leaf 507918229)) (.branch 116 (.leaf 497468555) (.leaf 487238538))) (.branch 119 (.branch 118 (.leaf 477223351) (.leaf 467418284)) (.branch 120 (.leaf 457818740) (.leaf 448420230)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1099).prefactor = (154685465767989/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1099).cutoff/(generalMeanRows 1099).c)).2 =
    (414114105212461/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1099).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1099).q*(generalMeanRows 1099).c/2-2 = (101/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable286.value]
  have hcontinuation : (generalMeanRows 1099).q*(generalMeanRows 1099).cutoff/2-2 = (398/177:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable366.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1099).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1099).criticalRate j.val*(generalMeanRows 1099).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1099).c*(generalMeanRows 1099).criticalPoint j.val)).2-
      (generalMeanRows 1099).J/2-(generalMeanRows 1099).error (generalMeanGrid j.val)+
      (generalMeanRows 1099).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1099).c)).2-
      (generalMeanRows 1099).J/2-(generalMeanRows 1099).error 4 := by
  have he : (generalMeanRows 1099).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1099) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1099)
    (generalMeanRows_prefactorDomain 1099) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1099

/-! Kernel-checked entropy margins for general spectral rectangle 1100. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1100
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7566267198) (.branch 2 (.leaf 7340980806) (.leaf 7124820965))) (.branch 5 (.branch 4 (.leaf 6917284230) (.leaf 6717902934)) (.branch 6 (.leaf 6526242021) (.leaf 6341896232)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6164487576) (.leaf 5993663071)) (.branch 10 (.leaf 5829092710) (.leaf 5670467629))) (.branch 13 (.branch 12 (.leaf 5517498447) (.leaf 5369913771)) (.branch 14 (.leaf 5227458829) (.leaf 5089894239))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4956994876) (.branch 17 (.leaf 4828548847) (.leaf 4704356550))) (.branch 20 (.branch 19 (.leaf 4584229809) (.leaf 4467991090)) (.branch 21 (.leaf 4355472770) (.leaf 4246516473)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4140972458) (.leaf 4038699046)) (.branch 25 (.leaf 3939562102) (.leaf 3843434551))) (.branch 28 (.branch 27 (.leaf 3750195930) (.leaf 3659731973)) (.branch 29 (.leaf 3571934228) (.leaf 3486699700)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3403930521) (.branch 32 (.leaf 3323533641) (.leaf 3245420542))) (.branch 35 (.branch 34 (.leaf 3169506971) (.leaf 3095712691)) (.branch 36 (.leaf 3023961250) (.leaf 2954179763)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2886298713) (.leaf 2820251758)) (.branch 40 (.leaf 2755975557) (.leaf 2693409603))) (.branch 43 (.branch 42 (.leaf 2632496069) (.leaf 2573179664)) (.branch 44 (.leaf 2515407492) (.leaf 2459128933))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2404295513) (.branch 47 (.leaf 2350860800) (.leaf 2298780292))) (.branch 50 (.branch 49 (.leaf 2248011323) (.leaf 2198512966)) (.branch 51 (.leaf 2150245945) (.leaf 2103172555)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2057256581) (.leaf 2012463225)) (.branch 55 (.leaf 1968759039) (.leaf 1926111858))) (.branch 58 (.branch 57 (.leaf 1884490739) (.leaf 1843865900)) (.branch 59 (.leaf 1804208670) (.leaf 1765491433))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1727687582) (.branch 62 (.leaf 1690771471) (.leaf 1654718370))) (.branch 65 (.branch 64 (.leaf 1619504425) (.leaf 1585106622)) (.branch 66 (.leaf 1551502741) (.leaf 1518671331)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1486591670) (.leaf 1455243735)) (.branch 70 (.leaf 1424608173) (.leaf 1394666272))) (.branch 73 (.branch 72 (.leaf 1365399932) (.leaf 1336791643)) (.branch 74 (.leaf 1308824460) (.leaf 1281481976))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1254748304) (.branch 77 (.leaf 1228608056) (.leaf 1203046319))) (.branch 80 (.branch 79 (.leaf 1178048643) (.leaf 1153601017)) (.branch 81 (.leaf 1129689853) (.leaf 1106301973)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1083424589) (.leaf 1061045292)) (.branch 85 (.leaf 1039152036) (.leaf 1017733123))) (.branch 88 (.branch 87 (.leaf 996777193) (.leaf 976273211)) (.branch 89 (.leaf 956210454) (.leaf 936578503)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 917367226) (.branch 92 (.leaf 898566774) (.leaf 880167570))) (.branch 95 (.branch 94 (.leaf 862160296) (.leaf 844535890)) (.branch 96 (.leaf 827285530) (.leaf 810400634)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 793872845) (.leaf 777694029)) (.branch 100 (.leaf 761856264) (.leaf 746351833))) (.branch 103 (.branch 102 (.leaf 731173221) (.leaf 716313107)) (.branch 104 (.leaf 701764354) (.leaf 687520010))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 673573297) (.leaf 659917607)) (.branch 108 (.leaf 646546498) (.leaf 633453687))) (.branch 111 (.branch 110 (.leaf 620633049) (.leaf 608078607)) (.branch 112 (.leaf 595784532) (.leaf 583745135)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 571954866) (.leaf 560408310)) (.branch 116 (.leaf 549100180) (.leaf 538025317))) (.branch 119 (.branch 118 (.leaf 527178683) (.leaf 516555360)) (.branch 120 (.leaf 506150547) (.leaf 495959554)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1100).prefactor = (1604387582586083/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1100).cutoff/(generalMeanRows 1100).c)).2 =
    (4198284064759/10000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1100).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1100).q*(generalMeanRows 1100).c/2-2 = (99/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable367.value]
  have hcontinuation : (generalMeanRows 1100).q*(generalMeanRows 1100).cutoff/2-2 = (398/177:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable366.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1100).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1100).criticalRate j.val*(generalMeanRows 1100).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1100).c*(generalMeanRows 1100).criticalPoint j.val)).2-
      (generalMeanRows 1100).J/2-(generalMeanRows 1100).error (generalMeanGrid j.val)+
      (generalMeanRows 1100).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1100).c)).2-
      (generalMeanRows 1100).J/2-(generalMeanRows 1100).error 4 := by
  have he : (generalMeanRows 1100).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1100) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1100)
    (generalMeanRows_prefactorDomain 1100) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1100

/-! Kernel-checked entropy margins for general spectral rectangle 1101. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1101
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8294888599) (.branch 2 (.leaf 8063972284) (.leaf 7842229672))) (.branch 5 (.branch 4 (.leaf 7629151427) (.leaf 7424264675)) (.branch 6 (.leaf 7227129768) (.leaf 7037337402)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6854506041) (.leaf 6678279605)) (.branch 10 (.leaf 6508325393) (.leaf 6344332211))) (.branch 13 (.branch 12 (.leaf 6186008678) (.leaf 6033081699)) (.branch 14 (.leaf 5885295068) (.leaf 5742408212))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5604195034) (.branch 17 (.leaf 5470442866) (.leaf 5340951510))) (.branch 20 (.branch 19 (.leaf 5215532353) (.leaf 5094007570)) (.branch 21 (.leaf 4976209376) (.leaf 4861979351)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4751167809) (.leaf 4643633223)) (.branch 25 (.leaf 4539241694) (.leaf 4437866452))) (.branch 28 (.branch 27 (.leaf 4339387405) (.leaf 4243690718)) (.branch 29 (.leaf 4150668416) (.leaf 4060218027)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3972242241) (.branch 32 (.leaf 3886648601) (.leaf 3803349206))) (.branch 35 (.branch 34 (.leaf 3722260444) (.leaf 3643302736)) (.branch 36 (.leaf 3566400303) (.leaf 3491480947)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3418475839) (.leaf 3347319336)) (.branch 40 (.leaf 3277948796) (.leaf 3210304411))) (.branch 43 (.branch 42 (.leaf 3144329052) (.leaf 3079968119)) (.branch 44 (.leaf 3017169406) (.leaf 2955882969))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2896061007) (.branch 47 (.leaf 2837657748) (.leaf 2780629342))) (.branch 50 (.branch 49 (.leaf 2724933757) (.leaf 2670530690)) (.branch 51 (.leaf 2617381478) (.leaf 2565449009)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2514697650) (.leaf 2465093167)) (.branch 55 (.leaf 2416602661) (.leaf 2369194500))) (.branch 58 (.branch 57 (.leaf 2322838253) (.leaf 2277504640)) (.branch 59 (.leaf 2233165471) (.leaf 2189793592))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2147362844) (.branch 62 (.leaf 2105848009) (.leaf 2065224769))) (.branch 65 (.branch 64 (.leaf 2025469665) (.leaf 1986560059)) (.branch 66 (.leaf 1948474093) (.leaf 1911190656)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1874689352) (.leaf 1838950468)) (.branch 70 (.leaf 1803954943) (.leaf 1769684341))) (.branch 73 (.branch 72 (.leaf 1736120822) (.leaf 1703247120)) (.branch 74 (.leaf 1671046516) (.leaf 1639502819))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1608600338) (.branch 77 (.leaf 1578323867) (.leaf 1548658664))) (.branch 80 (.branch 79 (.leaf 1519590429) (.leaf 1491105293)) (.branch 81 (.leaf 1463189795) (.leaf 1435830868)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1409015824) (.leaf 1382732342)) (.branch 85 (.leaf 1356968448) (.leaf 1331712508))) (.branch 88 (.branch 87 (.leaf 1306953213) (.leaf 1282679566)) (.branch 89 (.leaf 1258880871) (.leaf 1235546725)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1212667004) (.branch 92 (.leaf 1190231854) (.leaf 1168231682))) (.branch 95 (.branch 94 (.leaf 1146657148) (.leaf 1125499154)) (.branch 96 (.leaf 1104748838) (.leaf 1084397564)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1064436917) (.leaf 1044858692)) (.branch 100 (.leaf 1025654890) (.leaf 1006817713))) (.branch 103 (.branch 102 (.leaf 988339553) (.leaf 970212987)) (.branch 104 (.leaf 952430775) (.leaf 934985851))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 917871317) (.leaf 901080440)) (.branch 108 (.leaf 884606647) (.leaf 868443517))) (.branch 111 (.branch 110 (.leaf 852584782) (.leaf 837024317)) (.branch 112 (.leaf 821756139) (.leaf 806774401)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 792073391) (.leaf 777647526)) (.branch 116 (.leaf 763491347) (.leaf 749599518))) (.branch 119 (.branch 118 (.leaf 735966824) (.leaf 722588162)) (.branch 120 (.leaf 709458544) (.leaf 696573091)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1101).prefactor = (3267903165494549/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1101).cutoff/(generalMeanRows 1101).c)).2 =
    (448900221297877/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1101).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1101).q*(generalMeanRows 1101).c/2-2 = (89/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable368.value]
  have hcontinuation : (generalMeanRows 1101).q*(generalMeanRows 1101).cutoff/2-2 = (398/177:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable366.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1101).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1101).criticalRate j.val*(generalMeanRows 1101).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1101).c*(generalMeanRows 1101).criticalPoint j.val)).2-
      (generalMeanRows 1101).J/2-(generalMeanRows 1101).error (generalMeanGrid j.val)+
      (generalMeanRows 1101).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1101).c)).2-
      (generalMeanRows 1101).J/2-(generalMeanRows 1101).error 4 := by
  have he : (generalMeanRows 1101).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1101) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1101)
    (generalMeanRows_prefactorDomain 1101) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1101

/-! Kernel-checked entropy margins for general spectral rectangle 1102. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1102
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6829784740) (.branch 2 (.leaf 6630247023) (.leaf 6438590992))) (.branch 5 (.branch 4 (.leaf 6254395721) (.leaf 6077269565)) (.branch 6 (.leaf 5906847574) (.leaf 5742789186)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5584776170) (.leaf 5432510783)) (.branch 10 (.leaf 5285714118) (.leaf 5144124612))) (.branch 13 (.branch 12 (.leaf 5007496703) (.leaf 4875599615)) (.branch 14 (.leaf 4748216250) (.leaf 4625142195))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4506184801) (.branch 17 (.leaf 4391162354) (.leaf 4279903315))) (.branch 20 (.branch 19 (.leaf 4172245621) (.leaf 4068036045)) (.branch 21 (.leaf 3967129614) (.leaf 3869389061)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3774684334) (.leaf 3682892132)) (.branch 25 (.leaf 3593895485) (.leaf 3507583355))) (.branch 28 (.branch 27 (.leaf 3423850278) (.leaf 3342596026)) (.branch 29 (.leaf 3263725289) (.leaf 3187147391)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3112776013) (.branch 32 (.leaf 3040528945) (.leaf 2970327849))) (.branch 35 (.branch 34 (.leaf 2902098041) (.leaf 2835768285)) (.branch 36 (.leaf 2771270603) (.leaf 2708540094)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2647514770) (.leaf 2588135394)) (.branch 40 (.leaf 2530345339) (.leaf 2474090445))) (.branch 43 (.branch 42 (.leaf 2419318891) (.leaf 2365981077)) (.branch 44 (.leaf 2314029503) (.leaf 2263418667))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2214104962) (.branch 47 (.leaf 2166046579) (.leaf 2119203421))) (.branch 50 (.branch 49 (.leaf 2073537015) (.leaf 2029010436)) (.branch 51 (.leaf 1985588228) (.leaf 1943236334)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1901922030) (.leaf 1861613864)) (.branch 55 (.leaf 1822281589) (.leaf 1783896114))) (.branch 58 (.branch 57 (.leaf 1746429447) (.leaf 1709854643)) (.branch 59 (.leaf 1674145760) (.leaf 1639277809))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1605226714) (.branch 62 (.leaf 1571969273) (.leaf 1539483112))) (.branch 65 (.branch 64 (.leaf 1507746657) (.leaf 1476739094)) (.branch 66 (.leaf 1446440337) (.leaf 1416830996)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1387892350) (.leaf 1359606314)) (.branch 70 (.leaf 1331955419) (.leaf 1304922777))) (.branch 73 (.branch 72 (.leaf 1278492067) (.leaf 1252647502)) (.branch 74 (.leaf 1227373815) (.leaf 1202656234))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1178480460) (.branch 77 (.leaf 1154832655) (.leaf 1131699417))) (.branch 80 (.branch 79 (.leaf 1109067764) (.leaf 1086925122)) (.branch 81 (.leaf 1065259304) (.leaf 1044058497)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1023311249) (.leaf 1003006452)) (.branch 85 (.leaf 983133334) (.leaf 963681439))) (.branch 88 (.branch 87 (.leaf 944640625) (.leaf 926001044)) (.branch 89 (.leaf 907753135) (.leaf 889887614)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 872395461) (.branch 92 (.leaf 855267915) (.leaf 838496461))) (.branch 95 (.branch 94 (.leaf 822072823) (.leaf 805988957)) (.branch 96 (.leaf 790237038) (.leaf 774809460)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 759698821) (.leaf 744897921)) (.branch 100 (.leaf 730399754) (.leaf 716197501))) (.branch 103 (.branch 102 (.leaf 702284522) (.leaf 688654356)) (.branch 104 (.leaf 675300707) (.leaf 662217447))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 649398604) (.leaf 636838360)) (.branch 108 (.leaf 624531046) (.leaf 612471137))) (.branch 111 (.branch 110 (.leaf 600653248) (.leaf 589072128)) (.branch 112 (.leaf 577722657) (.leaf 566599845)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 555698822) (.leaf 545014838)) (.branch 116 (.leaf 534543260) (.leaf 524279567))) (.branch 119 (.branch 118 (.leaf 514219347) (.leaf 504358294)) (.branch 120 (.leaf 494692206) (.leaf 485216979)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1102).prefactor = (5385254660623949/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1102).cutoff/(generalMeanRows 1102).c)).2 =
    (92477003176991/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1102).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1102).q*(generalMeanRows 1102).c/2-2 = (2989/4000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable352.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1102).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1102).criticalRate j.val*(generalMeanRows 1102).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1102).c*(generalMeanRows 1102).criticalPoint j.val)).2-
      (generalMeanRows 1102).J/2-(generalMeanRows 1102).error (generalMeanGrid j.val)+
      (generalMeanRows 1102).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1102).c)).2-
      (generalMeanRows 1102).J/2-(generalMeanRows 1102).error 4 := by
  have he : (generalMeanRows 1102).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1102) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1102)
    (generalMeanRows_prefactorDomain 1102) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1102

/-! Kernel-checked entropy margins for general spectral rectangle 1103. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1103
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6479202887) (.branch 2 (.leaf 6292666014) (.leaf 6113515531))) (.branch 5 (.branch 4 (.leaf 5941351853) (.leaf 5775803447)) (.branch 6 (.leaf 5616524345) (.leaf 5463191941)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5315505015) (.leaf 5173181964)) (.branch 10 (.leaf 5035959215) (.leaf 4903589796))) (.branch 13 (.branch 12 (.leaf 4775842039) (.leaf 4652498418)) (.branch 14 (.leaf 4533354482) (.leaf 4418217895))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4306907556) (.branch 17 (.leaf 4199252801) (.leaf 4095092665))) (.branch 20 (.branch 19 (.leaf 3994275217) (.leaf 3896656944)) (.branch 21 (.leaf 3802102183) (.leaf 3710482602)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3621676725) (.leaf 3535569484)) (.branch 25 (.leaf 3452051815) (.leaf 3371020282))) (.branch 28 (.branch 27 (.leaf 3292376722) (.leaf 3216027926)) (.branch 29 (.leaf 3141885335) (.leaf 3069864764)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2999886140) (.branch 32 (.leaf 2931873261) (.leaf 2865753569))) (.branch 35 (.branch 34 (.leaf 2801457946) (.leaf 2738920510)) (.branch 36 (.leaf 2678078439) (.leaf 2618871797)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2561243371) (.leaf 2505138531)) (.branch 40 (.leaf 2450505077) (.leaf 2397293119))) (.branch 43 (.branch 42 (.leaf 2345454948) (.leaf 2294944919)) (.branch 44 (.leaf 2245719350) (.leaf 2197736410))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2150956030) (.branch 47 (.leaf 2105339814) (.leaf 2060850947))) (.branch 50 (.branch 49 (.leaf 2017454121) (.leaf 1975115459)) (.branch 51 (.leaf 1933802442) (.leaf 1893483845)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1854129671) (.leaf 1815711094)) (.branch 55 (.leaf 1778200400) (.leaf 1741570937))) (.branch 58 (.branch 57 (.leaf 1705797064) (.leaf 1670854103)) (.branch 59 (.leaf 1636718292) (.leaf 1603366749))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1570777424) (.branch 62 (.leaf 1538929067) (.leaf 1507801189))) (.branch 65 (.branch 64 (.leaf 1477374029) (.leaf 1447628522)) (.branch 66 (.leaf 1418546266) (.leaf 1390109498)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1362301059) (.leaf 1335104376)) (.branch 70 (.leaf 1308503431) (.leaf 1282482739))) (.branch 73 (.branch 72 (.leaf 1257027327) (.leaf 1232122714)) (.branch 74 (.leaf 1207754885) (.leaf 1183910277))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1160575760) (.branch 77 (.leaf 1137738616) (.leaf 1115386529))) (.branch 80 (.branch 79 (.leaf 1093507560) (.leaf 1072090143)) (.branch 81 (.leaf 1051123059) (.leaf 1030595433)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1010496713) (.leaf 990816661)) (.branch 85 (.leaf 971545344) (.leaf 952673115))) (.branch 88 (.branch 87 (.leaf 934190609) (.leaf 916088731)) (.branch 89 (.leaf 898358644) (.leaf 880991763)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 863979741) (.branch 92 (.leaf 847314468) (.leaf 830988054))) (.branch 95 (.branch 94 (.leaf 814992829) (.leaf 799321329)) (.branch 96 (.leaf 783966294) (.leaf 768920657)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 754177541) (.leaf 739730250)) (.branch 100 (.leaf 725572263) (.leaf 711697231))) (.branch 103 (.branch 102 (.leaf 698098968) (.leaf 684771448)) (.branch 104 (.leaf 671708798) (.leaf 658905294))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 646355357) (.leaf 634053549)) (.branch 108 (.leaf 621994564) (.leaf 610173231))) (.branch 111 (.branch 110 (.leaf 598584504) (.leaf 587223460)) (.branch 112 (.leaf 576085298) (.leaf 565165329)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 554458982) (.leaf 543961789)) (.branch 116 (.leaf 533669394) (.leaf 523577540))) (.branch 119 (.branch 118 (.leaf 513682072) (.leaf 503978930)) (.branch 120 (.leaf 494464151) (.leaf 485133863)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1103).prefactor = (5123675206237897/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1103).cutoff/(generalMeanRows 1103).c)).2 =
    (397188285489327/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1103).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1103).q*(generalMeanRows 1103).c/2-2 = (1181/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable360.value]
  have hcontinuation : (generalMeanRows 1103).q*(generalMeanRows 1103).cutoff/2-2 = (311/150:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable369.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1103).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1103).criticalRate j.val*(generalMeanRows 1103).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1103).c*(generalMeanRows 1103).criticalPoint j.val)).2-
      (generalMeanRows 1103).J/2-(generalMeanRows 1103).error (generalMeanGrid j.val)+
      (generalMeanRows 1103).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1103).c)).2-
      (generalMeanRows 1103).J/2-(generalMeanRows 1103).error 4 := by
  have he : (generalMeanRows 1103).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1103) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1103)
    (generalMeanRows_prefactorDomain 1103) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1103

/-! Kernel-checked entropy margins for general spectral rectangle 1104. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1104
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6587260080) (.branch 2 (.leaf 6392564576) (.leaf 6205638756))) (.branch 5 (.branch 4 (.leaf 6026063238) (.leaf 5853447995)) (.branch 6 (.leaf 5687429767) (.leaf 5527669747)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5373851519) (.leaf 5225679210)) (.branch 10 (.leaf 5082875829) (.leaf 4945181769))) (.branch 13 (.branch 12 (.leaf 4812353460) (.leaf 4684162143)) (.branch 14 (.leaf 4560392763) (.leaf 4440842958))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4325322145) (.branch 17 (.leaf 4213650678) (.leaf 4105659087))) (.branch 20 (.branch 19 (.leaf 4001187368) (.leaf 3900084350)) (.branch 21 (.leaf 3802207097) (.leaf 3707420363)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3615596098) (.leaf 3526612980)) (.branch 25 (.leaf 3440355987) (.leaf 3356716007))) (.branch 28 (.branch 27 (.leaf 3275589468) (.leaf 3196878001)) (.branch 29 (.leaf 3120488125) (.leaf 3046330952)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2974321920) (.branch 32 (.leaf 2904380537) (.leaf 2836430144))) (.branch 35 (.branch 34 (.leaf 2770397697) (.leaf 2706213562)) (.branch 36 (.leaf 2643811323) (.leaf 2583127603)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2524101895) (.leaf 2466676407)) (.branch 40 (.leaf 2410795915) (.leaf 2356407624))) (.branch 43 (.branch 42 (.leaf 2303461039) (.leaf 2251907845)) (.branch 44 (.leaf 2201701794) (.leaf 2152798593))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2105155809) (.branch 47 (.leaf 2058732774) (.leaf 2013490491))) (.branch 50 (.branch 49 (.leaf 1969391555) (.leaf 1926400071)) (.branch 51 (.leaf 1884481584) (.leaf 1843603002)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1803732537) (.leaf 1764839635)) (.branch 55 (.leaf 1726894923) (.leaf 1689870151))) (.branch 58 (.branch 57 (.leaf 1653738138) (.leaf 1618472726)) (.branch 59 (.leaf 1584048727) (.leaf 1550441883))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1517628823) (.branch 62 (.leaf 1485587019) (.leaf 1454294757))) (.branch 65 (.branch 64 (.leaf 1423731089) (.leaf 1393875810)) (.branch 66 (.leaf 1364709420) (.leaf 1336213092)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1308368648) (.leaf 1281158527)) (.branch 70 (.leaf 1254565761) (.leaf 1228573950))) (.branch 73 (.branch 72 (.leaf 1203167237) (.leaf 1178330287)) (.branch 74 (.leaf 1154048263) (.leaf 1130306809))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1107092030) (.branch 77 (.leaf 1084390469) (.leaf 1062189098))) (.branch 80 (.branch 79 (.leaf 1040475292) (.leaf 1019236820)) (.branch 81 (.leaf 998461825) (.leaf 978138814)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 958256640) (.leaf 938804491)) (.branch 85 (.leaf 919771877) (.leaf 901148618))) (.branch 88 (.branch 87 (.leaf 882924834) (.leaf 865090930)) (.branch 89 (.leaf 847637589) (.leaf 830555763)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 813836659) (.branch 92 (.leaf 797471732) (.leaf 781452680))) (.branch 95 (.branch 94 (.leaf 765771429) (.leaf 750420129)) (.branch 96 (.leaf 735391146) (.leaf 720677054)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 706270628) (.leaf 692164836)) (.branch 100 (.leaf 678352837) (.leaf 664827969))) (.branch 103 (.branch 102 (.leaf 651583746) (.leaf 638613853)) (.branch 104 (.leaf 625912139) (.leaf 613472612))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 601289434) (.leaf 589356916)) (.branch 108 (.leaf 577669516) (.leaf 566221829))) (.branch 111 (.branch 110 (.leaf 555008587) (.leaf 544024655)) (.branch 112 (.leaf 533265023) (.leaf 522724807)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 512399242) (.leaf 502283680)) (.branch 116 (.leaf 492373587) (.leaf 482664536))) (.branch 119 (.branch 118 (.leaf 473152210) (.leaf 463832394)) (.branch 120 (.leaf 454700972) (.leaf 445753928)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1104).prefactor = (1072578819339483/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1104).cutoff/(generalMeanRows 1104).c)).2 =
    (192694369279087/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1104).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1104).q*(generalMeanRows 1104).c/2-2 = (1233/1600:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable363.value]
  have hcontinuation : (generalMeanRows 1104).q*(generalMeanRows 1104).cutoff/2-2 = (311/150:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable369.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1104).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1104).criticalRate j.val*(generalMeanRows 1104).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1104).c*(generalMeanRows 1104).criticalPoint j.val)).2-
      (generalMeanRows 1104).J/2-(generalMeanRows 1104).error (generalMeanGrid j.val)+
      (generalMeanRows 1104).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1104).c)).2-
      (generalMeanRows 1104).J/2-(generalMeanRows 1104).error 4 := by
  have he : (generalMeanRows 1104).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1104) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1104)
    (generalMeanRows_prefactorDomain 1104) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1104

/-! Kernel-checked entropy margins for general spectral rectangle 1105. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1105
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6415719298) (.branch 2 (.leaf 6213930596) (.leaf 6020366195))) (.branch 5 (.branch 4 (.leaf 5834583773) (.leaf 5656171762)) (.branch 6 (.leaf 5484746641) (.leaf 5319950524)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5161449001) (.leaf 5008929214)) (.branch 10 (.leaf 4862098116) (.leaf 4720680907))) (.branch 13 (.branch 12 (.leaf 4584419629) (.leaf 4453071880)) (.branch 14 (.leaf 4326409661) (.leaf 4204218317))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4086295582) (.branch 17 (.leaf 3972450697) (.leaf 3862503612))) (.branch 20 (.branch 19 (.leaf 3756284253) (.leaf 3653631845)) (.branch 21 (.leaf 3554394297) (.leaf 3458427630)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3365595454) (.leaf 3275768482)) (.branch 25 (.leaf 3188824084) (.leaf 3104645874))) (.branch 28 (.branch 27 (.leaf 3023123322) (.leaf 2944151406)) (.branch 29 (.leaf 2867630274) (.leaf 2793464943)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2721565011) (.branch 32 (.leaf 2651844391) (.leaf 2584221065))) (.branch 35 (.branch 34 (.leaf 2518616854) (.leaf 2454957199)) (.branch 36 (.leaf 2393170961) (.leaf 2333190234)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2274950167) (.leaf 2218388801)) (.branch 40 (.leaf 2163446911) (.leaf 2110067864))) (.branch 43 (.branch 42 (.leaf 2058197482) (.leaf 2007783913)) (.branch 44 (.leaf 1958777512) (.leaf 1911130727))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1864797996) (.branch 47 (.leaf 1819735642) (.leaf 1775901783))) (.branch 50 (.branch 49 (.leaf 1733256242) (.leaf 1691760462)) (.branch 51 (.leaf 1651377429) (.leaf 1612071598)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1573808819) (.leaf 1536556276)) (.branch 55 (.leaf 1500282421) (.leaf 1464956913))) (.branch 58 (.branch 57 (.leaf 1430550566) (.leaf 1397035296)) (.branch 59 (.leaf 1364384066) (.leaf 1332570842))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1301570549) (.branch 62 (.leaf 1271359025) (.leaf 1241912984))) (.branch 65 (.branch 64 (.leaf 1213209973) (.leaf 1185228341)) (.branch 66 (.leaf 1157947202) (.leaf 1131346399)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1105406479) (.leaf 1080108660)) (.branch 70 (.leaf 1055434801) (.leaf 1031367379))) (.branch 73 (.branch 72 (.leaf 1007889462) (.leaf 984984683)) (.branch 74 (.leaf 962637221) (.leaf 940831774))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 919553543) (.branch 77 (.leaf 898788210) (.leaf 878521915))) (.branch 80 (.branch 79 (.leaf 858741247) (.leaf 839433218)) (.branch 81 (.leaf 820585251) (.leaf 802185164)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 784221152) (.leaf 766681779)) (.branch 85 (.leaf 749555957) (.leaf 732832936))) (.branch 88 (.branch 87 (.leaf 716502296) (.leaf 700553925)) (.branch 89 (.leaf 684978018) (.leaf 669765059)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 654905815) (.branch 92 (.leaf 640391322) (.leaf 626212880))) (.branch 95 (.branch 94 (.leaf 612362038) (.leaf 598830592)) (.branch 96 (.leaf 585610570) (.leaf 572694230)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 560074047) (.leaf 547742710)) (.branch 100 (.leaf 535693110) (.leaf 523918339))) (.branch 103 (.branch 102 (.leaf 512411678) (.leaf 501166595)) (.branch 104 (.leaf 490176736) (.leaf 479435919))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 468938133) (.leaf 458677527)) (.branch 108 (.leaf 448648407) (.leaf 438845231))) (.branch 111 (.branch 110 (.leaf 429262607) (.leaf 419895283)) (.branch 112 (.leaf 410738146) (.leaf 401786218)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 393034651) (.leaf 384478722)) (.branch 116 (.leaf 376113830) (.leaf 367935495))) (.branch 119 (.branch 118 (.leaf 359939351) (.leaf 352121141)) (.branch 120 (.leaf 344476721) (.leaf 337002049)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1105).prefactor = (5613281860133697/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1105).cutoff/(generalMeanRows 1105).c)).2 =
    (178242496187913/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1105).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1105).q*(generalMeanRows 1105).cutoff/2-2 = (311/150:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable369.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1105).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1105).criticalRate j.val*(generalMeanRows 1105).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1105).c*(generalMeanRows 1105).criticalPoint j.val)).2-
      (generalMeanRows 1105).J/2-(generalMeanRows 1105).error (generalMeanGrid j.val)+
      (generalMeanRows 1105).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1105).c)).2-
      (generalMeanRows 1105).J/2-(generalMeanRows 1105).error 4 := by
  have he : (generalMeanRows 1105).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1105) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1105)
    (generalMeanRows_prefactorDomain 1105) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1105

/-! Kernel-checked entropy margins for general spectral rectangle 1106. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1106
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6351417000) (.branch 2 (.leaf 6162038631) (.leaf 5980284438))) (.branch 5 (.branch 4 (.leaf 5805738317) (.leaf 5638013521)) (.branch 6 (.leaf 5476750059) (.leaf 5321612394)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5172287368) (.leaf 5028482356)) (.branch 10 (.leaf 4889923597) (.leaf 4756354698))) (.branch 13 (.branch 12 (.leaf 4627535274) (.leaf 4503239725)) (.branch 14 (.leaf 4383256123) (.leaf 4267385195))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4155439410) (.branch 17 (.leaf 4047242126) (.leaf 3942626834))) (.branch 20 (.branch 19 (.leaf 3841436443) (.leaf 3743522639)) (.branch 21 (.leaf 3648745290) (.leaf 3556971904)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3468077121) (.leaf 3381942250)) (.branch 25 (.leaf 3298454846) (.leaf 3217508308))) (.branch 28 (.branch 27 (.leaf 3139001515) (.leaf 3062838488)) (.branch 29 (.leaf 2988928072) (.leaf 2917183645)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2847522847) (.branch 32 (.leaf 2779867327) (.leaf 2714142504))) (.branch 35 (.branch 34 (.leaf 2650277354) (.leaf 2588204201)) (.branch 36 (.leaf 2527858525) (.leaf 2469178789)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2412106267) (.leaf 2356584891)) (.branch 40 (.leaf 2302561105) (.leaf 2249983727))) (.branch 43 (.branch 42 (.leaf 2198803821) (.leaf 2148974578)) (.branch 44 (.leaf 2100451205) (.leaf 2053190814))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2007152327) (.branch 47 (.leaf 1962296382) (.leaf 1918585244))) (.branch 50 (.branch 49 (.leaf 1875982723) (.leaf 1834454096)) (.branch 51 (.leaf 1793966036) (.leaf 1754486538)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1715984858) (.leaf 1678431453)) (.branch 55 (.leaf 1641797918) (.leaf 1606056935))) (.branch 58 (.branch 57 (.leaf 1571182221) (.leaf 1537148479)) (.branch 59 (.leaf 1503931352) (.leaf 1471507379))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1439853955) (.branch 62 (.leaf 1408949290) (.leaf 1378772375))) (.branch 65 (.branch 64 (.leaf 1349302944) (.leaf 1320521445)) (.branch 66 (.leaf 1292409003) (.leaf 1264947395)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1238119020) (.leaf 1211906874)) (.branch 70 (.leaf 1186294522) (.leaf 1161266074))) (.branch 73 (.branch 72 (.leaf 1136806164) (.leaf 1112899930)) (.branch 74 (.leaf 1089532987) (.leaf 1066691415))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1044361733) (.branch 77 (.leaf 1022530888) (.leaf 1001186233))) (.branch 80 (.branch 79 (.leaf 980315514) (.leaf 959906852)) (.branch 81 (.leaf 939948733) (.leaf 920429989)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 901339785) (.leaf 882667613)) (.branch 85 (.leaf 864403271) (.leaf 846536857))) (.branch 88 (.branch 87 (.leaf 829058756) (.leaf 811959632)) (.branch 89 (.leaf 795230415) (.leaf 778862292)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 762846698) (.branch 92 (.leaf 747175309) (.leaf 731840033))) (.branch 95 (.branch 94 (.leaf 716832998) (.leaf 702146551)) (.branch 96 (.leaf 687773245) (.leaf 673705836)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 659937273) (.leaf 646460693)) (.branch 100 (.leaf 633269417) (.leaf 620356938))) (.branch 103 (.branch 102 (.leaf 607716924) (.leaf 595343204)) (.branch 104 (.leaf 583229767) (.leaf 571370759))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 559760472) (.leaf 548393347)) (.branch 108 (.leaf 537263961) (.leaf 526367031))) (.branch 111 (.branch 110 (.leaf 515697404) (.leaf 505250056)) (.branch 112 (.leaf 495020086) (.leaf 485002715)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 475193281) (.leaf 465587234)) (.branch 116 (.leaf 456180136) (.leaf 446967656))) (.branch 119 (.branch 118 (.leaf 437945566) (.leaf 429109739)) (.branch 120 (.leaf 420456148) (.leaf 411980860)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1106).prefactor = (5326634503011033/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1106).cutoff/(generalMeanRows 1106).c)).2 =
    (403021288159517/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1106).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1106).q*(generalMeanRows 1106).c/2-2 = (99/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable367.value]
  have hcontinuation : (generalMeanRows 1106).q*(generalMeanRows 1106).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable092.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1106).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1106).criticalRate j.val*(generalMeanRows 1106).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1106).c*(generalMeanRows 1106).criticalPoint j.val)).2-
      (generalMeanRows 1106).J/2-(generalMeanRows 1106).error (generalMeanGrid j.val)+
      (generalMeanRows 1106).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1106).c)).2-
      (generalMeanRows 1106).J/2-(generalMeanRows 1106).error 4 := by
  have he : (generalMeanRows 1106).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1106) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1106)
    (generalMeanRows_prefactorDomain 1106) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1106

/-! Kernel-checked entropy margins for general spectral rectangle 1107. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1107
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6431899795) (.branch 2 (.leaf 6235226165) (.leaf 6046537852))) (.branch 5 (.branch 4 (.leaf 5865399771) (.leaf 5691407443)) (.branch 6 (.leaf 5524184298) (.leaf 5363379262)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5208664610) (.leaf 5059734034)) (.branch 10 (.leaf 4916300910) (.leaf 4778096736))) (.branch 13 (.branch 12 (.leaf 4644869720) (.leaf 4516383501)) (.branch 14 (.leaf 4392415990) (.leaf 4272758319))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4157213873) (.branch 17 (.leaf 4045597420) (.leaf 3937734310))) (.branch 20 (.branch 19 (.leaf 3833459733) (.leaf 3732618057)) (.branch 21 (.leaf 3635062199) (.leaf 3540653064)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3449259017) (.leaf 3360755399)) (.branch 25 (.leaf 3275024086) (.leaf 3191953066))) (.branch 28 (.branch 27 (.leaf 3111436068) (.leaf 3033372202)) (.branch 29 (.leaf 2957665627) (.leaf 2884225257)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2812964464) (.branch 32 (.leaf 2743800824) (.leaf 2676655868))) (.branch 35 (.branch 34 (.leaf 2611454852) (.leaf 2548126546)) (.branch 36 (.leaf 2486603031) (.leaf 2426819515)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2368714162) (.leaf 2312227922)) (.branch 40 (.leaf 2257304385) (.leaf 2203889635))) (.branch 43 (.branch 42 (.leaf 2151932116) (.leaf 2101382508)) (.branch 44 (.leaf 2052193610) (.leaf 2004320225))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1957719061) (.branch 47 (.leaf 1912348630) (.leaf 1868169158))) (.branch 50 (.branch 49 (.leaf 1825142498) (.leaf 1783232048)) (.branch 51 (.leaf 1742402674) (.leaf 1702620640)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1663853538) (.leaf 1626070222)) (.branch 55 (.leaf 1589240753) (.leaf 1553336334))) (.branch 58 (.branch 57 (.leaf 1518329263) (.leaf 1484192878)) (.branch 59 (.leaf 1450901510) (.leaf 1418430435))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1386755835) (.branch 62 (.leaf 1355854754) (.leaf 1325705058))) (.branch 65 (.branch 64 (.leaf 1296285404) (.leaf 1267575199)) (.branch 66 (.leaf 1239554570) (.leaf 1212204332)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1185505959) (.leaf 1159441556)) (.branch 70 (.leaf 1133993832) (.leaf 1109146072))) (.branch 73 (.branch 72 (.leaf 1084882119) (.leaf 1061186345)) (.branch 74 (.leaf 1038043631) (.leaf 1015439349))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 993359340) (.branch 77 (.leaf 971789894) (.leaf 950717736))) (.branch 80 (.branch 79 (.leaf 930130003) (.leaf 910014234)) (.branch 81 (.leaf 890358354) (.leaf 871150652)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 852379777) (.leaf 834034717)) (.branch 85 (.leaf 816104792) (.leaf 798579636))) (.branch 88 (.branch 87 (.leaf 781449189) (.leaf 764703686)) (.branch 89 (.leaf 748333646) (.leaf 732329860)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 716683383) (.branch 92 (.leaf 701385524) (.leaf 686427839))) (.branch 95 (.branch 94 (.leaf 671802120) (.leaf 657500388)) (.branch 96 (.leaf 643514884) (.leaf 629838063)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 616462588) (.leaf 603381320)) (.branch 100 (.leaf 590587312) (.leaf 578073806))) (.branch 103 (.branch 102 (.leaf 565834222) (.leaf 553862157)) (.branch 104 (.leaf 542151376) (.leaf 530695807))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 519489538) (.leaf 508526809)) (.branch 108 (.leaf 497802010) (.leaf 487309676))) (.branch 111 (.branch 110 (.leaf 477044481) (.leaf 467001232)) (.branch 112 (.leaf 457174873) (.leaf 447560470)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 438153217) (.leaf 428948426)) (.branch 116 (.leaf 419941525) (.leaf 411128058))) (.branch 119 (.branch 118 (.leaf 402503675) (.leaf 394064137)) (.branch 120 (.leaf 385805305) (.leaf 377723143)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1107).prefactor = (5552663320647293/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1107).cutoff/(generalMeanRows 1107).c)).2 =
    (391625153428649/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1107).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1107).q*(generalMeanRows 1107).c/2-2 = (103/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable365.value]
  have hcontinuation : (generalMeanRows 1107).q*(generalMeanRows 1107).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable092.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1107).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1107).criticalRate j.val*(generalMeanRows 1107).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1107).c*(generalMeanRows 1107).criticalPoint j.val)).2-
      (generalMeanRows 1107).J/2-(generalMeanRows 1107).error (generalMeanGrid j.val)+
      (generalMeanRows 1107).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1107).c)).2-
      (generalMeanRows 1107).J/2-(generalMeanRows 1107).error 4 := by
  have he : (generalMeanRows 1107).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1107) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1107)
    (generalMeanRows_prefactorDomain 1107) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1107

/-! Kernel-checked entropy margins for general spectral rectangle 1108. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1108
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6167973764) (.branch 2 (.leaf 5984154313) (.leaf 5807771233))) (.branch 5 (.branch 4 (.leaf 5638413880) (.leaf 5475700871)) (.branch 6 (.leaf 5319277495) (.leaf 5168813401)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5024000529) (.leaf 4884551264)) (.branch 10 (.leaf 4750196762) (.leaf 4620685453))) (.branch 13 (.branch 12 (.leaf 4495781684) (.leaf 4375264487)) (.branch 14 (.leaf 4258926469) (.leaf 4146572797))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4038020270) (.branch 17 (.leaf 3933096485) (.leaf 3831639060))) (.branch 20 (.branch 19 (.leaf 3733494933) (.leaf 3638519713)) (.branch 21 (.leaf 3546577089) (.leaf 3457538283)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3371281547) (.leaf 3287691701)) (.branch 25 (.leaf 3206659704) (.leaf 3128082260))) (.branch 28 (.branch 27 (.leaf 3051861455) (.leaf 2977904411)) (.branch 29 (.leaf 2906122983) (.leaf 2836433459)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2768756294) (.branch 32 (.leaf 2703015859) (.leaf 2639140204))) (.branch 35 (.branch 34 (.leaf 2577060846) (.leaf 2516712562)) (.branch 36 (.leaf 2458033201) (.leaf 2400963508)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2345446961) (.leaf 2291429612)) (.branch 40 (.leaf 2238859951) (.leaf 2187688764))) (.branch 43 (.branch 42 (.leaf 2137869012) (.leaf 2089355711)) (.branch 44 (.leaf 2042105819) (.leaf 1996078139))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1951233216) (.branch 47 (.leaf 1907533245) (.leaf 1864941991))) (.branch 50 (.branch 49 (.leaf 1823424703) (.leaf 1782948040)) (.branch 51 (.leaf 1743479999) (.leaf 1704989851)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1667448074) (.leaf 1630826295)) (.branch 55 (.leaf 1595097232) (.leaf 1560234647))) (.branch 58 (.branch 57 (.leaf 1526213288) (.leaf 1493008848)) (.branch 59 (.leaf 1460597919) (.leaf 1428957949))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1398067201) (.branch 62 (.leaf 1367904721) (.leaf 1338450296))) (.branch 65 (.branch 64 (.leaf 1309684425) (.leaf 1281588286)) (.branch 66 (.leaf 1254143705) (.leaf 1227333128)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1201139595) (.leaf 1175546714)) (.branch 70 (.leaf 1150538636) (.leaf 1126100032))) (.branch 73 (.branch 72 (.leaf 1102216073) (.leaf 1078872408)) (.branch 74 (.leaf 1056055143) (.leaf 1033750825))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1011946424) (.branch 77 (.leaf 990629313) (.leaf 969787255))) (.branch 80 (.branch 79 (.leaf 949408387) (.leaf 929481205)) (.branch 81 (.leaf 909994550) (.leaf 890937597)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 872299838) (.leaf 854071076)) (.branch 85 (.leaf 836241408) (.leaf 818801217))) (.branch 88 (.branch 87 (.leaf 801741161) (.leaf 785052163)) (.branch 89 (.leaf 768725402) (.leaf 752752303)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 737124531) (.branch 92 (.leaf 721833977) (.leaf 706872756))) (.branch 95 (.branch 94 (.leaf 692233199) (.leaf 677907840)) (.branch 96 (.leaf 663889415) (.leaf 650170854)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 636745272) (.leaf 623605968)) (.branch 100 (.leaf 610746413) (.leaf 598160248))) (.branch 103 (.branch 102 (.leaf 585841280) (.leaf 573783472)) (.branch 104 (.leaf 561980943) (.leaf 550427961))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 539118937) (.leaf 528048424)) (.branch 108 (.leaf 517211109) (.leaf 506601812))) (.branch 111 (.branch 110 (.leaf 496215482) (.leaf 486047189)) (.branch 112 (.leaf 476092126) (.leaf 466345602)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 456803041) (.leaf 447459975)) (.branch 116 (.leaf 438312045) (.leaf 429354995))) (.branch 119 (.branch 118 (.leaf 420584672) (.leaf 411997019)) (.branch 120 (.leaf 403588077) (.leaf 395353978)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1108).prefactor = (527644327818319/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1108).cutoff/(generalMeanRows 1108).c)).2 =
    (42572209392871/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1108).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1108).q*(generalMeanRows 1108).c/2-2 = (1607/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable174.value]
  have hcontinuation : (generalMeanRows 1108).q*(generalMeanRows 1108).cutoff/2-2 = (527/230:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable370.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1108).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1108).criticalRate j.val*(generalMeanRows 1108).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1108).c*(generalMeanRows 1108).criticalPoint j.val)).2-
      (generalMeanRows 1108).J/2-(generalMeanRows 1108).error (generalMeanGrid j.val)+
      (generalMeanRows 1108).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1108).c)).2-
      (generalMeanRows 1108).J/2-(generalMeanRows 1108).error 4 := by
  have he : (generalMeanRows 1108).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1108) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1108)
    (generalMeanRows_prefactorDomain 1108) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1108

/-! Kernel-checked entropy margins for general spectral rectangle 1109. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1109
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6314912391) (.branch 2 (.leaf 6124311491) (.leaf 5941454593))) (.branch 5 (.branch 4 (.leaf 5765914453) (.leaf 5597294229)) (.branch 6 (.leaf 5435224788) (.leaf 5279362307)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5129386128) (.leaf 4984996837)) (.branch 10 (.leaf 4845914529) (.leaf 4711877252))) (.branch 13 (.branch 12 (.leaf 4582639600) (.leaf 4457971430)) (.branch 14 (.leaf 4337656712) (.leaf 4221492475))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4109287842) (.branch 17 (.leaf 4000863165) (.leaf 3896049217))) (.branch 20 (.branch 19 (.leaf 3794686464) (.leaf 3696624395)) (.branch 21 (.leaf 3601720899) (.leaf 3509841705)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3420859859) (.leaf 3334655237)) (.branch 25 (.leaf 3251114110) (.leaf 3170128725))) (.branch 28 (.branch 27 (.leaf 3091596931) (.leaf 3015421824)) (.branch 29 (.leaf 2941511425) (.leaf 2869778372)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2800139645) (.branch 32 (.leaf 2732516301) (.leaf 2666833233))) (.branch 35 (.branch 34 (.leaf 2603018942) (.leaf 2541005331)) (.branch 36 (.leaf 2480727502) (.leaf 2422123576)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2365134524) (.leaf 2309704002)) (.branch 40 (.leaf 2255778206) (.leaf 2203305731))) (.branch 43 (.branch 42 (.leaf 2152237435) (.leaf 2102526326)) (.branch 44 (.leaf 2054127436) (.leaf 2006997722))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1961095960) (.branch 47 (.leaf 1916382650) (.leaf 1872819929))) (.branch 50 (.branch 49 (.leaf 1830371485) (.leaf 1789002480)) (.branch 51 (.leaf 1748679472) (.leaf 1709370351)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1671044268) (.leaf 1633671574)) (.branch 55 (.leaf 1597223764) (.leaf 1561673420))) (.branch 58 (.branch 57 (.leaf 1526994158) (.leaf 1493160582)) (.branch 59 (.leaf 1460148234) (.leaf 1427933554))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1396493836) (.branch 62 (.leaf 1365807188) (.leaf 1335852499))) (.branch 65 (.branch 64 (.leaf 1306609400) (.leaf 1278058235)) (.branch 66 (.leaf 1250180025) (.leaf 1222956441)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1196369775) (.leaf 1170402915)) (.branch 70 (.leaf 1145039317) (.leaf 1120262983))) (.branch 73 (.branch 72 (.leaf 1096058438) (.leaf 1072410707)) (.branch 74 (.leaf 1049305297) (.leaf 1026728173))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1004665746) (.branch 77 (.leaf 983104849) (.leaf 962032723))) (.branch 80 (.branch 79 (.leaf 941437003) (.leaf 921305698)) (.branch 81 (.leaf 901627181) (.leaf 882390173)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 863583730) (.leaf 845197231)) (.branch 85 (.leaf 827220365) (.leaf 809643122))) (.branch 88 (.branch 87 (.leaf 792455779) (.leaf 775648890)) (.branch 89 (.leaf 759213280) (.leaf 743140031)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 727420474) (.branch 92 (.leaf 712046182) (.leaf 697008960))) (.branch 95 (.branch 94 (.leaf 682300837) (.leaf 667914061)) (.branch 96 (.leaf 653841086) (.leaf 640074573)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 626607377) (.leaf 613432542)) (.branch 100 (.leaf 600543297) (.leaf 587933046))) (.branch 103 (.branch 102 (.leaf 575595369) (.leaf 563524010)) (.branch 104 (.leaf 551712873) (.leaf 540156020))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 528847666) (.leaf 517782169)) (.branch 108 (.leaf 506954032) (.leaf 496357895))) (.branch 111 (.branch 110 (.leaf 485988534) (.leaf 475840851)) (.branch 112 (.leaf 465909878) (.leaf 456190767)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 446678790) (.leaf 437369334)) (.branch 116 (.leaf 428257899) (.leaf 419340092))) (.branch 119 (.branch 118 (.leaf 410611628) (.leaf 402068325)) (.branch 120 (.leaf 393706100) (.leaf 385520966)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1109).prefactor = (5481224001317099/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1109).cutoff/(generalMeanRows 1109).c)).2 =
    (210059919190021/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1109).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hcontinuation : (generalMeanRows 1109).q*(generalMeanRows 1109).cutoff/2-2 = (527/230:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable370.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1109).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1109).criticalRate j.val*(generalMeanRows 1109).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1109).c*(generalMeanRows 1109).criticalPoint j.val)).2-
      (generalMeanRows 1109).J/2-(generalMeanRows 1109).error (generalMeanGrid j.val)+
      (generalMeanRows 1109).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1109).c)).2-
      (generalMeanRows 1109).J/2-(generalMeanRows 1109).error 4 := by
  have he : (generalMeanRows 1109).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1109) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1109)
    (generalMeanRows_prefactorDomain 1109) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1109

/-! Kernel-checked entropy margins for general spectral rectangle 1110. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1110
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6281407741) (.branch 2 (.leaf 6084679373) (.leaf 5896051614))) (.branch 5 (.branch 4 (.leaf 5715078467) (.leaf 5541345535)) (.branch 6 (.leaf 5374467227) (.leaf 5214084272)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5059861493) (.leaf 4911485811)) (.branch 10 (.leaf 4768664449) (.leaf 4631123313))) (.branch 13 (.branch 12 (.leaf 4498605535) (.leaf 4370870141)) (.branch 14 (.leaf 4247690858) (.leaf 4128855014))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4014162547) (.branch 17 (.leaf 3903425095) (.leaf 3796465167))) (.branch 20 (.branch 19 (.leaf 3693115381) (.leaf 3593217767)) (.branch 21 (.leaf 3496623127) (.leaf 3403190446)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3312786350) (.leaf 3225284604)) (.branch 25 (.leaf 3140565652) (.leaf 3058516192))) (.branch 28 (.branch 27 (.leaf 2979028776) (.leaf 2902001450)) (.branch 29 (.leaf 2827337411) (.leaf 2754944694)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2684735880) (.branch 32 (.leaf 2616627824) (.leaf 2550541401))) (.branch 35 (.branch 34 (.leaf 2486401271) (.leaf 2424135662)) (.branch 36 (.leaf 2363676161) (.leaf 2304957527)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2247917508) (.leaf 2192496679)) (.branch 40 (.leaf 2138638284) (.leaf 2086288087))) (.branch 43 (.branch 42 (.leaf 2035394241) (.leaf 1985907154)) (.branch 44 (.leaf 1937779373) (.leaf 1890965469))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1845421931) (.branch 47 (.leaf 1801107070) (.leaf 1757980920))) (.branch 50 (.branch 49 (.leaf 1716005154) (.leaf 1675143000)) (.branch 51 (.leaf 1635359165) (.leaf 1596619759)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1558892227) (.leaf 1522145286)) (.branch 55 (.leaf 1486348860) (.leaf 1451474026))) (.branch 58 (.branch 57 (.leaf 1417492956) (.leaf 1384378867)) (.branch 59 (.leaf 1352105973) (.leaf 1320649438))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1289985333) (.branch 62 (.leaf 1260090594) (.leaf 1230942983))) (.branch 65 (.branch 64 (.leaf 1202521053) (.leaf 1174804112)) (.branch 66 (.leaf 1147772187) (.leaf 1121405999)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1095686927) (.leaf 1070596985)) (.branch 70 (.leaf 1046118790) (.leaf 1022235540))) (.branch 73 (.branch 72 (.leaf 998930991) (.leaf 976189430)) (.branch 74 (.leaf 953995657) (.leaf 932334963))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 911193109) (.branch 77 (.leaf 890556308) (.leaf 870411210))) (.branch 80 (.branch 79 (.leaf 850744881) (.leaf 831544787)) (.branch 81 (.leaf 812798784) (.leaf 794495095)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 776622303) (.leaf 759169334)) (.branch 85 (.leaf 742125447) (.leaf 725480217))) (.branch 88 (.branch 87 (.leaf 709223528) (.leaf 693345561)) (.branch 89 (.leaf 677836783) (.leaf 662687934)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 647890023) (.branch 92 (.leaf 633434313) (.leaf 619312317))) (.branch 95 (.branch 94 (.leaf 605515785) (.leaf 592036701)) (.branch 96 (.leaf 578867269) (.leaf 565999910)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 553427255) (.leaf 541142135)) (.branch 100 (.leaf 529137577) (.leaf 517406796))) (.branch 103 (.branch 102 (.leaf 505943192) (.leaf 494740337)) (.branch 104 (.leaf 483791980) (.leaf 473092033))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 462634568) (.leaf 452413815)) (.branch 108 (.leaf 442424152) (.leaf 432660106))) (.branch 111 (.branch 110 (.leaf 423116345) (.leaf 413787674)) (.branch 112 (.leaf 404669031) (.leaf 395755486)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 387042232) (.leaf 378524585)) (.branch 116 (.leaf 370197980) (.leaf 362057966))) (.branch 119 (.branch 118 (.leaf 354100205) (.leaf 346320465)) (.branch 120 (.leaf 338714621) (.leaf 331278652)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1110).prefactor = (5693952340365049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1110).cutoff/(generalMeanRows 1110).c)).2 =
    (50437369643/125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1110).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1110).q*(generalMeanRows 1110).c/2-2 = (1733/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable177.value]
  have hcontinuation : (generalMeanRows 1110).q*(generalMeanRows 1110).cutoff/2-2 = (527/230:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable370.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1110).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1110).criticalRate j.val*(generalMeanRows 1110).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1110).c*(generalMeanRows 1110).criticalPoint j.val)).2-
      (generalMeanRows 1110).J/2-(generalMeanRows 1110).error (generalMeanGrid j.val)+
      (generalMeanRows 1110).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1110).c)).2-
      (generalMeanRows 1110).J/2-(generalMeanRows 1110).error 4 := by
  have he : (generalMeanRows 1110).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1110) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1110)
    (generalMeanRows_prefactorDomain 1110) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1110

/-! Kernel-checked entropy margins for general spectral rectangle 1111. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1111
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6249993024) (.branch 2 (.leaf 6047192584) (.leaf 5852860081))) (.branch 5 (.branch 4 (.leaf 5666529805) (.leaf 5487768907)) (.branch 6 (.leaf 5316174501) (.leaf 5151371084)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4993008224) (.leaf 4840758491)) (.branch 10 (.leaf 4694315591) (.leaf 4553392687))) (.branch 13 (.branch 12 (.leaf 4417720883) (.leaf 4287047847)) (.branch 14 (.leaf 4161136563) (.leaf 4039764199))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3922721070) (.branch 17 (.leaf 3809809695) (.leaf 3700843938))) (.branch 20 (.branch 19 (.leaf 3595648212) (.leaf 3494056757)) (.branch 21 (.leaf 3395912976) (.leaf 3301068820)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3209384225) (.leaf 3120726591)) (.branch 25 (.leaf 3034970305) (.leaf 2951996292))) (.branch 28 (.branch 27 (.leaf 2871691608) (.leaf 2793949059)) (.branch 29 (.leaf 2718666846) (.leaf 2645748238)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2575101271) (.branch 32 (.leaf 2506638458) (.leaf 2440276534))) (.branch 35 (.branch 34 (.leaf 2375936201) (.leaf 2313541908)) (.branch 36 (.leaf 2253021632) (.leaf 2194306681)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2137331506) (.leaf 2082033529)) (.branch 40 (.leaf 2028352977) (.leaf 1976232734))) (.branch 43 (.branch 42 (.leaf 1925618193) (.leaf 1876457125)) (.branch 44 (.leaf 1828699552) (.leaf 1782297631))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1737205540) (.branch 47 (.leaf 1693379377) (.leaf 1650777060))) (.branch 50 (.branch 49 (.leaf 1609358237) (.leaf 1569084197)) (.branch 51 (.leaf 1529917789) (.leaf 1491823348)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1454766619) (.leaf 1418714689)) (.branch 55 (.leaf 1383635925) (.leaf 1349499912))) (.branch 58 (.branch 57 (.leaf 1316277395) (.leaf 1283940226)) (.branch 59 (.leaf 1252461309) (.leaf 1221814559))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1191974849) (.branch 62 (.leaf 1162917969) (.leaf 1134620586))) (.branch 65 (.branch 64 (.leaf 1107060205) (.leaf 1080215131)) (.branch 66 (.leaf 1054064435) (.leaf 1028587919)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1003766088) (.leaf 979580117)) (.branch 70 (.leaf 956011824) (.leaf 933043646))) (.branch 73 (.branch 72 (.leaf 910658606) (.leaf 888840296)) (.branch 74 (.leaf 867572852) (.leaf 846840929))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 826629684) (.branch 77 (.leaf 806924754) (.leaf 787712238))) (.branch 80 (.branch 79 (.leaf 768978679) (.leaf 750711045)) (.branch 81 (.leaf 732896715) (.leaf 715523462)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 698579439) (.leaf 682053164)) (.branch 85 (.leaf 665933507) (.leaf 650209676))) (.branch 88 (.branch 87 (.leaf 634871207) (.leaf 619907947)) (.branch 89 (.leaf 605310051) (.leaf 591067962)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 577172408) (.branch 92 (.leaf 563614387) (.leaf 550385162))) (.branch 95 (.branch 94 (.leaf 537476246) (.leaf 524879401)) (.branch 96 (.leaf 512586621) (.leaf 500590132)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 488882380) (.leaf 477456023)) (.branch 100 (.leaf 466303926) (.leaf 455419154))) (.branch 103 (.branch 102 (.leaf 444794965) (.leaf 434424804)) (.branch 104 (.leaf 424302296) (.leaf 414421242))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 404775611) (.leaf 395359537)) (.branch 108 (.leaf 386167313) (.leaf 377193387))) (.branch 111 (.branch 110 (.leaf 368432354) (.leaf 359878955)) (.branch 112 (.leaf 351528072) (.leaf 343374721)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 335414052) (.leaf 327641342)) (.branch 116 (.leaf 320051991) (.leaf 312641521))) (.branch 119 (.branch 118 (.leaf 305405571) (.leaf 298339892)) (.branch 120 (.leaf 291440348) (.leaf 284702905)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1111).prefactor = (5914936745252171/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1111).cutoff/(generalMeanRows 1111).c)).2 =
    (387149819142471/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1111).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1111).q*(generalMeanRows 1111).c/2-2 = (731/800:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable371.value]
  have hcontinuation : (generalMeanRows 1111).q*(generalMeanRows 1111).cutoff/2-2 = (527/230:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable370.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1111).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1111).criticalRate j.val*(generalMeanRows 1111).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1111).c*(generalMeanRows 1111).criticalPoint j.val)).2-
      (generalMeanRows 1111).J/2-(generalMeanRows 1111).error (generalMeanGrid j.val)+
      (generalMeanRows 1111).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1111).c)).2-
      (generalMeanRows 1111).J/2-(generalMeanRows 1111).error 4 := by
  have he : (generalMeanRows 1111).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1111) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1111)
    (generalMeanRows_prefactorDomain 1111) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1111

/-! Kernel-checked entropy margins for general spectral rectangle 1112. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1112
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6586259728) (.branch 2 (.leaf 6375020903) (.leaf 6172560957))) (.branch 5 (.branch 4 (.leaf 5978396954) (.leaf 5792080080)) (.branch 6 (.leaf 5613192632) (.leaf 5441345335)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5276174944) (.leaf 5117342091)) (.branch 10 (.leaf 4964529344) (.leaf 4817439471))) (.branch 13 (.branch 12 (.leaf 4675793855) (.leaf 4539331068)) (.branch 14 (.leaf 4407805575) (.leaf 4280986557))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4158656835) (.branch 17 (.leaf 4040611889) (.leaf 3926658964))) (.branch 20 (.branch 19 (.leaf 3816616247) (.leaf 3710312116)) (.branch 21 (.leaf 3607584450) (.leaf 3508279989)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3412253752) (.leaf 3319368496)) (.branch 25 (.leaf 3229494214) (.leaf 3142507682))) (.branch 28 (.branch 27 (.leaf 3058292023) (.leaf 2976736320)) (.branch 29 (.leaf 2897735243) (.leaf 2821188715)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2747001591) (.branch 32 (.leaf 2675083366) (.leaf 2605347904))) (.branch 35 (.branch 34 (.leaf 2537713179) (.leaf 2472101042)) (.branch 36 (.leaf 2408436996) (.leaf 2346649989)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2286672225) (.leaf 2228438980)) (.branch 40 (.leaf 2171888431) (.leaf 2116961505))) (.branch 43 (.branch 42 (.leaf 2063601722) (.leaf 2011755064)) (.branch 44 (.leaf 1961369838) (.leaf 1912396559))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1864787831) (.branch 47 (.leaf 1818498243) (.leaf 1773484266))) (.branch 50 (.branch 49 (.leaf 1729704157) (.leaf 1687117867)) (.branch 51 (.leaf 1645686964) (.leaf 1605374545)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1566145168) (.leaf 1527964775)) (.branch 55 (.leaf 1490800630) (.leaf 1454621254))) (.branch 58 (.branch 57 (.leaf 1419396368) (.leaf 1385096833)) (.branch 59 (.leaf 1351694599) (.leaf 1319162656))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1287474985) (.branch 62 (.leaf 1256606515) (.leaf 1226533077))) (.branch 65 (.branch 64 (.leaf 1197231367) (.leaf 1168678908)) (.branch 66 (.leaf 1140854013) (.leaf 1113735749)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1087303908) (.leaf 1061538973)) (.branch 70 (.leaf 1036422093) (.leaf 1011935049))) (.branch 73 (.branch 72 (.leaf 988060233) (.leaf 964780623)) (.branch 74 (.leaf 942079754) (.leaf 919941701))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 898351054) (.branch 77 (.leaf 877292900) (.leaf 856752800))) (.branch 80 (.branch 79 (.leaf 836716776) (.leaf 817171286)) (.branch 81 (.leaf 798103212) (.leaf 779499846)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 761348868) (.leaf 743638335)) (.branch 85 (.leaf 726356669) (.leaf 709492640))) (.branch 88 (.branch 87 (.leaf 693035355) (.leaf 676974246)) (.branch 89 (.leaf 661299056) (.leaf 645999833)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 631066913) (.branch 92 (.leaf 616490914) (.leaf 602262726))) (.branch 95 (.branch 94 (.leaf 588373500) (.leaf 574814640)) (.branch 96 (.leaf 561577793) (.leaf 548654844)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 536037903) (.leaf 523719305)) (.branch 100 (.leaf 511691594) (.leaf 499947522))) (.branch 103 (.branch 102 (.leaf 488480041) (.leaf 477282295)) (.branch 104 (.leaf 466347616) (.leaf 455669516))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 445241684) (.leaf 435057975)) (.branch 108 (.leaf 425112414) (.leaf 415399180))) (.branch 111 (.branch 110 (.leaf 405912611) (.leaf 396647190)) (.branch 112 (.leaf 387597551) (.leaf 378758464)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 370124837) (.leaf 361691713)) (.branch 116 (.leaf 353454260) (.leaf 345407773))) (.branch 119 (.branch 118 (.leaf 337547668) (.leaf 329869479)) (.branch 120 (.leaf 322368854) (.leaf 315041550)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1112).prefactor = (3072248818479861/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1112).cutoff/(generalMeanRows 1112).c)).2 =
    (392569886611811/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1112).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1112).q*(generalMeanRows 1112).c/2-2 = (449/500:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable336.value]
  have hcontinuation : (generalMeanRows 1112).q*(generalMeanRows 1112).cutoff/2-2 = (527/230:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable370.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1112).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1112).criticalRate j.val*(generalMeanRows 1112).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1112).c*(generalMeanRows 1112).criticalPoint j.val)).2-
      (generalMeanRows 1112).J/2-(generalMeanRows 1112).error (generalMeanGrid j.val)+
      (generalMeanRows 1112).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1112).c)).2-
      (generalMeanRows 1112).J/2-(generalMeanRows 1112).error 4 := by
  have he : (generalMeanRows 1112).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1112) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1112)
    (generalMeanRows_prefactorDomain 1112) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1112

/-! Kernel-checked entropy margins for general spectral rectangle 1113. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1113
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7041510256) (.branch 2 (.leaf 6820976121) (.leaf 6609522836))) (.branch 5 (.branch 4 (.leaf 6406650435) (.leaf 6211894375)) (.branch 6 (.leaf 6024822406) (.leaf 5845031781)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5672146765) (.leaf 5505816393)) (.branch 10 (.leaf 5345712459) (.leaf 5191527704))) (.branch 13 (.branch 12 (.leaf 5042974173) (.leaf 4899781736)) (.branch 14 (.leaf 4761696736) (.leaf 4628480768))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4499909559) (.branch 17 (.leaf 4375771956) (.leaf 4255868989))) (.branch 20 (.branch 19 (.leaf 4140013020) (.leaf 4028026965)) (.branch 21 (.leaf 3919743571) (.leaf 3815004760)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3713661017) (.leaf 3615570832)) (.branch 25 (.leaf 3520600184) (.leaf 3428622057))) (.branch 28 (.branch 27 (.leaf 3339516004) (.leaf 3253167732)) (.branch 29 (.leaf 3169468724) (.leaf 3088315887)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3009611224) (.branch 32 (.leaf 2933261527) (.leaf 2859178097))) (.branch 35 (.branch 34 (.leaf 2787276479) (.leaf 2717476214)) (.branch 36 (.leaf 2649700611) (.leaf 2583876534)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2519934199) (.leaf 2457806990)) (.branch 40 (.leaf 2397431281) (.leaf 2338746276))) (.branch 43 (.branch 42 (.leaf 2281693851) (.leaf 2226218416)) (.branch 44 (.leaf 2172266773) (.leaf 2119787998))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2068733314) (.branch 47 (.leaf 2019055987) (.leaf 1970711214))) (.branch 50 (.branch 49 (.leaf 1923656032) (.leaf 1877849218)) (.branch 51 (.leaf 1833251208) (.leaf 1789824012)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1747531136) (.leaf 1706337510)) (.branch 55 (.leaf 1666209419) (.leaf 1627114440))) (.branch 58 (.branch 57 (.leaf 1589021378) (.leaf 1551900209)) (.branch 59 (.leaf 1515722027) (.leaf 1480458991))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1446084274) (.branch 62 (.leaf 1412572023) (.leaf 1379897309))) (.branch 65 (.branch 64 (.leaf 1348036090) (.leaf 1316965168)) (.branch 66 (.leaf 1286662156) (.leaf 1257105440)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1228274147) (.leaf 1200148113)) (.branch 70 (.leaf 1172707853) (.leaf 1145934532))) (.branch 73 (.branch 72 (.leaf 1119809938) (.leaf 1094316460)) (.branch 74 (.leaf 1069437056) (.leaf 1045155238))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1021455044) (.branch 77 (.leaf 998321019) (.leaf 975738197))) (.branch 80 (.branch 79 (.leaf 953692078) (.leaf 932168614)) (.branch 81 (.leaf 911154188) (.leaf 890635601)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 870600053) (.leaf 851035130)) (.branch 85 (.leaf 831928790) (.leaf 813269349))) (.branch 88 (.branch 87 (.leaf 795045466) (.leaf 777246134)) (.branch 89 (.leaf 759860664) (.leaf 742878679)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 726290097) (.branch 92 (.leaf 710085127) (.leaf 694254252))) (.branch 95 (.branch 94 (.leaf 678788225) (.leaf 663678060)) (.branch 96 (.leaf 648915017) (.leaf 634490601)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 620396550) (.leaf 606624829)) (.branch 100 (.leaf 593167619) (.leaf 580017317))) (.branch 103 (.branch 102 (.leaf 567166520) (.leaf 554608028)) (.branch 104 (.leaf 542334829) (.leaf 530340099))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 518617194) (.leaf 507159644)) (.branch 108 (.leaf 495961149) (.leaf 485015573))) (.branch 111 (.branch 110 (.leaf 474316937) (.leaf 463859419)) (.branch 112 (.leaf 453637345) (.leaf 443645187)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 433877557) (.leaf 424329204)) (.branch 116 (.leaf 414995011) (.leaf 405869988))) (.branch 119 (.branch 118 (.leaf 396949271) (.leaf 388228117)) (.branch 120 (.leaf 379701904) (.leaf 371366121)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1113).prefactor = (6382967872126253/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1113).cutoff/(generalMeanRows 1113).c)).2 =
    (50437369643/125000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1113).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1113).q*(generalMeanRows 1113).c/2-2 = (1733/2000:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable177.value]
  have hcontinuation : (generalMeanRows 1113).q*(generalMeanRows 1113).cutoff/2-2 = (527/230:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable370.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1113).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1113).criticalRate j.val*(generalMeanRows 1113).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1113).c*(generalMeanRows 1113).criticalPoint j.val)).2-
      (generalMeanRows 1113).J/2-(generalMeanRows 1113).error (generalMeanGrid j.val)+
      (generalMeanRows 1113).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1113).c)).2-
      (generalMeanRows 1113).J/2-(generalMeanRows 1113).error 4 := by
  have he : (generalMeanRows 1113).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1113) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1113)
    (generalMeanRows_prefactorDomain 1113) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1113

/-! Kernel-checked entropy margins for general spectral rectangle 1114. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1114
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7529252128) (.branch 2 (.leaf 7299140828) (.leaf 7078419925))) (.branch 5 (.branch 4 (.leaf 6866571755) (.leaf 6663115436)) (.branch 6 (.leaf 6467603612) (.leaf 6279619555)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6098774570) (.leaf 5924705671)) (.branch 10 (.leaf 5757073483) (.leaf 5595560364))) (.branch 13 (.branch 12 (.leaf 5439868696) (.leaf 5289719344)) (.branch 14 (.leaf 5144850256) (.leaf 5005015192))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4869982560) (.branch 17 (.leaf 4739534363) (.leaf 4613465228))) (.branch 20 (.branch 19 (.leaf 4491581521) (.leaf 4373700538)) (.branch 21 (.leaf 4259649756) (.leaf 4149266148)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4042395552) (.leaf 3938892088)) (.branch 25 (.leaf 3838617624) (.leaf 3741441273))) (.branch 28 (.branch 27 (.leaf 3647238940) (.leaf 3555892893)) (.branch 29 (.leaf 3467291370) (.leaf 3381328211)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3297902521) (.branch 32 (.leaf 3216918352) (.leaf 3138284411))) (.branch 35 (.branch 34 (.leaf 3061913783) (.leaf 2987723679)) (.branch 36 (.leaf 2915635196) (.leaf 2845573096)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2777465601) (.leaf 2711244194)) (.branch 40 (.leaf 2646843441) (.leaf 2584200822))) (.branch 43 (.branch 42 (.leaf 2523256572) (.leaf 2463953530)) (.branch 44 (.leaf 2406237001) (.leaf 2350054627))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2295356261) (.branch 47 (.leaf 2242093854) (.leaf 2190221347))) (.branch 50 (.branch 49 (.leaf 2139694566) (.leaf 2090471130)) (.branch 51 (.leaf 2042510359) (.leaf 1995773191)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1950222098) (.leaf 1905821015)) (.branch 55 (.leaf 1862535269) (.leaf 1820331508))) (.branch 58 (.branch 57 (.leaf 1779177643) (.leaf 1739042784)) (.branch 59 (.leaf 1699897187) (.leaf 1661712200))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1624460211) (.branch 62 (.leaf 1588114602) (.leaf 1552649705))) (.branch 65 (.branch 64 (.leaf 1518040758) (.leaf 1484263864)) (.branch 66 (.leaf 1451295956) (.leaf 1419114756)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1387698748) (.leaf 1357027137)) (.branch 70 (.leaf 1327079824) (.leaf 1297837376))) (.branch 73 (.branch 72 (.leaf 1269280996) (.leaf 1241392501)) (.branch 74 (.leaf 1214154290) (.leaf 1187549327))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1161561115) (.branch 77 (.leaf 1136173676) (.leaf 1111371528))) (.branch 80 (.branch 79 (.leaf 1087139670) (.leaf 1063463557)) (.branch 81 (.leaf 1040329091) (.leaf 1017722594)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 995630801) (.leaf 974040839)) (.branch 85 (.leaf 952940216) (.leaf 932316803))) (.branch 88 (.branch 87 (.leaf 912158826) (.leaf 892454847)) (.branch 89 (.leaf 873193758) (.leaf 854364766)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 835957383) (.branch 92 (.leaf 817961412) (.leaf 800366945))) (.branch 95 (.branch 94 (.leaf 783164343) (.leaf 766344236)) (.branch 96 (.leaf 749897506) (.leaf 733815286)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 718088947) (.leaf 702710089)) (.branch 100 (.leaf 687670540) (.leaf 672962341))) (.branch 103 (.branch 102 (.leaf 658577745) (.leaf 644509208)) (.branch 104 (.leaf 630749380) (.leaf 617291105))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 604127410) (.leaf 591251500)) (.branch 108 (.leaf 578656756) (.leaf 566336725))) (.branch 111 (.branch 110 (.leaf 554285118) (.leaf 542495804)) (.branch 112 (.leaf 530962807) (.leaf 519680298)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 508642595) (.leaf 497844155)) (.branch 116 (.leaf 487279571) (.leaf 476943571))) (.branch 119 (.branch 118 (.leaf 466831010) (.leaf 456936869)) (.branch 120 (.leaf 447256250) (.leaf 437784374)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1114).prefactor = (132613864513601/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1114).cutoff/(generalMeanRows 1114).c)).2 =
    (414548793330587/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1114).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1114).q*(generalMeanRows 1114).c/2-2 = (167/200:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable082.value]
  have hcontinuation : (generalMeanRows 1114).q*(generalMeanRows 1114).cutoff/2-2 = (527/230:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable370.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1114).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1114).criticalRate j.val*(generalMeanRows 1114).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1114).c*(generalMeanRows 1114).criticalPoint j.val)).2-
      (generalMeanRows 1114).J/2-(generalMeanRows 1114).error (generalMeanGrid j.val)+
      (generalMeanRows 1114).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1114).c)).2-
      (generalMeanRows 1114).J/2-(generalMeanRows 1114).error 4 := by
  have he : (generalMeanRows 1114).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1114) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1114)
    (generalMeanRows_prefactorDomain 1114) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1114

/-! Kernel-checked entropy margins for general spectral rectangle 1115. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1115
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8164854046) (.branch 2 (.leaf 7927754067) (.leaf 7700166119))) (.branch 5 (.branch 4 (.leaf 7481563804) (.leaf 7271458348)) (.branch 6 (.leaf 7069395260) (.leaf 6874951362)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6687732127) (.leaf 6507369293)) (.branch 10 (.leaf 6333518725) (.leaf 6165858472))) (.branch 13 (.branch 12 (.leaf 6004087031) (.leaf 5847921758)) (.branch 14 (.leaf 5697097440) (.leaf 5551364987))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5410490243) (.branch 17 (.leaf 5274252907) (.leaf 5142445539))) (.branch 20 (.branch 19 (.leaf 5014872653) (.leaf 4891349885)) (.branch 21 (.leaf 4771703235) (.leaf 4655768357)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4543389919) (.leaf 4434421005)) (.branch 25 (.leaf 4328722564) (.leaf 4226162906))) (.branch 28 (.branch 27 (.leaf 4126617229) (.leaf 4029967183)) (.branch 29 (.leaf 3936100472) (.leaf 3844910476)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3756295903) (.branch 32 (.leaf 3670160471) (.leaf 3586412602))) (.branch 35 (.branch 34 (.leaf 3504965148) (.leaf 3425735127)) (.branch 36 (.leaf 3348643483) (.leaf 3273614857)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3200577377) (.leaf 3129462464)) (.branch 40 (.leaf 3060204639) (.leaf 2992741360))) (.branch 43 (.branch 42 (.leaf 2927012853) (.leaf 2862961967)) (.branch 44 (.leaf 2800534025) (.leaf 2739676698))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2680339876) (.branch 47 (.leaf 2622475553) (.leaf 2566037715))) (.branch 50 (.branch 49 (.leaf 2510982242) (.leaf 2457266802)) (.branch 51 (.leaf 2404850769) (.leaf 2353695130)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2303762411) (.leaf 2255016592)) (.branch 55 (.leaf 2207423046) (.leaf 2160948461))) (.branch 58 (.branch 57 (.leaf 2115560784) (.leaf 2071229158)) (.branch 59 (.leaf 2027923864) (.leaf 1985616269))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1944278775) (.branch 62 (.leaf 1903884772) (.leaf 1864408592))) (.branch 65 (.branch 64 (.leaf 1825825466) (.leaf 1788111485)) (.branch 66 (.leaf 1751243559) (.leaf 1715199383)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1679957404) (.leaf 1645496785)) (.branch 70 (.leaf 1611797375) (.leaf 1578839684))) (.branch 73 (.branch 72 (.leaf 1546604849) (.leaf 1515074611)) (.branch 74 (.leaf 1484231292) (.leaf 1454057766))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1424537442) (.branch 77 (.leaf 1395654239) (.leaf 1367392568))) (.branch 80 (.branch 79 (.leaf 1339737308) (.leaf 1312673796)) (.branch 81 (.leaf 1286187801) (.leaf 1260265511)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1234893520) (.leaf 1210058805)) (.branch 85 (.leaf 1185748722) (.leaf 1161950981))) (.branch 88 (.branch 87 (.leaf 1138653643) (.leaf 1115845101)) (.branch 89 (.leaf 1093514070) (.leaf 1071649575)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1050240942) (.branch 92 (.leaf 1029277787) (.leaf 1008750003))) (.branch 95 (.branch 94 (.leaf 988647755) (.leaf 968961466)) (.branch 96 (.leaf 949681813) (.leaf 930799717)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 912306332) (.leaf 894193043)) (.branch 100 (.leaf 876451454) (.leaf 859073382))) (.branch 103 (.branch 102 (.leaf 842050852) (.leaf 825376087)) (.branch 104 (.leaf 809041507) (.leaf 793039718))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 777363508) (.leaf 762005845)) (.branch 108 (.leaf 746959863) (.leaf 732218867))) (.branch 111 (.branch 110 (.leaf 717776322) (.leaf 703625849)) (.branch 112 (.leaf 689761221) (.leaf 676176360)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 662865331) (.leaf 649822338)) (.branch 116 (.leaf 637041721) (.leaf 624517951))) (.branch 119 (.branch 118 (.leaf 612245629) (.leaf 600219479)) (.branch 120 (.leaf 588434345) (.leaf 576885193)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1115).prefactor = (1695979936466597/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1115).cutoff/(generalMeanRows 1115).c)).2 =
    (109255412295661/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1115).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1115).q*(generalMeanRows 1115).c/2-2 = (193/250:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable071.value]
  have hcontinuation : (generalMeanRows 1115).q*(generalMeanRows 1115).cutoff/2-2 = (527/230:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable370.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1115).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1115).criticalRate j.val*(generalMeanRows 1115).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1115).c*(generalMeanRows 1115).criticalPoint j.val)).2-
      (generalMeanRows 1115).J/2-(generalMeanRows 1115).error (generalMeanGrid j.val)+
      (generalMeanRows 1115).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1115).c)).2-
      (generalMeanRows 1115).J/2-(generalMeanRows 1115).error 4 := by
  have he : (generalMeanRows 1115).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1115) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1115)
    (generalMeanRows_prefactorDomain 1115) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1115

/-! Kernel-checked entropy margins for general spectral rectangle 1116. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1116
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5436954367) (.branch 2 (.leaf 5253112993) (.leaf 5077154273))) (.branch 5 (.branch 4 (.leaf 4908634909) (.leaf 4747143447)) (.branch 6 (.leaf 4592297457) (.leaf 4443741012)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4301142432) (.leaf 4164192261)) (.branch 10 (.leaf 4032601445) (.leaf 3906099692))) (.branch 13 (.branch 12 (.leaf 3784433984) (.leaf 3667367234)) (.branch 14 (.leaf 3554677072) (.leaf 3446154725))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3341604018) (.branch 17 (.leaf 3240840447) (.leaf 3143690338))) (.branch 20 (.branch 19 (.leaf 3049990077) (.leaf 2959585405)) (.branch 21 (.leaf 2872330768) (.leaf 2788088727)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2706729403) (.leaf 2628129977)) (.branch 25 (.leaf 2552174227) (.leaf 2478752094))) (.branch 28 (.branch 27 (.leaf 2407759288) (.leaf 2339096920)) (.branch 29 (.leaf 2272671163) (.leaf 2208392938)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2146177619) (.branch 32 (.leaf 2085944764) (.leaf 2027617864))) (.branch 35 (.branch 34 (.leaf 1971124106) (.leaf 1916394157)) (.branch 36 (.leaf 1863361961) (.leaf 1811964547)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1762141857) (.leaf 1713836578)) (.branch 40 (.leaf 1666993989) (.leaf 1621561817))) (.branch 43 (.branch 42 (.leaf 1577490105) (.leaf 1534731082)) (.branch 44 (.leaf 1493239048) (.leaf 1452970265))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1413882847) (.branch 47 (.leaf 1375936674) (.leaf 1339093289))) (.branch 50 (.branch 49 (.leaf 1303315823) (.leaf 1268568905)) (.branch 51 (.leaf 1234818596) (.leaf 1202032310)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1170178754) (.leaf 1139227858)) (.branch 55 (.leaf 1109150722) (.leaf 1079919556))) (.branch 58 (.branch 57 (.leaf 1051507632) (.leaf 1023889227)) (.branch 59 (.leaf 997039584) (.leaf 970934862))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 945552097) (.branch 62 (.leaf 920869163) (.leaf 896864731))) (.branch 65 (.branch 64 (.leaf 873518237) (.leaf 850809849)) (.branch 66 (.leaf 828720431) (.leaf 807231518)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 786325284) (.leaf 765984517)) (.branch 70 (.leaf 746192591) (.leaf 726933445))) (.branch 73 (.branch 72 (.leaf 708191557) (.leaf 689951924)) (.branch 74 (.leaf 672200039) (.leaf 654921872))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 638103855) (.branch 77 (.leaf 621732855) (.leaf 605796168))) (.branch 80 (.branch 79 (.leaf 590281493) (.leaf 575176922)) (.branch 81 (.leaf 560470923) (.leaf 546152328)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 532210317) (.leaf 518634406)) (.branch 85 (.leaf 505414435) (.leaf 492540557))) (.branch 88 (.branch 87 (.leaf 480003224) (.leaf 467793180)) (.branch 89 (.leaf 455901447) (.leaf 444319320)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 433038350) (.branch 92 (.leaf 422050344) (.leaf 411347348))) (.branch 95 (.branch 94 (.leaf 400921647) (.leaf 390765748)) (.branch 96 (.leaf 380872380) (.leaf 371234482)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 361845200) (.leaf 352697876)) (.branch 100 (.leaf 343786043) (.leaf 335103421))) (.branch 103 (.branch 102 (.leaf 326643907) (.leaf 318401575)) (.branch 104 (.leaf 310370663) (.leaf 302545575))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 294920869) (.leaf 287491259)) (.branch 108 (.leaf 280251604) (.leaf 273196908))) (.branch 111 (.branch 110 (.leaf 266322314) (.leaf 259623098)) (.branch 112 (.leaf 253094667) (.leaf 246732555)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 240532420) (.leaf 234490035)) (.branch 116 (.leaf 228601291) (.leaf 222862193))) (.branch 119 (.branch 118 (.leaf 217268851) (.leaf 211817481)) (.branch 120 (.leaf 206504404) (.leaf 201326038)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1116).prefactor = (5662550296695723/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1116).cutoff/(generalMeanRows 1116).c)).2 =
    (208907495558603/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1116).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1116).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1116).criticalRate j.val*(generalMeanRows 1116).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1116).c*(generalMeanRows 1116).criticalPoint j.val)).2-
      (generalMeanRows 1116).J/2-(generalMeanRows 1116).error (generalMeanGrid j.val)+
      (generalMeanRows 1116).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1116).c)).2-
      (generalMeanRows 1116).J/2-(generalMeanRows 1116).error 4 := by
  have he : (generalMeanRows 1116).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1116) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1116)
    (generalMeanRows_prefactorDomain 1116) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1116

/-! Kernel-checked entropy margins for general spectral rectangle 1117. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1117
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6621885931) (.branch 2 (.leaf 6436870838) (.leaf 6259111830))) (.branch 5 (.branch 4 (.leaf 6088214719) (.leaf 5923813141)) (.branch 6 (.leaf 5765566085) (.leaf 5613155700)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5466285333) (.leaf 5324677774)) (.branch 10 (.leaf 5188073672) (.leaf 5056230120))) (.branch 13 (.branch 12 (.leaf 4928919364) (.leaf 4805927647)) (.branch 14 (.leaf 4687054152) (.leaf 4572110042))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4460917594) (.branch 17 (.leaf 4353309396) (.leaf 4249127623))) (.branch 20 (.branch 19 (.leaf 4148223372) (.leaf 4050456048)) (.branch 21 (.leaf 3955692804) (.leaf 3863808025)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3774682854) (.leaf 3688204751)) (.branch 25 (.leaf 3604267090) (.leaf 3522768784))) (.branch 28 (.branch 27 (.leaf 3443613937) (.leaf 3366711527)) (.branch 29 (.leaf 3291975101) (.leaf 3219322507)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3148675629) (.branch 32 (.leaf 3079960153) (.leaf 3013105341))) (.branch 35 (.branch 34 (.leaf 2948043825) (.leaf 2884711414)) (.branch 36 (.leaf 2823046910) (.leaf 2762991943)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2704490811) (.leaf 2647490332)) (.branch 40 (.leaf 2591939705) (.leaf 2537790385))) (.branch 43 (.branch 42 (.leaf 2484995955) (.leaf 2433512018)) (.branch 44 (.leaf 2383296083) (.leaf 2334307475))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2286507230) (.branch 47 (.leaf 2239858013) (.leaf 2194324033))) (.branch 50 (.branch 49 (.leaf 2149870962) (.leaf 2106465867)) (.branch 51 (.leaf 2064077132) (.leaf 2022674402)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1982228513) (.leaf 1942711438)) (.branch 55 (.leaf 1904096231) (.leaf 1866356976))) (.branch 58 (.branch 57 (.leaf 1829468735) (.leaf 1793407506)) (.branch 59 (.leaf 1758150176) (.leaf 1723674479))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1689958961) (.branch 62 (.leaf 1656982937) (.leaf 1624726463))) (.branch 65 (.branch 64 (.leaf 1593170296) (.leaf 1562295866)) (.branch 66 (.leaf 1532085247) (.leaf 1502521126)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1473586778) (.leaf 1445266040)) (.branch 70 (.leaf 1417543288) (.leaf 1390403413))) (.branch 73 (.branch 72 (.leaf 1363831797) (.leaf 1337814297)) (.branch 74 (.leaf 1312337224) (.leaf 1287387321))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1262951748) (.branch 77 (.leaf 1239018067) (.leaf 1215574222))) (.branch 80 (.branch 79 (.leaf 1192608526) (.leaf 1170109645)) (.branch 81 (.leaf 1148066588) (.leaf 1126468686)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1105305590) (.leaf 1084567250)) (.branch 85 (.leaf 1064243907) (.leaf 1044326083))) (.branch 88 (.branch 87 (.leaf 1024804570) (.leaf 1005670418)) (.branch 89 (.leaf 986914929) (.leaf 968529646)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 950506343) (.branch 92 (.leaf 932837019) (.leaf 915513892))) (.branch 95 (.branch 94 (.leaf 898529385) (.leaf 881876124)) (.branch 96 (.leaf 865546932) (.leaf 849534815)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 833832966) (.leaf 818434751)) (.branch 100 (.leaf 803333707) (.leaf 788523533))) (.branch 103 (.branch 102 (.leaf 773998090) (.leaf 759751392)) (.branch 104 (.leaf 745777599) (.leaf 732071021))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 718626101) (.leaf 705437423)) (.branch 108 (.leaf 692499699) (.leaf 679807770))) (.branch 111 (.branch 110 (.leaf 667356597) (.leaf 655141266)) (.branch 112 (.leaf 643156973) (.leaf 631399032)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 619862863) (.leaf 608543993)) (.branch 116 (.leaf 597438052) (.leaf 586540770))) (.branch 119 (.branch 118 (.leaf 575847976) (.leaf 565355591)) (.branch 120 (.leaf 555059629) (.leaf 544956195)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1117).prefactor = (5106378666183709/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1117).cutoff/(generalMeanRows 1117).c)).2 =
    (83112760206057/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1117).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1117).q*(generalMeanRows 1117).c/2-2 = (89/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable368.value]
  have hcontinuation : (generalMeanRows 1117).q*(generalMeanRows 1117).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable123.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1117).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1117).criticalRate j.val*(generalMeanRows 1117).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1117).c*(generalMeanRows 1117).criticalPoint j.val)).2-
      (generalMeanRows 1117).J/2-(generalMeanRows 1117).error (generalMeanGrid j.val)+
      (generalMeanRows 1117).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1117).c)).2-
      (generalMeanRows 1117).J/2-(generalMeanRows 1117).error 4 := by
  have he : (generalMeanRows 1117).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1117) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1117)
    (generalMeanRows_prefactorDomain 1117) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1117

/-! Kernel-checked entropy margins for general spectral rectangle 1118. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1118
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6656918293) (.branch 2 (.leaf 6463315375) (.leaf 6277392252))) (.branch 5 (.branch 4 (.leaf 6098733326) (.leaf 5926952203)) (.branch 6 (.leaf 5761689113) (.leaf 5602608607)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5449397502) (.leaf 5301763037)) (.branch 10 (.leaf 5159431220) (.leaf 5022145337))) (.branch 13 (.branch 12 (.leaf 4889664605) (.leaf 4761762954)) (.branch 14 (.leaf 4638227922) (.leaf 4518859651))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4403469968) (.branch 17 (.leaf 4291881558) (.leaf 4183927194))) (.branch 20 (.branch 19 (.leaf 4079449040) (.leaf 3978298012)) (.branch 21 (.leaf 3880333188) (.leaf 3785421265)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3693436063) (.leaf 3604258063)) (.branch 25 (.leaf 3517773983) (.leaf 3433876383))) (.branch 28 (.branch 27 (.leaf 3352463304) (.leaf 3273437930)) (.branch 29 (.leaf 3196708271) (.leaf 3122186880)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3049790577) (.branch 32 (.leaf 2979440199) (.leaf 2911060367))) (.branch 35 (.branch 34 (.leaf 2844579267) (.leaf 2779928446)) (.branch 36 (.leaf 2717042623) (.leaf 2655859509)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2596319645) (.leaf 2538366243)) (.branch 40 (.leaf 2481945041) (.leaf 2427004168))) (.branch 43 (.branch 42 (.leaf 2373494016) (.leaf 2321367119)) (.branch 44 (.leaf 2270578039) (.leaf 2221083265))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2172841110) (.branch 47 (.leaf 2125811616) (.leaf 2079956470))) (.branch 50 (.branch 49 (.leaf 2035238920) (.leaf 1991623696)) (.branch 51 (.leaf 1949076937) (.leaf 1907566121)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1867060001) (.leaf 1827528544)) (.branch 55 (.leaf 1788942871) (.leaf 1751275202))) (.branch 58 (.branch 57 (.leaf 1714498806) (.leaf 1678587951)) (.branch 59 (.leaf 1643517857) (.leaf 1609264652))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1575805332) (.branch 62 (.leaf 1543117721) (.leaf 1511180433))) (.branch 65 (.branch 64 (.leaf 1479972838) (.leaf 1449475028)) (.branch 66 (.leaf 1419667784) (.leaf 1390532549)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1362051396) (.leaf 1334207004)) (.branch 70 (.leaf 1306982630) (.leaf 1280362088))) (.branch 73 (.branch 72 (.leaf 1254329721) (.leaf 1228870381)) (.branch 74 (.leaf 1203969411) (.leaf 1179612620))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1155786269) (.branch 77 (.leaf 1132477050) (.leaf 1109672067))) (.branch 80 (.branch 79 (.leaf 1087358826) (.leaf 1065525213)) (.branch 81 (.leaf 1044159482) (.leaf 1023250242)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1002786441) (.leaf 982757354)) (.branch 85 (.leaf 963152572) (.leaf 943961988))) (.branch 88 (.branch 87 (.leaf 925175788) (.leaf 906784440)) (.branch 89 (.leaf 888778682) (.leaf 871149513)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 853888187) (.branch 92 (.leaf 836986199) (.leaf 820435279))) (.branch 95 (.branch 94 (.leaf 804227383) (.leaf 788354688)) (.branch 96 (.leaf 772809580) (.leaf 757584650)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 742672687) (.leaf 728066670)) (.branch 100 (.leaf 713759762) (.leaf 699745306))) (.branch 103 (.branch 102 (.leaf 686016815) (.leaf 672567972)) (.branch 104 (.leaf 659392620) (.leaf 646484759))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 633838539) (.leaf 621448261)) (.branch 108 (.leaf 609308364) (.leaf 597413427))) (.branch 111 (.branch 110 (.leaf 585758164) (.leaf 574337416)) (.branch 112 (.leaf 563146152) (.leaf 552179463)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 541432557) (.leaf 530900759)) (.branch 116 (.leaf 520579504) (.leaf 510464337))) (.branch 119 (.branch 118 (.leaf 500550908) (.leaf 490834969)) (.branch 120 (.leaf 481312371) (.leaf 471979064)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1118).prefactor = (5362031197730797/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1118).cutoff/(generalMeanRows 1118).c)).2 =
    (24876218211211/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1118).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1118).q*(generalMeanRows 1118).c/2-2 = (19/25:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable075.value]
  have hcontinuation : (generalMeanRows 1118).q*(generalMeanRows 1118).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable123.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1118).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1118).criticalRate j.val*(generalMeanRows 1118).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1118).c*(generalMeanRows 1118).criticalPoint j.val)).2-
      (generalMeanRows 1118).J/2-(generalMeanRows 1118).error (generalMeanGrid j.val)+
      (generalMeanRows 1118).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1118).c)).2-
      (generalMeanRows 1118).J/2-(generalMeanRows 1118).error 4 := by
  have he : (generalMeanRows 1118).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1118) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1118)
    (generalMeanRows_prefactorDomain 1118) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1118

/-! Kernel-checked entropy margins for general spectral rectangle 1119. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1119
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6694413321) (.branch 2 (.leaf 6492127426) (.leaf 6297965100))) (.branch 5 (.branch 4 (.leaf 6111487975) (.leaf 5932288355)) (.branch 6 (.leaf 5759986515) (.leaf 5594228284)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5434682889) (.leaf 5281041027)) (.branch 10 (.leaf 5133013127) (.leaf 4990327783))) (.branch 13 (.branch 12 (.leaf 4852730351) (.leaf 4719981661)) (.branch 14 (.leaf 4591856865) (.leaf 4468144379))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4348644925) (.branch 17 (.leaf 4233170654) (.leaf 4121544347))) (.branch 20 (.branch 19 (.leaf 4013598678) (.leaf 3909175545)) (.branch 21 (.leaf 3808125450) (.leaf 3710306932)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3615586041) (.leaf 3523835858)) (.branch 25 (.leaf 3434936044) (.leaf 3348772432))) (.branch 28 (.branch 27 (.leaf 3265236642) (.leaf 3184225727)) (.branch 29 (.leaf 3105641845) (.leaf 3029391953)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2955387524) (.branch 32 (.leaf 2883544279) (.leaf 2813781946))) (.branch 35 (.branch 34 (.leaf 2746024028) (.leaf 2680197588)) (.branch 36 (.leaf 2616233048) (.leaf 2554064008)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2493627063) (.leaf 2434861646)) (.branch 40 (.leaf 2377709868) (.leaf 2322116383))) (.branch 43 (.branch 42 (.leaf 2268028244) (.leaf 2215394785)) (.branch 44 (.leaf 2164167495) (.leaf 2114299911))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2065747512) (.branch 47 (.leaf 2018467620) (.leaf 1972419305))) (.branch 50 (.branch 49 (.leaf 1927563304) (.leaf 1883861931)) (.branch 51 (.leaf 1841279004) (.leaf 1799779770)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1759330837) (.leaf 1719900110)) (.branch 55 (.leaf 1681456723) (.leaf 1643970991))) (.branch 58 (.branch 57 (.leaf 1607414345) (.leaf 1571759288)) (.branch 59 (.leaf 1536979341) (.leaf 1503048998))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1469943681) (.branch 62 (.leaf 1437639700) (.leaf 1406114214))) (.branch 65 (.branch 64 (.leaf 1375345188) (.leaf 1345311367)) (.branch 66 (.leaf 1315992233) (.leaf 1287367977)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1259419471) (.leaf 1232128236)) (.branch 70 (.leaf 1205476413) (.leaf 1179446744))) (.branch 73 (.branch 72 (.leaf 1154022537) (.leaf 1129187654)) (.branch 74 (.leaf 1104926478) (.leaf 1081223900))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1058065293) (.branch 77 (.leaf 1035436496) (.leaf 1013323795))) (.branch 80 (.branch 79 (.leaf 991713905) (.leaf 970593954)) (.branch 81 (.leaf 949951464) (.leaf 929774341)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 910050859) (.leaf 890769641)) (.branch 85 (.leaf 871919654) (.leaf 853490191))) (.branch 88 (.branch 87 (.leaf 835470860) (.leaf 817851572)) (.branch 89 (.leaf 800622534) (.leaf 783774232)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 767297427) (.branch 92 (.leaf 751183141) (.leaf 735422650))) (.branch 95 (.branch 94 (.leaf 720007475) (.leaf 704929374)) (.branch 96 (.leaf 690180333) (.leaf 675752556)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 661638464) (.leaf 647830682)) (.branch 100 (.leaf 634322034) (.leaf 621105537))) (.branch 103 (.branch 102 (.leaf 608174395) (.leaf 595521991)) (.branch 104 (.leaf 583141884) (.leaf 571027800))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 559173631) (.leaf 547573426)) (.branch 108 (.leaf 536221387) (.leaf 525111867))) (.branch 111 (.branch 110 (.leaf 514239361) (.leaf 503598505)) (.branch 112 (.leaf 493184070) (.leaf 482990959)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 473014203) (.leaf 463248955)) (.branch 116 (.leaf 453690491) (.leaf 444334201))) (.branch 119 (.branch 118 (.leaf 435175589) (.leaf 426210271)) (.branch 120 (.leaf 417433967) (.leaf 408842502)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1119).prefactor = (2815241528780497/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    GeneralPrefactorLogs.lower_eq_cache]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1119).cutoff/(generalMeanRows 1119).c)).2 =
    (380777684944869/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : Fin 121) :
    (generalMeanRows 1119).error (generalMeanGrid j.val) = errorValues j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
  have hfirst : (generalMeanRows 1119).q*(generalMeanRows 1119).c/2-2 = (101/125:ℚ) := by decide +kernel
  simp only [hfirst, GeneralMeanDecayTable286.value]
  have hcontinuation : (generalMeanRows 1119).q*(generalMeanRows 1119).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
  simp only [hcontinuation, GeneralMeanDecayTable123.value]
  try simp only [expUpperRoundedQ_eq_integer]
  simp only [resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]
  decide +kernel

private theorem criticalConditions (j : Fin 120) :
    0 < (generalMeanRows 1119).criticalRate j.val ∧
    0 ≤ 2+(generalMeanRows 1119).criticalRate j.val*(generalMeanRows 1119).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1119).c*(generalMeanRows 1119).criticalPoint j.val)).2-
      (generalMeanRows 1119).J/2-(generalMeanRows 1119).error (generalMeanGrid j.val)+
      (generalMeanRows 1119).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
    errorValue ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩]
  revert j
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1119).c)).2-
      (generalMeanRows 1119).J/2-(generalMeanRows 1119).error 4 := by
  have he : (generalMeanRows 1119).error 4 = errorValues 120 := by
    simpa only [generalMeanGrid_last] using errorValue (120 : Fin 121)
  rw [he]
  simp only [GeneralCriticalLogs.upper_eq_cache]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1119) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1119)
    (generalMeanRows_prefactorDomain 1119) (fun j => (criticalConditions j).1)
    (fun j => (criticalConditions j).2) finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1119

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock15 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 15 i) := by
  fin_cases i
  · exact EntropyRow1050.numerical
  · exact EntropyRow1051.numerical
  · exact EntropyRow1052.numerical
  · exact EntropyRow1053.numerical
  · exact EntropyRow1054.numerical
  · exact EntropyRow1055.numerical
  · exact EntropyRow1056.numerical
  · exact EntropyRow1057.numerical
  · exact EntropyRow1058.numerical
  · exact EntropyRow1059.numerical
  · exact EntropyRow1060.numerical
  · exact EntropyRow1061.numerical
  · exact EntropyRow1062.numerical
  · exact EntropyRow1063.numerical
  · exact EntropyRow1064.numerical
  · exact EntropyRow1065.numerical
  · exact EntropyRow1066.numerical
  · exact EntropyRow1067.numerical
  · exact EntropyRow1068.numerical
  · exact EntropyRow1069.numerical
  · exact EntropyRow1070.numerical
  · exact EntropyRow1071.numerical
  · exact EntropyRow1072.numerical
  · exact EntropyRow1073.numerical
  · exact EntropyRow1074.numerical
  · exact EntropyRow1075.numerical
  · exact EntropyRow1076.numerical
  · exact EntropyRow1077.numerical
  · exact EntropyRow1078.numerical
  · exact EntropyRow1079.numerical
  · exact EntropyRow1080.numerical
  · exact EntropyRow1081.numerical
  · exact EntropyRow1082.numerical
  · exact EntropyRow1083.numerical
  · exact EntropyRow1084.numerical
  · exact EntropyRow1085.numerical
  · exact EntropyRow1086.numerical
  · exact EntropyRow1087.numerical
  · exact EntropyRow1088.numerical
  · exact EntropyRow1089.numerical
  · exact EntropyRow1090.numerical
  · exact EntropyRow1091.numerical
  · exact EntropyRow1092.numerical
  · exact EntropyRow1093.numerical
  · exact EntropyRow1094.numerical
  · exact EntropyRow1095.numerical
  · exact EntropyRow1096.numerical
  · exact EntropyRow1097.numerical
  · exact EntropyRow1098.numerical
  · exact EntropyRow1099.numerical
  · exact EntropyRow1100.numerical
  · exact EntropyRow1101.numerical
  · exact EntropyRow1102.numerical
  · exact EntropyRow1103.numerical
  · exact EntropyRow1104.numerical
  · exact EntropyRow1105.numerical
  · exact EntropyRow1106.numerical
  · exact EntropyRow1107.numerical
  · exact EntropyRow1108.numerical
  · exact EntropyRow1109.numerical
  · exact EntropyRow1110.numerical
  · exact EntropyRow1111.numerical
  · exact EntropyRow1112.numerical
  · exact EntropyRow1113.numerical
  · exact EntropyRow1114.numerical
  · exact EntropyRow1115.numerical
  · exact EntropyRow1116.numerical
  · exact EntropyRow1117.numerical
  · exact EntropyRow1118.numerical
  · exact EntropyRow1119.numerical
end SingularValueBounds.KL.Certificates
