import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block17
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block20
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block22
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block23
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block24
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block25
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block26
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 1190. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1190
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7009657781) (.branch 2 (.leaf 6818163006) (.leaf 6633961054))) (.branch 5 (.branch 4 (.leaf 6456633299) (.leaf 6285793776)) (.branch 6 (.leaf 6121086088) (.leaf 5962180666)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5808772308) (.leaf 5660577994)) (.branch 10 (.leaf 5517334916) (.leaf 5378798716))) (.branch 13 (.branch 12 (.leaf 5244741897) (.leaf 5114952395)) (.branch 14 (.leaf 4989232286) (.leaf 4867396619))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4749272364) (.branch 17 (.leaf 4634697448) (.leaf 4523519891))) (.branch 20 (.branch 19 (.leaf 4415597013) (.leaf 4310794715)) (.branch 21 (.leaf 4208986828) (.leaf 4110054511)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4013885706) (.leaf 3920374645)) (.branch 25 (.leaf 3829421385) (.leaf 3740931400))) (.branch 28 (.branch 27 (.leaf 3654815189) (.leaf 3570987935)) (.branch 29 (.leaf 3489369171) (.leaf 3409882495)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3332455287) (.branch 32 (.leaf 3257018468) (.leaf 3183506259))) (.branch 35 (.branch 34 (.leaf 3111855977) (.leaf 3042007830)) (.branch 36 (.leaf 2973904742) (.leaf 2907492179)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2842718001) (.leaf 2779532309)) (.branch 40 (.leaf 2717887319) (.leaf 2657737236))) (.branch 43 (.branch 42 (.leaf 2599038140) (.leaf 2541747876)) (.branch 44 (.leaf 2485825961) (.leaf 2431233487))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2377933037) (.branch 47 (.leaf 2325888607) (.leaf 2275065529))) (.branch 50 (.branch 49 (.leaf 2225430404) (.leaf 2176951033)) (.branch 51 (.leaf 2129596363) (.leaf 2083336425)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2038142283) (.leaf 1993985986)) (.branch 55 (.leaf 1950840517) (.leaf 1908679756))) (.branch 58 (.branch 57 (.leaf 1867478432) (.leaf 1827212092)) (.branch 59 (.leaf 1787857056) (.leaf 1749390393))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1711789882) (.branch 62 (.leaf 1675033983) (.leaf 1639101809))) (.branch 65 (.branch 64 (.leaf 1603973104) (.leaf 1569628207)) (.branch 66 (.leaf 1536048039) (.leaf 1503214075)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1471108320) (.leaf 1439713297)) (.branch 70 (.leaf 1409012018) (.leaf 1378987973))) (.branch 73 (.branch 72 (.leaf 1349625110) (.leaf 1320907816)) (.branch 74 (.leaf 1292820908) (.leaf 1265349609))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1238479544) (.branch 77 (.leaf 1212196716) (.leaf 1186487501))) (.branch 80 (.branch 79 (.leaf 1161338634) (.leaf 1136737192)) (.branch 81 (.leaf 1112670591) (.leaf 1089126569)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1066093179) (.leaf 1043558775)) (.branch 85 (.leaf 1021512010) (.leaf 999941819))) (.branch 88 (.branch 87 (.leaf 978837415) (.leaf 958188279)) (.branch 89 (.leaf 937984153) (.leaf 918215032)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 898871154) (.branch 92 (.leaf 879942999) (.leaf 861421275))) (.branch 95 (.branch 94 (.leaf 843296917) (.leaf 825561077)) (.branch 96 (.leaf 808205120) (.leaf 791220618)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 774599342) (.leaf 758333261)) (.branch 100 (.leaf 742414531) (.leaf 726835495))) (.branch 103 (.branch 102 (.leaf 711588674) (.leaf 696666766)) (.branch 104 (.leaf 682062638) (.leaf 667769325))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 653780020) (.leaf 640088078)) (.branch 108 (.leaf 626687003) (.leaf 613570452))) (.branch 111 (.branch 110 (.leaf 600732226) (.leaf 588166268)) (.branch 112 (.leaf 575866660) (.leaf 563827617)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 552043489) (.leaf 540508751)) (.branch 116 (.leaf 529218005) (.leaf 518165974))) (.branch 119 (.branch 118 (.leaf 507347500) (.leaf 496757542)) (.branch 120 (.leaf 486391172) (.leaf 476243571)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1190).prefactor = (3039313265676763/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1190).cutoff/(generalMeanRows 1190).c)).2 =
    (629460917437909/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1190).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1190).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1190).q*(generalMeanRows 1190).c/2-2 = (1321/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable402.value]
    have hcontinuation : (generalMeanRows 1190).q*(generalMeanRows 1190).cutoff/2-2 = (644/195:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable400.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1190).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1190

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1190).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1190).criticalRate j.val*(generalMeanRows 1190).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1190).c*(generalMeanRows 1190).criticalPoint j.val)).2-
      (generalMeanRows 1190).J/2-(generalMeanRows 1190).error (generalMeanGrid j.val)+
      (generalMeanRows 1190).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1190).c)).2-
      (generalMeanRows 1190).J/2-(generalMeanRows 1190).error 4 := by
  have he : (generalMeanRows 1190).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1190) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1190)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1190

/-! Kernel-checked entropy margins for general spectral rectangle 1191. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1191
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5909408068) (.branch 2 (.leaf 5755400629) (.leaf 5607157437))) (.branch 5 (.branch 4 (.leaf 5464346969) (.leaf 5326663569)) (.branch 6 (.leaf 5193825015) (.leaf 5065570345)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4941657921) (.leaf 4821863698)) (.branch 10 (.leaf 4705979665) (.leaf 4593812456))) (.branch 13 (.branch 12 (.leaf 4485182088) (.leaf 4379920836)) (.branch 14 (.leaf 4277872204) (.leaf 4178890005))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4082837522) (.branch 17 (.leaf 3989586750) (.leaf 3899017703))) (.branch 20 (.branch 19 (.leaf 3811017791) (.leaf 3725481247)) (.branch 21 (.leaf 3642308607) (.leaf 3561406235)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3482685887) (.leaf 3406064321)) (.branch 25 (.leaf 3331462924) (.leaf 3258807388))) (.branch 28 (.branch 27 (.leaf 3188027402) (.leaf 3119056369)) (.branch 29 (.leaf 3051831153) (.leaf 2986291842)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2922381526) (.branch 32 (.leaf 2860046104) (.leaf 2799234093))) (.branch 35 (.branch 34 (.leaf 2739896459) (.leaf 2681986462)) (.branch 36 (.leaf 2625459509) (.leaf 2570273021)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2516386304) (.leaf 2463760443)) (.branch 40 (.leaf 2412358186) (.leaf 2362143851))) (.branch 43 (.branch 42 (.leaf 2313083233) (.leaf 2265143517)) (.branch 44 (.leaf 2218293202) (.leaf 2172502025))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2127740895) (.branch 47 (.leaf 2083981825) (.leaf 2041197877))) (.branch 50 (.branch 49 (.leaf 1999363105) (.leaf 1958452505)) (.branch 51 (.leaf 1918441961) (.leaf 1879308208)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1841028785) (.leaf 1803581995)) (.branch 55 (.leaf 1766946871) (.leaf 1731103140))) (.branch 58 (.branch 57 (.leaf 1696031189) (.leaf 1661712038)) (.branch 59 (.leaf 1628127308) (.leaf 1595259197))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1563090451) (.branch 62 (.leaf 1531604345) (.leaf 1500784656))) (.branch 65 (.branch 64 (.leaf 1470615645) (.leaf 1441082035)) (.branch 66 (.leaf 1412168995) (.leaf 1383862117)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1356147406) (.leaf 1329011259)) (.branch 70 (.leaf 1302440450) (.leaf 1276422120))) (.branch 73 (.branch 72 (.leaf 1250943760) (.leaf 1225993197)) (.branch 74 (.leaf 1201558585) (.leaf 1177628393))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1154191392) (.branch 77 (.leaf 1131236644) (.leaf 1108753497))) (.branch 80 (.branch 79 (.leaf 1086731570) (.leaf 1065160745)) (.branch 81 (.leaf 1044031162) (.leaf 1023333205)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1003057499) (.leaf 983194901)) (.branch 85 (.leaf 963736490) (.leaf 944673566))) (.branch 88 (.branch 87 (.leaf 925997636) (.leaf 907700413)) (.branch 89 (.leaf 889773810) (.leaf 872209930)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 855001063) (.branch 92 (.leaf 838139682) (.leaf 821618436))) (.branch 95 (.branch 94 (.leaf 805430144) (.leaf 789567792)) (.branch 96 (.leaf 774024529) (.leaf 758793659)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 743868643) (.leaf 729243086)) (.branch 100 (.leaf 714910743) (.leaf 700865505))) (.branch 103 (.branch 102 (.leaf 687101405) (.leaf 673612607)) (.branch 104 (.leaf 660393406) (.leaf 647438225))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 634741609) (.leaf 622298224)) (.branch 108 (.leaf 610102854) (.leaf 598150398))) (.branch 111 (.branch 110 (.leaf 586435867) (.leaf 574954378)) (.branch 112 (.leaf 563701158) (.leaf 552671535)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 541860939) (.leaf 531264900)) (.branch 116 (.leaf 520879043) (.leaf 510699087))) (.branch 119 (.branch 118 (.leaf 500720843) (.leaf 490940210)) (.branch 120 (.leaf 481353179) (.leaf 471955821)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1191).prefactor = (4827558022608169/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1191).cutoff/(generalMeanRows 1191).c)).2 =
    (19807815558021/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1191).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1191).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1191).q*(generalMeanRows 1191).c/2-2 = (1233/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable363.value]
    have hcontinuation : (generalMeanRows 1191).q*(generalMeanRows 1191).cutoff/2-2 = (29/9:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable403.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1191).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1191

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1191).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1191).criticalRate j.val*(generalMeanRows 1191).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1191).c*(generalMeanRows 1191).criticalPoint j.val)).2-
      (generalMeanRows 1191).J/2-(generalMeanRows 1191).error (generalMeanGrid j.val)+
      (generalMeanRows 1191).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1191).c)).2-
      (generalMeanRows 1191).J/2-(generalMeanRows 1191).error 4 := by
  have he : (generalMeanRows 1191).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1191) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1191)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1191

/-! Kernel-checked entropy margins for general spectral rectangle 1192. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1192
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6066706697) (.branch 2 (.leaf 5906527048) (.leaf 5752371599))) (.branch 5 (.branch 4 (.leaf 5603894468) (.leaf 5460776708)) (.branch 6 (.leaf 5322723767) (.leaf 5189463237)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5060742831) (.leaf 4936328587)) (.branch 10 (.leaf 4816003244) (.leaf 4699564800))) (.branch 13 (.branch 12 (.leaf 4586825194) (.leaf 4477609138)) (.branch 14 (.leaf 4371753047) (.leaf 4269104082))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4169519274) (.branch 17 (.leaf 4072864737) (.leaf 3979014948))) (.branch 20 (.branch 19 (.leaf 3887852096) (.leaf 3799265487)) (.branch 21 (.leaf 3713151003) (.leaf 3629410607)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3547951890) (.leaf 3468687660)) (.branch 25 (.leaf 3391535565) (.leaf 3316417741))) (.branch 28 (.branch 27 (.leaf 3243260503) (.leaf 3171994044)) (.branch 29 (.leaf 3102552176) (.leaf 3034872075)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2968894061) (.branch 32 (.leaf 2904561387) (.leaf 2841820046))) (.branch 35 (.branch 34 (.leaf 2780618591) (.leaf 2720907978)) (.branch 36 (.leaf 2662641408) (.leaf 2605774189)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2550263607) (.leaf 2496068806)) (.branch 40 (.leaf 2443150678) (.leaf 2391471755))) (.branch 43 (.branch 42 (.leaf 2340996119) (.leaf 2291689311)) (.branch 44 (.leaf 2243518248) (.leaf 2196451147))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2150457451) (.branch 47 (.leaf 2105507768) (.leaf 2061573803))) (.branch 50 (.branch 49 (.leaf 2018628303) (.leaf 1976645003)) (.branch 51 (.leaf 1935598577) (.leaf 1895464586)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1856219439) (.leaf 1817840350)) (.branch 55 (.leaf 1780305297) (.leaf 1743592991))) (.branch 58 (.branch 57 (.leaf 1707682837) (.leaf 1672554904)) (.branch 59 (.leaf 1638189895) (.leaf 1604569120))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1571674467) (.branch 62 (.leaf 1539488379) (.leaf 1507993831))) (.branch 65 (.branch 64 (.leaf 1477174303) (.leaf 1447013767)) (.branch 66 (.leaf 1417496661) (.leaf 1388607871)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1360332718) (.leaf 1332656934)) (.branch 70 (.leaf 1305566653) (.leaf 1279048392))) (.branch 73 (.branch 72 (.leaf 1253089038) (.leaf 1227675833)) (.branch 74 (.leaf 1202796365) (.leaf 1178438551))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1154590628) (.branch 77 (.leaf 1131241143) (.leaf 1108378940))) (.branch 80 (.branch 79 (.leaf 1085993151) (.leaf 1064073186)) (.branch 81 (.leaf 1042608726) (.leaf 1021589711)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1001006335) (.leaf 980849033)) (.branch 85 (.leaf 961108480) (.leaf 941775580))) (.branch 88 (.branch 87 (.leaf 922841457) (.leaf 904297453)) (.branch 89 (.leaf 886135119) (.leaf 868346207)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 850922668) (.branch 92 (.leaf 833856644) (.leaf 817140462))) (.branch 95 (.branch 94 (.leaf 800766631) (.leaf 784727835)) (.branch 96 (.leaf 769016928) (.leaf 753626930)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 738551023) (.leaf 723782546)) (.branch 100 (.leaf 709314990) (.leaf 695141996))) (.branch 103 (.branch 102 (.leaf 681257348) (.leaf 667654972)) (.branch 104 (.leaf 654328931) (.leaf 641273422))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 628482772) (.leaf 615951435)) (.branch 108 (.leaf 603673987) (.leaf 591645129))) (.branch 111 (.branch 110 (.leaf 579859674) (.leaf 568312554)) (.branch 112 (.leaf 556998810) (.leaf 545913594)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 535052163) (.leaf 524409879)) (.branch 116 (.leaf 513982202) (.leaf 503764696))) (.branch 119 (.branch 118 (.leaf 493753017) (.leaf 483942917)) (.branch 120 (.leaf 474330240) (.leaf 464910919)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1192).prefactor = (5026137004061431/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1192).cutoff/(generalMeanRows 1192).c)).2 =
    (628899592696813/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1192).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1192).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1192).q*(generalMeanRows 1192).cutoff/2-2 = (29/9:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable403.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1192).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1192

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1192).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1192).criticalRate j.val*(generalMeanRows 1192).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1192).c*(generalMeanRows 1192).criticalPoint j.val)).2-
      (generalMeanRows 1192).J/2-(generalMeanRows 1192).error (generalMeanGrid j.val)+
      (generalMeanRows 1192).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1192).c)).2-
      (generalMeanRows 1192).J/2-(generalMeanRows 1192).error 4 := by
  have he : (generalMeanRows 1192).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1192) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1192)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1192

/-! Kernel-checked entropy margins for general spectral rectangle 1193. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1193
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6141598107) (.branch 2 (.leaf 5975245447) (.leaf 5815211088))) (.branch 5 (.branch 4 (.leaf 5661133371) (.leaf 5512678686)) (.branch 6 (.leaf 5369538831) (.leaf 5231428669)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5098084030) (.leaf 4969259838)) (.branch 10 (.leaf 4844728429) (.leaf 4724278041))) (.branch 13 (.branch 12 (.leaf 4607711458) (.leaf 4494844782)) (.branch 14 (.leaf 4385506328) (.leaf 4279535624))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4176782502) (.branch 17 (.leaf 4077106281) (.leaf 3980375013))) (.branch 20 (.branch 19 (.leaf 3886464810) (.leaf 3795259223)) (.branch 21 (.leaf 3706648678) (.leaf 3620529962)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3536805750) (.leaf 3455384179)) (.branch 25 (.leaf 3376178454) (.leaf 3299106481))) (.branch 28 (.branch 27 (.leaf 3224090546) (.leaf 3151057001)) (.branch 29 (.leaf 3079935991) (.leaf 3010661197)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2943169595) (.branch 32 (.leaf 2877401243) (.leaf 2813299079))) (.branch 35 (.branch 34 (.leaf 2750808733) (.leaf 2689878359)) (.branch 36 (.leaf 2630458477) (.leaf 2572501822)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2515963216) (.leaf 2460799437)) (.branch 40 (.leaf 2406969103) (.leaf 2354432567))) (.branch 43 (.branch 42 (.leaf 2303151817) (.leaf 2253090378)) (.branch 44 (.leaf 2204213233) (.leaf 2156486734))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2109878536) (.branch 47 (.leaf 2064357521) (.leaf 2019893734))) (.branch 50 (.branch 49 (.leaf 1976458325) (.leaf 1934023489)) (.branch 51 (.leaf 1892562416) (.leaf 1852049238)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1812458986) (.leaf 1773767545)) (.branch 55 (.leaf 1735951614) (.leaf 1698988666))) (.branch 58 (.branch 57 (.leaf 1662856915) (.leaf 1627535280)) (.branch 59 (.leaf 1593003354) (.leaf 1559241376))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1526230200) (.branch 62 (.leaf 1493951272) (.leaf 1462386602))) (.branch 65 (.branch 64 (.leaf 1431518741) (.leaf 1401330761)) (.branch 66 (.leaf 1371806233) (.leaf 1342929207)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1314684191) (.leaf 1287056139)) (.branch 70 (.leaf 1260030428) (.leaf 1233592846))) (.branch 73 (.branch 72 (.leaf 1207729576) (.leaf 1182427178)) (.branch 74 (.leaf 1157672584) (.leaf 1133453075))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1109756275) (.branch 77 (.leaf 1086570138) (.leaf 1063882936))) (.branch 80 (.branch 79 (.leaf 1041683247) (.leaf 1019959948)) (.branch 81 (.leaf 998702203) (.leaf 977899454)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 957541413) (.leaf 937618052)) (.branch 85 (.leaf 918119596) (.leaf 899036515))) (.branch 88 (.branch 87 (.leaf 880359516) (.leaf 862079536)) (.branch 89 (.leaf 844187736) (.leaf 826675493)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 809534393) (.branch 92 (.leaf 792756228) (.leaf 776332988))) (.branch 95 (.branch 94 (.leaf 760256854) (.leaf 744520196)) (.branch 96 (.leaf 729115564) (.leaf 714035686)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 699273461) (.leaf 684821956)) (.branch 100 (.leaf 670674401) (.leaf 656824182))) (.branch 103 (.branch 102 (.leaf 643264841) (.leaf 629990069)) (.branch 104 (.leaf 616993704) (.leaf 604269725))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 591812249) (.leaf 579615528)) (.branch 108 (.leaf 567673948) (.leaf 555982019))) (.branch 111 (.branch 110 (.leaf 544534378) (.leaf 533325782)) (.branch 112 (.leaf 522351109) (.leaf 511605350)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 501083611) (.leaf 490781104)) (.branch 116 (.leaf 480693153) (.leaf 470815184))) (.branch 119 (.branch 118 (.leaf 461142723) (.leaf 451671400)) (.branch 120 (.leaf 442396939) (.leaf 433315159)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1193).prefactor = (5232884424234713/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1193).cutoff/(generalMeanRows 1193).c)).2 =
    (619071503760551/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1193).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1193).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1193).q*(generalMeanRows 1193).cutoff/2-2 = (29/9:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable403.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1193).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1193

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1193).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1193).criticalRate j.val*(generalMeanRows 1193).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1193).c*(generalMeanRows 1193).criticalPoint j.val)).2-
      (generalMeanRows 1193).J/2-(generalMeanRows 1193).error (generalMeanGrid j.val)+
      (generalMeanRows 1193).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1193).c)).2-
      (generalMeanRows 1193).J/2-(generalMeanRows 1193).error 4 := by
  have he : (generalMeanRows 1193).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1193) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1193)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1193

/-! Kernel-checked entropy margins for general spectral rectangle 1194. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1194
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6305326677) (.branch 2 (.leaf 6132386082) (.leaf 5966047105))) (.branch 5 (.branch 4 (.leaf 5805932383) (.leaf 5651693757)) (.branch 6 (.leaf 5503009530) (.leaf 5359582028)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5221135413) (.leaf 5087413740)) (.branch 10 (.leaf 4958179202) (.leaf 4833210566))) (.branch 13 (.branch 12 (.leaf 4712301751) (.leaf 4595260559)) (.branch 14 (.leaf 4481907523) (.leaf 4372074864))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4265605548) (.branch 17 (.leaf 4162352431) (.leaf 4062177480))) (.branch 20 (.branch 19 (.leaf 3964951071) (.leaf 3870551336)) (.branch 21 (.leaf 3778863585) (.leaf 3689779764)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3603197970) (.leaf 3519021998)) (.branch 25 (.leaf 3437160935) (.leaf 3357528784))) (.branch 28 (.branch 27 (.leaf 3280044116) (.leaf 3204629755)) (.branch 29 (.leaf 3131212489) (.leaf 3059722801)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2990094620) (.branch 32 (.leaf 2922265098) (.leaf 2856174398))) (.branch 35 (.branch 34 (.leaf 2791765503) (.leaf 2728984035)) (.branch 36 (.leaf 2667778093) (.leaf 2608098097)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2549896648) (.leaf 2493128401)) (.branch 40 (.leaf 2437749937) (.leaf 2383719656))) (.branch 43 (.branch 42 (.leaf 2330997669) (.leaf 2279545702)) (.branch 44 (.leaf 2229327009) (.leaf 2180306281))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2132449574) (.branch 47 (.leaf 2085724232) (.leaf 2040098824))) (.branch 50 (.branch 49 (.leaf 1995543073) (.leaf 1952027805)) (.branch 51 (.leaf 1909524888) (.leaf 1868007180)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1827448485) (.leaf 1787823504)) (.branch 55 (.leaf 1749107793) (.leaf 1711277724))) (.branch 58 (.branch 57 (.leaf 1674310445) (.leaf 1638183849)) (.branch 59 (.leaf 1602876536) (.leaf 1568367787))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1534637528) (.branch 62 (.leaf 1501666311) (.leaf 1469435279))) (.branch 65 (.branch 64 (.leaf 1437926147) (.leaf 1407121178)) (.branch 66 (.leaf 1377003159) (.leaf 1347555381)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1318761622) (.leaf 1290606124)) (.branch 70 (.leaf 1263073579) (.leaf 1236149108))) (.branch 73 (.branch 72 (.leaf 1209818251) (.leaf 1184066947)) (.branch 74 (.leaf 1158881520) (.leaf 1134248669))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1110155452) (.branch 77 (.leaf 1086589273) (.leaf 1063537872))) (.branch 80 (.branch 79 (.leaf 1040989313) (.leaf 1018931973)) (.branch 81 (.leaf 997354532) (.leaf 976245964)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 955595526) (.leaf 935392749)) (.branch 85 (.leaf 915627432) (.leaf 896289631))) (.branch 88 (.branch 87 (.leaf 877369651) (.leaf 858858041)) (.branch 89 (.leaf 840745583) (.leaf 823023289)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 805682392) (.branch 92 (.leaf 788714339) (.leaf 772110786))) (.branch 95 (.branch 94 (.leaf 755863592) (.leaf 739964813)) (.branch 96 (.leaf 724406695) (.leaf 709181671)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 694282356) (.leaf 679701538)) (.branch 100 (.leaf 665432179) (.leaf 651467404))) (.branch 103 (.branch 102 (.leaf 637800504) (.leaf 624424924)) (.branch 104 (.leaf 611334265) (.leaf 598522274))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 585982847) (.leaf 573710019)) (.branch 108 (.leaf 561697965) (.leaf 549940993))) (.branch 111 (.branch 110 (.leaf 538433541) (.leaf 527170178)) (.branch 112 (.leaf 516145594) (.leaf 505354601)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 494792130) (.leaf 484453226)) (.branch 116 (.leaf 474333049) (.leaf 464426865))) (.branch 119 (.branch 118 (.leaf 454730049) (.leaf 445238080)) (.branch 120 (.leaf 435946538) (.leaf 426851104)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1194).prefactor = (5448136287425327/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1194).cutoff/(generalMeanRows 1194).c)).2 =
    (307096722653561/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1194).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1194).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1194).q*(generalMeanRows 1194).c/2-2 = (1321/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable402.value]
    have hcontinuation : (generalMeanRows 1194).q*(generalMeanRows 1194).cutoff/2-2 = (29/9:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable403.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1194).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1194

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1194).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1194).criticalRate j.val*(generalMeanRows 1194).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1194).c*(generalMeanRows 1194).criticalPoint j.val)).2-
      (generalMeanRows 1194).J/2-(generalMeanRows 1194).error (generalMeanGrid j.val)+
      (generalMeanRows 1194).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1194).c)).2-
      (generalMeanRows 1194).J/2-(generalMeanRows 1194).error 4 := by
  have he : (generalMeanRows 1194).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1194) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1194)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1194

/-! Kernel-checked entropy margins for general spectral rectangle 1195. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1195
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6564692871) (.branch 2 (.leaf 6384638458) (.leaf 6211457217))) (.branch 5 (.branch 4 (.leaf 6044756263) (.leaf 5884173115)) (.branch 6 (.leaf 5729372843) (.leaf 5580045528)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5435903987) (.leaf 5296681745)) (.branch 10 (.leaf 5162131215) (.leaf 5032022062))) (.branch 13 (.branch 12 (.leaf 4906139728) (.leaf 4784284110)) (.branch 14 (.leaf 4666268359) (.leaf 4551917793))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4441068919) (.branch 17 (.leaf 4333568541) (.leaf 4229272948))) (.branch 20 (.branch 19 (.leaf 4128047183) (.leaf 4029764366)) (.branch 21 (.leaf 3934305089) (.leaf 3841556854)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3751413564) (.leaf 3663775059)) (.branch 25 (.leaf 3578546687) (.leaf 3495638910))) (.branch 28 (.branch 27 (.leaf 3414966952) (.leaf 3336450462)) (.branch 29 (.leaf 3260013217) (.leaf 3185582839)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3113090540) (.branch 32 (.leaf 3042470888) (.leaf 2973661583))) (.branch 35 (.branch 34 (.leaf 2906603263) (.leaf 2841239314)) (.branch 36 (.leaf 2777515698) (.leaf 2715380798)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2654785264) (.leaf 2595681886)) (.branch 40 (.leaf 2538025459) (.leaf 2481772671))) (.branch 43 (.branch 42 (.leaf 2426881994) (.leaf 2373313579)) (.branch 44 (.leaf 2321029167) (.leaf 2269991997))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2220166730) (.branch 47 (.leaf 2171519367) (.leaf 2124017183))) (.branch 50 (.branch 49 (.leaf 2077628656) (.leaf 2032323411)) (.branch 51 (.leaf 1988072158) (.leaf 1944846642)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1902619588) (.leaf 1861364655)) (.branch 55 (.leaf 1821056394) (.leaf 1781670205))) (.branch 58 (.branch 57 (.leaf 1743182297) (.leaf 1705569653)) (.branch 59 (.leaf 1668809993) (.leaf 1632881745))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1597764011) (.branch 62 (.leaf 1563436540) (.leaf 1529879702))) (.branch 65 (.branch 64 (.leaf 1497074459) (.leaf 1465002344)) (.branch 66 (.leaf 1433645437) (.leaf 1402986341)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1373008166) (.leaf 1343694507)) (.branch 70 (.leaf 1315029425) (.leaf 1286997431))) (.branch 73 (.branch 72 (.leaf 1259583469) (.leaf 1232772898)) (.branch 74 (.leaf 1206551483) (.leaf 1180905373))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1155821095) (.branch 77 (.leaf 1131285534) (.leaf 1107285926))) (.branch 80 (.branch 79 (.leaf 1083809844) (.leaf 1060845187)) (.branch 81 (.leaf 1038380170) (.leaf 1016403312)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 994903429) (.leaf 973869623)) (.branch 85 (.leaf 953291270) (.leaf 933158019))) (.branch 88 (.branch 87 (.leaf 913459776) (.leaf 894186700)) (.branch 89 (.leaf 875329197) (.leaf 856877906)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 838823700) (.branch 92 (.leaf 821157676) (.leaf 803871145))) (.branch 95 (.branch 94 (.leaf 786955631) (.leaf 770402864)) (.branch 96 (.leaf 754204771) (.leaf 738353475)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 722841284) (.leaf 707660692)) (.branch 100 (.leaf 692804371) (.leaf 678265163))) (.branch 103 (.branch 102 (.leaf 664036082) (.leaf 650110305)) (.branch 104 (.leaf 636481168) (.leaf 623142163))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 610086933) (.leaf 597309270)) (.branch 108 (.leaf 584803106) (.leaf 572562517))) (.branch 111 (.branch 110 (.leaf 560581713) (.leaf 548855037)) (.branch 112 (.leaf 537376963) (.leaf 526142088)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 515145136) (.leaf 504380947)) (.branch 116 (.leaf 493844482) (.leaf 483530812))) (.branch 119 (.branch 118 (.leaf 473435123) (.leaf 463552707)) (.branch 120 (.leaf 453878963) (.leaf 444409392)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1195).prefactor = (5672242419285131/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1195).cutoff/(generalMeanRows 1195).c)).2 =
    (307096722653561/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1195).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1195).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1195).q*(generalMeanRows 1195).c/2-2 = (1321/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable402.value]
    have hcontinuation : (generalMeanRows 1195).q*(generalMeanRows 1195).cutoff/2-2 = (29/9:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable403.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1195).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1195

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1195).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1195).criticalRate j.val*(generalMeanRows 1195).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1195).c*(generalMeanRows 1195).criticalPoint j.val)).2-
      (generalMeanRows 1195).J/2-(generalMeanRows 1195).error (generalMeanGrid j.val)+
      (generalMeanRows 1195).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1195).c)).2-
      (generalMeanRows 1195).J/2-(generalMeanRows 1195).error 4 := by
  have he : (generalMeanRows 1195).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1195) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1195)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1195

/-! Kernel-checked entropy margins for general spectral rectangle 1196. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1196
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6739789622) (.branch 2 (.leaf 6552631653) (.leaf 6372654457))) (.branch 5 (.branch 4 (.leaf 6199448071) (.leaf 6032634197)) (.branch 6 (.leaf 5871863229) (.leaf 5716811610)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5567179466) (.leaf 5422688499)) (.branch 10 (.leaf 5283080087) (.leaf 5148113585))) (.branch 13 (.branch 12 (.leaf 5017564793) (.leaf 4891224573)) (.branch 14 (.leaf 4768897605) (.leaf 4650401254))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4535564553) (.branch 17 (.leaf 4424227270) (.leaf 4316239071))) (.branch 20 (.branch 19 (.leaf 4211458749) (.leaf 4109753529)) (.branch 21 (.leaf 4010998430) (.leaf 3915075685)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3821874210) (.leaf 3731289119)) (.branch 25 (.leaf 3643221276) (.leaf 3557576891))) (.branch 28 (.branch 27 (.leaf 3474267147) (.leaf 3393207851)) (.branch 29 (.leaf 3314319124) (.leaf 3237525107)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3162753697) (.branch 32 (.leaf 3089936297) (.leaf 3019007589))) (.branch 35 (.branch 34 (.leaf 2949905330) (.leaf 2882570151)) (.branch 36 (.leaf 2816945380) (.leaf 2752976879)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2690612889) (.leaf 2629803886)) (.branch 40 (.leaf 2570502453) (.leaf 2512663153))) (.branch 43 (.branch 42 (.leaf 2456242419) (.leaf 2401198448)) (.branch 44 (.leaf 2347491102) (.leaf 2295081816))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2243933514) (.branch 47 (.leaf 2194010529) (.leaf 2145278530))) (.branch 50 (.branch 49 (.leaf 2097704451) (.leaf 2051256429)) (.branch 51 (.leaf 2005903742) (.leaf 1961616752)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1918366854) (.leaf 1876126425)) (.branch 55 (.leaf 1834868778) (.leaf 1794568119))) (.branch 58 (.branch 57 (.leaf 1755199505) (.leaf 1716738805)) (.branch 59 (.leaf 1679162668) (.leaf 1642448484))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1606574352) (.branch 62 (.leaf 1571519055) (.leaf 1537262025))) (.branch 65 (.branch 64 (.leaf 1503783322) (.leaf 1471063605)) (.branch 66 (.leaf 1439084106) (.leaf 1407826613)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1377273444) (.leaf 1347407430)) (.branch 70 (.leaf 1318211890) (.leaf 1289670619))) (.branch 73 (.branch 72 (.leaf 1261767868) (.leaf 1234488326)) (.branch 74 (.leaf 1207817106) (.leaf 1181739730))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1156242113) (.branch 77 (.leaf 1131310553) (.leaf 1106931713))) (.branch 80 (.branch 79 (.leaf 1083092613) (.leaf 1059780616)) (.branch 81 (.leaf 1036983418) (.leaf 1014689035)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 992885795) (.leaf 971562328)) (.branch 85 (.leaf 950707553) (.leaf 930310675))) (.branch 88 (.branch 87 (.leaf 910361171) (.leaf 890848784)) (.branch 89 (.leaf 871763515) (.leaf 853095613)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 834835573) (.branch 92 (.leaf 816974123) (.leaf 799502219))) (.branch 95 (.branch 94 (.leaf 782411040) (.leaf 765691982)) (.branch 96 (.leaf 749336648) (.leaf 733336845)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 717684579) (.leaf 702372049)) (.branch 100 (.leaf 687391639) (.leaf 672735916))) (.branch 103 (.branch 102 (.leaf 658397624) (.leaf 644369681)) (.branch 104 (.leaf 630645169) (.leaf 617217338))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 604079592) (.leaf 591225494)) (.branch 108 (.leaf 578648754) (.leaf 566343232))) (.branch 111 (.branch 110 (.leaf 554302930) (.leaf 542521988)) (.branch 112 (.leaf 530994683) (.leaf 519715424)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 508678749) (.leaf 497879321)) (.branch 116 (.leaf 487311928) (.leaf 476971475))) (.branch 119 (.branch 118 (.leaf 466852984) (.leaf 456951590)) (.branch 120 (.leaf 447262542) (.leaf 437781194)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1196).prefactor = (5905567035354501/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1196).cutoff/(generalMeanRows 1196).c)).2 =
    (609339066842321/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1196).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1196).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1196).q*(generalMeanRows 1196).cutoff/2-2 = (29/9:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable403.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1196).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1196

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1196).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1196).criticalRate j.val*(generalMeanRows 1196).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1196).c*(generalMeanRows 1196).criticalPoint j.val)).2-
      (generalMeanRows 1196).J/2-(generalMeanRows 1196).error (generalMeanGrid j.val)+
      (generalMeanRows 1196).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1196).c)).2-
      (generalMeanRows 1196).J/2-(generalMeanRows 1196).error 4 := by
  have he : (generalMeanRows 1196).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1196) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1196)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1196

/-! Kernel-checked entropy margins for general spectral rectangle 1197. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1197
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6364872052) (.branch 2 (.leaf 6172927437) (.leaf 5988624609))) (.branch 5 (.branch 4 (.leaf 5811529687) (.leaf 5641241849)) (.branch 6 (.leaf 5477390250) (.leaf 5319631276)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5167646098) (.leaf 5021138478)) (.branch 10 (.leaf 4879832799) (.leaf 4743472304))) (.branch 13 (.branch 12 (.leaf 4611817499) (.leaf 4484644720)) (.branch 14 (.leaf 4361744839) (.leaf 4242922085))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4127992986) (.branch 17 (.leaf 4016785398) (.leaf 3909137635))) (.branch 20 (.branch 19 (.leaf 3804897661) (.leaf 3703922371)) (.branch 21 (.leaf 3606076923) (.leaf 3511234133)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3419273917) (.leaf 3330082790)) (.branch 25 (.leaf 3243553394) (.leaf 3159584076))) (.branch 28 (.branch 27 (.leaf 3078078496) (.leaf 2998945263)) (.branch 29 (.leaf 2922097608) (.leaf 2847453078)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2774933253) (.branch 32 (.leaf 2704463489) (.leaf 2635972678))) (.branch 35 (.branch 34 (.leaf 2569393027) (.leaf 2504659851)) (.branch 36 (.leaf 2441711390) (.leaf 2380488625)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2320935124) (.leaf 2262996884)) (.branch 40 (.leaf 2206622198) (.leaf 2151761519))) (.branch 43 (.branch 42 (.leaf 2098367340) (.leaf 2046394086)) (.branch 44 (.leaf 1995798005) (.leaf 1946537068))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1898570885) (.branch 47 (.leaf 1851860615) (.leaf 1806368885))) (.branch 50 (.branch 49 (.leaf 1762059720) (.leaf 1718898472)) (.branch 51 (.leaf 1676851753) (.leaf 1635887374)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1595974293) (.leaf 1557082552)) (.branch 55 (.leaf 1519183237) (.leaf 1482248420))) (.branch 58 (.branch 57 (.leaf 1446251124) (.leaf 1411165274)) (.branch 59 (.leaf 1376965662) (.leaf 1343627905))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1311128415) (.branch 62 (.leaf 1279444361) (.leaf 1248553642))) (.branch 65 (.branch 64 (.leaf 1218434852) (.leaf 1189067259)) (.branch 66 (.leaf 1160430770) (.leaf 1132505913)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1105273808) (.leaf 1078716147)) (.branch 70 (.leaf 1052815172) (.leaf 1027553654))) (.branch 73 (.branch 72 (.leaf 1002914874) (.leaf 978882603)) (.branch 74 (.leaf 955441086) (.leaf 932575024))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 910269561) (.branch 77 (.leaf 888510262) (.leaf 867283105))) (.branch 80 (.branch 79 (.leaf 846574465) (.leaf 826371098)) (.branch 81 (.leaf 806660132) (.leaf 787429052)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 768665690) (.leaf 750358212)) (.branch 85 (.leaf 732495110) (.leaf 715065188))) (.branch 88 (.branch 87 (.leaf 698057556) (.leaf 681461617)) (.branch 89 (.leaf 665267060) (.leaf 649463850)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 634042221) (.branch 92 (.leaf 618992667) (.leaf 604305931))) (.branch 95 (.branch 94 (.leaf 589973006) (.leaf 575985118)) (.branch 96 (.leaf 562333724) (.leaf 549010506)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 536007362) (.leaf 523316402)) (.branch 100 (.leaf 510929938) (.leaf 498840482))) (.branch 103 (.branch 102 (.leaf 487040742) (.leaf 475523608)) (.branch 104 (.leaf 464282159) (.leaf 453309645))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 442599492) (.leaf 432145293)) (.branch 108 (.leaf 421940804) (.leaf 411979938))) (.branch 111 (.branch 110 (.leaf 402256764) (.leaf 392765500)) (.branch 112 (.leaf 383500510) (.leaf 374456299)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 365627512) (.leaf 357008926)) (.branch 116 (.leaf 348595451) (.leaf 340382123))) (.branch 119 (.branch 118 (.leaf 332364102) (.leaf 324536669)) (.branch 120 (.leaf 316895221) (.leaf 309435272)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1197).prefactor = (6148489332982543/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1197).cutoff/(generalMeanRows 1197).c)).2 =
    (57600264657473/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1197).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1197).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1197).q*(generalMeanRows 1197).cutoff/2-2 = (29/9:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable403.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1197).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1197

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1197).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1197).criticalRate j.val*(generalMeanRows 1197).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1197).c*(generalMeanRows 1197).criticalPoint j.val)).2-
      (generalMeanRows 1197).J/2-(generalMeanRows 1197).error (generalMeanGrid j.val)+
      (generalMeanRows 1197).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1197).c)).2-
      (generalMeanRows 1197).J/2-(generalMeanRows 1197).error 4 := by
  have he : (generalMeanRows 1197).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1197) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1197)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1197

/-! Kernel-checked entropy margins for general spectral rectangle 1198. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1198
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6909041097) (.branch 2 (.leaf 6707752868) (.leaf 6514350443))) (.branch 5 (.branch 4 (.leaf 6328385320) (.leaf 6149443366)) (.branch 6 (.leaf 5977141601) (.leaf 5811125339)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5651065634) (.leaf 5496656995)) (.branch 10 (.leaf 5347615333) (.leaf 5203676124))) (.branch 13 (.branch 12 (.leaf 5064592747) (.leaf 4930134993)) (.branch 14 (.leaf 4800087711) (.leaf 4674249586))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4552432034) (.branch 17 (.leaf 4434458197) (.leaf 4320162027))) (.branch 20 (.branch 19 (.leaf 4209387457) (.leaf 4101987646)) (.branch 21 (.leaf 3997824286) (.leaf 3896766972)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3798692627) (.leaf 3703484973)) (.branch 25 (.leaf 3611034048) (.leaf 3521235767))) (.branch 28 (.branch 27 (.leaf 3433991509) (.leaf 3349207747)) (.branch 29 (.leaf 3266795706) (.leaf 3186671041)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3108753555) (.branch 32 (.leaf 3032966919) (.leaf 2959238435))) (.branch 35 (.branch 34 (.leaf 2887498800) (.leaf 2817681896)) (.branch 36 (.leaf 2749724599) (.leaf 2683566589)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2619150190) (.leaf 2556420211)) (.branch 40 (.leaf 2495323802) (.leaf 2435810320))) (.branch 43 (.branch 42 (.leaf 2377831203) (.leaf 2321339858)) (.branch 44 (.leaf 2266291548) (.leaf 2212643294))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2160353783) (.branch 47 (.leaf 2109383278) (.leaf 2059693535))) (.branch 50 (.branch 49 (.leaf 2011247732) (.leaf 1964010393)) (.branch 51 (.leaf 1917947322) (.leaf 1873025543)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1829213239) (.leaf 1786479696)) (.branch 55 (.leaf 1744795256) (.leaf 1704131264))) (.branch 58 (.branch 57 (.leaf 1664460025) (.leaf 1625754760)) (.branch 59 (.leaf 1587989566) (.leaf 1551139378))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1515179934) (.branch 62 (.leaf 1480087739) (.leaf 1445840036))) (.branch 65 (.branch 64 (.leaf 1412414773) (.leaf 1379790577)) (.branch 66 (.leaf 1347946724) (.leaf 1316863116)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1286520258) (.leaf 1256899231)) (.branch 70 (.leaf 1227981671) (.leaf 1199749751))) (.branch 73 (.branch 72 (.leaf 1172186161) (.leaf 1145274085)) (.branch 74 (.leaf 1118997189) (.leaf 1093339598))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1068285886) (.branch 77 (.leaf 1043821056) (.leaf 1019930527))) (.branch 80 (.branch 79 (.leaf 996600120) (.leaf 973816044)) (.branch 81 (.leaf 951564883) (.leaf 929833585)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 908609448) (.leaf 887880113)) (.branch 85 (.leaf 867633546) (.leaf 847858034))) (.branch 88 (.branch 87 (.leaf 828542174) (.leaf 809674862)) (.branch 89 (.leaf 791245281) (.leaf 773242900)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 755657457) (.branch 92 (.leaf 738478958) (.leaf 721697663))) (.branch 95 (.branch 94 (.leaf 705304084) (.leaf 689288973)) (.branch 96 (.leaf 673643317) (.leaf 658358333)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 643425459) (.leaf 628836348)) (.branch 100 (.leaf 614582863) (.leaf 600657069))) (.branch 103 (.branch 102 (.leaf 587051231) (.leaf 573757805)) (.branch 104 (.leaf 560769435) (.leaf 548078945))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 535679339) (.leaf 523563790)) (.branch 108 (.leaf 511725642) (.leaf 500158399))) (.branch 111 (.branch 110 (.leaf 488855725) (.leaf 477811439)) (.branch 112 (.leaf 467019509) (.leaf 456474050)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 446169322) (.leaf 436099720)) (.branch 116 (.leaf 426259776) (.leaf 416644154))) (.branch 119 (.branch 118 (.leaf 407247648) (.leaf 398065172)) (.branch 120 (.leaf 389091768) (.leaf 380322593)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1198).prefactor = (6401404107595709/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1198).cutoff/(generalMeanRows 1198).c)).2 =
    (23606153044839/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1198).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1198).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1198).q*(generalMeanRows 1198).c/2-2 = (1431/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable399.value]
    have hcontinuation : (generalMeanRows 1198).q*(generalMeanRows 1198).cutoff/2-2 = (29/9:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable403.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1198).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1198

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1198).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1198).criticalRate j.val*(generalMeanRows 1198).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1198).c*(generalMeanRows 1198).criticalPoint j.val)).2-
      (generalMeanRows 1198).J/2-(generalMeanRows 1198).error (generalMeanGrid j.val)+
      (generalMeanRows 1198).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1198).c)).2-
      (generalMeanRows 1198).J/2-(generalMeanRows 1198).error 4 := by
  have he : (generalMeanRows 1198).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1198) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1198)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1198

/-! Kernel-checked entropy margins for general spectral rectangle 1199. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1199
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7589950883) (.branch 2 (.leaf 7381776002) (.leaf 7181547731))) (.branch 5 (.branch 4 (.leaf 6988811820) (.leaf 6803149180)) (.branch 6 (.leaf 6624172573) (.leaf 6451523676)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6284870454) (.leaf 6123904815)) (.branch 10 (.leaf 5968340506) (.leaf 5817911216))) (.branch 13 (.branch 12 (.leaf 5672368881) (.leaf 5531482145)) (.branch 14 (.leaf 5395034976) (.leaf 5262825413))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5134664427) (.branch 17 (.leaf 5010374897) (.leaf 4889790669))) (.branch 20 (.branch 19 (.leaf 4772755706) (.leaf 4659123314)) (.branch 21 (.leaf 4548755436) (.leaf 4441522003)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4337300351) (.leaf 4235974674)) (.branch 25 (.leaf 4137435538) (.leaf 4041579424))) (.branch 28 (.branch 27 (.leaf 3948308312) (.leaf 3857529305)) (.branch 29 (.leaf 3769154274) (.leaf 3683099538)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3599285566) (.branch 32 (.leaf 3517636705) (.leaf 3438080928))) (.branch 35 (.branch 34 (.leaf 3360549600) (.leaf 3284977266)) (.branch 36 (.leaf 3211301448) (.leaf 3139462468)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3069403269) (.leaf 3001069266)) (.branch 40 (.leaf 2934408197) (.leaf 2869369984))) (.branch 43 (.branch 42 (.leaf 2805906611) (.leaf 2743972010)) (.branch 44 (.leaf 2683521943) (.leaf 2624513911))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2566907053) (.branch 47 (.leaf 2510662062) (.leaf 2455741100))) (.branch 50 (.branch 49 (.leaf 2402107723) (.leaf 2349726814)) (.branch 51 (.leaf 2298564507) (.leaf 2248588133)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2199766158) (.leaf 2152068129)) (.branch 55 (.leaf 2105464620) (.leaf 2059927191))) (.branch 58 (.branch 57 (.leaf 2015428334) (.leaf 1971941437)) (.branch 59 (.leaf 1929440741) (.leaf 1887901305))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1847298968) (.branch 62 (.leaf 1807610315) (.leaf 1768812650))) (.branch 65 (.branch 64 (.leaf 1730883963) (.leaf 1693802902)) (.branch 66 (.leaf 1657548748) (.leaf 1622101388)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1587441294) (.leaf 1553549498)) (.branch 70 (.leaf 1520407572) (.leaf 1487997608))) (.branch 73 (.branch 72 (.leaf 1456302198) (.leaf 1425304417)) (.branch 74 (.leaf 1394987804) (.leaf 1365336347))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1336334465) (.branch 77 (.leaf 1307966999) (.leaf 1280219190))) (.branch 80 (.branch 79 (.leaf 1253076669) (.leaf 1226525447)) (.branch 81 (.leaf 1200551898) (.leaf 1175142747)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1150285064) (.leaf 1125966248)) (.branch 85 (.leaf 1102174018) (.leaf 1078896404))) (.branch 88 (.branch 87 (.leaf 1056121736) (.leaf 1033838638)) (.branch 89 (.leaf 1012036014) (.leaf 990703045)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 969829177) (.branch 92 (.leaf 949404115) (.leaf 929417815))) (.branch 95 (.branch 94 (.leaf 909860477) (.leaf 890722538)) (.branch 96 (.leaf 871994666) (.leaf 853667752)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 835732905) (.leaf 818181444)) (.branch 100 (.leaf 801004898) (.leaf 784194992))) (.branch 103 (.branch 102 (.leaf 767743647) (.leaf 751642976)) (.branch 104 (.leaf 735885273) (.leaf 720463014))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 705368850) (.leaf 690595601)) (.branch 108 (.leaf 676136255) (.leaf 661983960))) (.branch 111 (.branch 110 (.leaf 648132023) (.leaf 634573903)) (.branch 112 (.leaf 621303210) (.leaf 608313699)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 595599269) (.leaf 583153956)) (.branch 116 (.leaf 570971930) (.leaf 559047497))) (.branch 119 (.branch 118 (.leaf 547375087) (.leaf 535949259)) (.branch 120 (.leaf 524764692) (.leaf 513816187)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1199).prefactor = (1311623931307417/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1199).cutoff/(generalMeanRows 1199).c)).2 =
    (307096722653561/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1199).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1199).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1199).q*(generalMeanRows 1199).c/2-2 = (1321/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable402.value]
    have hcontinuation : (generalMeanRows 1199).q*(generalMeanRows 1199).cutoff/2-2 = (29/9:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable403.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1199).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1199

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1199).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1199).criticalRate j.val*(generalMeanRows 1199).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1199).c*(generalMeanRows 1199).criticalPoint j.val)).2-
      (generalMeanRows 1199).J/2-(generalMeanRows 1199).error (generalMeanGrid j.val)+
      (generalMeanRows 1199).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1199).c)).2-
      (generalMeanRows 1199).J/2-(generalMeanRows 1199).error 4 := by
  have he : (generalMeanRows 1199).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1199) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1199)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1199

/-! Kernel-checked entropy margins for general spectral rectangle 1200. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1200
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6069238942) (.branch 2 (.leaf 5893407627) (.leaf 5724373576))) (.branch 5 (.branch 4 (.leaf 5561750338) (.leaf 5405181596)) (.branch 6 (.leaf 5254338297) (.leaf 5108916092)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4968633059) (.leaf 4833227668)) (.branch 10 (.leaf 4702456955) (.leaf 4576094893))) (.branch 13 (.branch 12 (.leaf 4453930919) (.leaf 4335768615)) (.branch 14 (.leaf 4221424520) (.leaf 4110727046))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4003515515) (.branch 17 (.leaf 3899639275) (.leaf 3798956903))) (.branch 20 (.branch 19 (.leaf 3701335478) (.leaf 3606649928)) (.branch 21 (.leaf 3514782426) (.leaf 3425621850)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3339063280) (.leaf 3255007547)) (.branch 25 (.leaf 3173360819) (.leaf 3094034219))) (.branch 28 (.branch 27 (.leaf 3016943476) (.leaf 2942008614)) (.branch 29 (.leaf 2869153648) (.leaf 2798306327)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2729397879) (.branch 32 (.leaf 2662362788) (.leaf 2597138585))) (.branch 35 (.branch 34 (.leaf 2533665653) (.leaf 2471887050)) (.branch 36 (.leaf 2411748346) (.leaf 2353197471)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2296184574) (.leaf 2240661892)) (.branch 40 (.leaf 2186583632) (.leaf 2133905859))) (.branch 43 (.branch 42 (.leaf 2082586389) (.leaf 2032584698)) (.branch 44 (.leaf 1983861827) (.leaf 1936380304))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1890104061) (.branch 47 (.leaf 1844998366) (.leaf 1801029753))) (.branch 50 (.branch 49 (.leaf 1758165959) (.leaf 1716375867)) (.branch 51 (.leaf 1675629448) (.leaf 1635897711)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1597152655) (.leaf 1559367221)) (.branch 55 (.leaf 1522515253) (.leaf 1486571454))) (.branch 58 (.branch 57 (.leaf 1451511353) (.leaf 1417311263)) (.branch 59 (.leaf 1383948255) (.leaf 1351400120))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1319645343) (.branch 62 (.leaf 1288663073) (.leaf 1258433099))) (.branch 65 (.branch 64 (.leaf 1228935820) (.leaf 1200152227)) (.branch 66 (.leaf 1172063876) (.leaf 1144652868)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1117901831) (.leaf 1091793895)) (.branch 70 (.leaf 1066312679) (.leaf 1041442272))) (.branch 73 (.branch 72 (.leaf 1017167216) (.leaf 993472488)) (.branch 74 (.leaf 970343489) (.leaf 947766028))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 925726305) (.branch 77 (.leaf 904210904) (.leaf 883206773))) (.branch 80 (.branch 79 (.leaf 862701221) (.leaf 842681897)) (.branch 81 (.leaf 823136785) (.leaf 804054192)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 785422737) (.leaf 767231343)) (.branch 85 (.leaf 749469225) (.leaf 732125884))) (.branch 88 (.branch 87 (.leaf 715191095) (.leaf 698654902)) (.branch 89 (.leaf 682507609) (.leaf 666739769)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 651342182) (.branch 92 (.leaf 636305885) (.leaf 621622145))) (.branch 95 (.branch 94 (.leaf 607282452) (.leaf 593278514)) (.branch 96 (.leaf 579602250) (.leaf 566245784)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 553201441) (.leaf 540461736)) (.branch 100 (.leaf 528019376) (.leaf 515867250))) (.branch 103 (.branch 102 (.leaf 503998425) (.leaf 492406140)) (.branch 104 (.leaf 481083806) (.leaf 470024993))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 459223436) (.leaf 448673021)) (.branch 108 (.leaf 438367786) (.leaf 428301918))) (.branch 111 (.branch 110 (.leaf 418469746) (.leaf 408865738)) (.branch 112 (.leaf 399484497) (.leaf 390320759)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 381369390) (.leaf 372625380)) (.branch 116 (.leaf 364083841) (.leaf 355740003))) (.branch 119 (.branch 118 (.leaf 347589214) (.leaf 339626933)) (.branch 120 (.leaf 331848730) (.leaf 324250283)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1200).prefactor = (5689096007580301/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1200).cutoff/(generalMeanRows 1200).c)).2 =
    (496618313427/781250000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1200).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1200).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1200).q*(generalMeanRows 1200).cutoff/2-2 = (269/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable404.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1200).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1200

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1200).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1200).criticalRate j.val*(generalMeanRows 1200).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1200).c*(generalMeanRows 1200).criticalPoint j.val)).2-
      (generalMeanRows 1200).J/2-(generalMeanRows 1200).error (generalMeanGrid j.val)+
      (generalMeanRows 1200).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1200).c)).2-
      (generalMeanRows 1200).J/2-(generalMeanRows 1200).error 4 := by
  have he : (generalMeanRows 1200).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1200) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1200)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1200

/-! Kernel-checked entropy margins for general spectral rectangle 1201. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1201
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6201936043) (.branch 2 (.leaf 6020191027) (.leaf 5845510948))) (.branch 5 (.branch 4 (.leaf 5677494377) (.leaf 5515771126)) (.branch 6 (.leaf 5359999269) (.leaf 5209862501)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5065067769) (.leaf 4925343170)) (.branch 10 (.leaf 4790436061) (.leaf 4660111369))) (.branch 13 (.branch 12 (.leaf 4534150065) (.leaf 4412347802)) (.branch 14 (.leaf 4294513675) (.leaf 4180469110))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4070046858) (.branch 17 (.leaf 3963090080) (.leaf 3859451523))) (.branch 20 (.branch 19 (.leaf 3758992768) (.leaf 3661583547)) (.branch 21 (.leaf 3567101125) (.leaf 3475429733)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3386460051) (.leaf 3300088741)) (.branch 25 (.leaf 3216218011) (.leaf 3134755227))) (.branch 28 (.branch 27 (.leaf 3055612547) (.leaf 2978706597)) (.branch 29 (.leaf 2903958160) (.leaf 2831291905)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2760636124) (.branch 32 (.leaf 2691922501) (.leaf 2625085894))) (.branch 35 (.branch 34 (.leaf 2560064132) (.leaf 2496797837)) (.branch 36 (.leaf 2435230243) (.leaf 2375307050)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2316976270) (.leaf 2260188094)) (.branch 40 (.leaf 2204894768) (.leaf 2151050476))) (.branch 43 (.branch 42 (.leaf 2098611234) (.leaf 2047534786)) (.branch 44 (.leaf 1997780513) (.leaf 1949309348))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1902083692) (.branch 47 (.leaf 1856067340) (.leaf 1811225411))) (.branch 50 (.branch 49 (.leaf 1767524282) (.leaf 1724931525)) (.branch 51 (.leaf 1683415853) (.leaf 1642947061)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1603495982) (.leaf 1565034432)) (.branch 55 (.leaf 1527535173) (.leaf 1490971865))) (.branch 58 (.branch 57 (.leaf 1455319031) (.leaf 1420552016)) (.branch 59 (.leaf 1386646957) (.leaf 1353580743))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1321330992) (.branch 62 (.leaf 1289876016) (.leaf 1259194794))) (.branch 65 (.branch 64 (.leaf 1229266948) (.leaf 1200072715)) (.branch 66 (.leaf 1171592926) (.leaf 1143808982)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1116702833) (.leaf 1090256958)) (.branch 70 (.leaf 1064454346) (.leaf 1039278477))) (.branch 73 (.branch 72 (.leaf 1014713305) (.leaf 990743241)) (.branch 74 (.leaf 967353138) (.leaf 944528276))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 922254344) (.branch 77 (.leaf 900517432) (.leaf 879304014))) (.branch 80 (.branch 79 (.leaf 858600936) (.leaf 838395404)) (.branch 81 (.leaf 818674972) (.leaf 799427532)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 780641304) (.leaf 762304822)) (.branch 85 (.leaf 744406929) (.leaf 726936762))) (.branch 88 (.branch 87 (.leaf 709883750) (.leaf 693237600)) (.branch 89 (.leaf 676988288) (.leaf 661126056)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 645641399) (.branch 92 (.leaf 630525061) (.leaf 615768025))) (.branch 95 (.branch 94 (.leaf 601361509) (.leaf 587296956)) (.branch 96 (.leaf 573566030) (.leaf 560160609)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 547072780) (.leaf 534294829)) (.branch 100 (.leaf 521819240) (.leaf 509638690))) (.branch 103 (.branch 102 (.leaf 497746037) (.leaf 486134324)) (.branch 104 (.leaf 474796765) (.leaf 463726750))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 452917830) (.leaf 442363720)) (.branch 108 (.leaf 432058292) (.leaf 421995570))) (.branch 111 (.branch 110 (.leaf 412169729) (.leaf 402575087)) (.branch 112 (.leaf 393206103) (.leaf 384057374)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 375123631) (.leaf 366399734)) (.branch 116 (.leaf 357880671) (.leaf 349561551))) (.branch 119 (.branch 118 (.leaf 341437608) (.leaf 333504188)) (.branch 120 (.leaf 325756753) (.leaf 318190877)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1201).prefactor = (5894401921836893/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1201).cutoff/(generalMeanRows 1201).c)).2 =
    (631041803287817/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1201).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1201).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1201).q*(generalMeanRows 1201).cutoff/2-2 = (269/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable404.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1201).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1201

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1201).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1201).criticalRate j.val*(generalMeanRows 1201).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1201).c*(generalMeanRows 1201).criticalPoint j.val)).2-
      (generalMeanRows 1201).J/2-(generalMeanRows 1201).error (generalMeanGrid j.val)+
      (generalMeanRows 1201).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1201).c)).2-
      (generalMeanRows 1201).J/2-(generalMeanRows 1201).error 4 := by
  have he : (generalMeanRows 1201).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1201) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1201)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1201

/-! Kernel-checked entropy margins for general spectral rectangle 1202. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1202
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6698050177) (.branch 2 (.leaf 6508472138) (.leaf 6326142729))) (.branch 5 (.branch 4 (.leaf 6150649204) (.leaf 5981611136)) (.branch 6 (.leaf 5818677332) (.leaf 5661523081)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5509847710) (.leaf 5363372393)) (.branch 10 (.leaf 5221838193) (.leaf 5085004311))) (.branch 13 (.branch 12 (.leaf 4952646502) (.leaf 4824555662)) (.branch 14 (.leaf 4700536545) (.leaf 4580406612))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4463994983) (.branch 17 (.leaf 4351141495) (.leaf 4241695848))) (.branch 20 (.branch 19 (.leaf 4135516823) (.leaf 4032471578)) (.branch 21 (.leaf 3932435007) (.leaf 3835289154)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3740922680) (.leaf 3649230374)) (.branch 25 (.leaf 3560112712) (.leaf 3473475448))) (.branch 28 (.branch 27 (.leaf 3389229241) (.leaf 3307289315)) (.branch 29 (.leaf 3227575147) (.leaf 3150010178)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3074521547) (.branch 32 (.leaf 3001039854) (.leaf 2929498932))) (.branch 35 (.branch 34 (.leaf 2859835640) (.leaf 2791989678)) (.branch 36 (.leaf 2725903406) (.leaf 2661521686)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2598791732) (.leaf 2537662967)) (.branch 40 (.leaf 2478086902) (.leaf 2420017008))) (.branch 43 (.branch 42 (.leaf 2363408615) (.leaf 2308218803)) (.branch 44 (.leaf 2254406306) (.leaf 2201931430))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2150755962) (.branch 47 (.leaf 2100843102) (.leaf 2052157381))) (.branch 50 (.branch 49 (.leaf 2004664604) (.leaf 1958331779)) (.branch 51 (.leaf 1913127066) (.leaf 1869019715)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1825980020) (.leaf 1783979269)) (.branch 55 (.leaf 1742989698) (.leaf 1702984449))) (.branch 58 (.branch 57 (.leaf 1663937532) (.leaf 1625823784)) (.branch 59 (.leaf 1588618837) (.leaf 1552299082))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1516841640) (.branch 62 (.leaf 1482224330) (.leaf 1448425642))) (.branch 65 (.branch 64 (.leaf 1415424713) (.leaf 1383201297)) (.branch 66 (.leaf 1351735743) (.leaf 1321008976)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1291002470) (.leaf 1261698233)) (.branch 70 (.leaf 1233078782) (.leaf 1205127131))) (.branch 73 (.branch 72 (.leaf 1177826768) (.leaf 1151161642)) (.branch 74 (.leaf 1125116145) (.leaf 1099675097))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1074823736) (.branch 77 (.leaf 1050547695) (.leaf 1026832997))) (.branch 80 (.branch 79 (.leaf 1003666041) (.leaf 981033587)) (.branch 81 (.leaf 958922745) (.leaf 937320966)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 916216032) (.leaf 895596040)) (.branch 85 (.leaf 875449401) (.leaf 855764822))) (.branch 88 (.branch 87 (.leaf 836531303) (.leaf 817738126)) (.branch 89 (.leaf 799374847) (.leaf 781431286)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 763897523) (.branch 92 (.leaf 746763888) (.leaf 730020954))) (.branch 95 (.branch 94 (.leaf 713659531) (.leaf 697670658)) (.branch 96 (.leaf 682045599) (.leaf 666775833)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 651853051) (.leaf 637269148)) (.branch 100 (.leaf 623016221) (.leaf 609086559))) (.branch 103 (.branch 102 (.leaf 595472640) (.leaf 582167127)) (.branch 104 (.leaf 569162862) (.leaf 556452858))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 544030301) (.leaf 531888541)) (.branch 108 (.leaf 520021086) (.leaf 508421605))) (.branch 111 (.branch 110 (.leaf 497083915) (.leaf 486001984)) (.branch 112 (.leaf 475169924) (.leaf 464581986)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 454232561) (.leaf 444116172)) (.branch 116 (.leaf 434227473) (.leaf 424561243))) (.branch 119 (.branch 118 (.leaf 415112388) (.leaf 405875931)) (.branch 120 (.leaf 396847016) (.leaf 388020899)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1202).prefactor = (6107116837167217/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1202).cutoff/(generalMeanRows 1202).c)).2 =
    (322497759030841/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1202).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1202).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1202).q*(generalMeanRows 1202).c/2-2 = (3529/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable373.value]
    have hcontinuation : (generalMeanRows 1202).q*(generalMeanRows 1202).cutoff/2-2 = (269/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable404.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1202).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1202

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1202).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1202).criticalRate j.val*(generalMeanRows 1202).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1202).c*(generalMeanRows 1202).criticalPoint j.val)).2-
      (generalMeanRows 1202).J/2-(generalMeanRows 1202).error (generalMeanGrid j.val)+
      (generalMeanRows 1202).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1202).c)).2-
      (generalMeanRows 1202).J/2-(generalMeanRows 1202).error 4 := by
  have he : (generalMeanRows 1202).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1202) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1202)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1202

/-! Kernel-checked entropy margins for general spectral rectangle 1203. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1203
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7234566408) (.branch 2 (.leaf 7037047793) (.leaf 6846960344))) (.branch 5 (.branch 4 (.leaf 6663879585) (.leaf 6487414492)) (.branch 6 (.leaf 6317204289) (.leaf 6152915591)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5994239868) (.leaf 5840891171)) (.branch 10 (.leaf 5692604102) (.leaf 5549131990))) (.branch 13 (.branch 12 (.leaf 5410245261) (.leaf 5275729958)) (.branch 14 (.leaf 5145386424) (.leaf 5019028094))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4896480423) (.branch 17 (.leaf 4777579902) (.leaf 4662173171))) (.branch 20 (.branch 19 (.leaf 4550116215) (.leaf 4441273634)) (.branch 21 (.leaf 4335517973) (.leaf 4232729123)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4132793766) (.leaf 4035604869)) (.branch 25 (.leaf 3941061228) (.leaf 3849067047))) (.branch 28 (.branch 27 (.leaf 3759531550) (.leaf 3672368633)) (.branch 29 (.leaf 3587496538) (.leaf 3504837555)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3424317755) (.branch 32 (.leaf 3345866733) (.leaf 3269417384))) (.branch 35 (.branch 34 (.leaf 3194905685) (.leaf 3122270503)) (.branch 36 (.leaf 3051453414) (.leaf 2982398534)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2915052370) (.leaf 2849363672)) (.branch 40 (.leaf 2785283304) (.leaf 2722764122))) (.branch 43 (.branch 42 (.leaf 2661760862) (.leaf 2602230030)) (.branch 44 (.leaf 2544129809) (.leaf 2487419968))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2432061774) (.branch 47 (.leaf 2378017918) (.leaf 2325252438))) (.branch 50 (.branch 49 (.leaf 2273730653) (.leaf 2223419098)) (.branch 51 (.leaf 2174285464) (.leaf 2126298543)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2079428176) (.leaf 2033645204)) (.branch 55 (.leaf 1988921421) (.leaf 1945229532))) (.branch 58 (.branch 57 (.leaf 1902543113) (.leaf 1860836572)) (.branch 59 (.leaf 1820085113) (.leaf 1780264704))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1741352042) (.branch 62 (.leaf 1703324527) (.leaf 1666160233))) (.branch 65 (.branch 64 (.leaf 1629837877) (.leaf 1594336799)) (.branch 66 (.leaf 1559636935) (.leaf 1525718797)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1492563448) (.leaf 1460152485)) (.branch 70 (.leaf 1428468016) (.leaf 1397492646))) (.branch 73 (.branch 72 (.leaf 1367209455) (.leaf 1337601986)) (.branch 74 (.leaf 1308654225) (.leaf 1280350588))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1252675905) (.branch 77 (.leaf 1225615411) (.leaf 1199154724))) (.branch 80 (.branch 79 (.leaf 1173279843) (.leaf 1147977126)) (.branch 81 (.leaf 1123233286) (.leaf 1099035376)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1075370779) (.leaf 1052227201)) (.branch 85 (.leaf 1029592655) (.leaf 1007455458))) (.branch 88 (.branch 87 (.leaf 985804219) (.leaf 964627828)) (.branch 89 (.leaf 943915454) (.leaf 923656531)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 903840755) (.branch 92 (.leaf 884458072) (.leaf 865498674))) (.branch 95 (.branch 94 (.leaf 846952992) (.leaf 828811688)) (.branch 96 (.leaf 811065650) (.leaf 793705984)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 776724009) (.leaf 760111254)) (.branch 100 (.leaf 743859446) (.leaf 727960511))) (.branch 103 (.branch 102 (.leaf 712406565) (.leaf 697189911)) (.branch 104 (.leaf 682303032) (.leaf 667738589))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 653489414) (.leaf 639548506)) (.branch 108 (.leaf 625909028) (.leaf 612564301))) (.branch 111 (.branch 110 (.leaf 599507803) (.leaf 586733161)) (.branch 112 (.leaf 574234151) (.leaf 562004689)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 550038835) (.leaf 538330784)) (.branch 116 (.leaf 526874862) (.leaf 515665529))) (.branch 119 (.branch 118 (.leaf 504697367) (.leaf 493965084)) (.branch 120 (.leaf 483463509) (.leaf 473187587)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1203).prefactor = (6327508126759771/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1203).cutoff/(generalMeanRows 1203).c)).2 =
    (26365867904317/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1203).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1203).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1203).q*(generalMeanRows 1203).c/2-2 = (3367/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable405.value]
    have hcontinuation : (generalMeanRows 1203).q*(generalMeanRows 1203).cutoff/2-2 = (269/77:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable404.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1203).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1203

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1203).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1203).criticalRate j.val*(generalMeanRows 1203).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1203).c*(generalMeanRows 1203).criticalPoint j.val)).2-
      (generalMeanRows 1203).J/2-(generalMeanRows 1203).error (generalMeanGrid j.val)+
      (generalMeanRows 1203).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1203).c)).2-
      (generalMeanRows 1203).J/2-(generalMeanRows 1203).error 4 := by
  have he : (generalMeanRows 1203).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1203) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1203)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1203

/-! Kernel-checked entropy margins for general spectral rectangle 1204. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1204
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6128387391) (.branch 2 (.leaf 5964538544) (.leaf 5806808766))) (.branch 5 (.branch 4 (.leaf 5654848618) (.leaf 5508336116)) (.branch 6 (.leaf 5366974110) (.leaf 5230487956)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5098623434) (.leaf 4971144900)) (.branch 10 (.leaf 4847833616) (.leaf 4728486264))) (.branch 13 (.branch 12 (.leaf 4612913603) (.leaf 4500939266)) (.branch 14 (.leaf 4392398671) (.leaf 4287138040))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4185013509) (.branch 17 (.leaf 4085890324) (.leaf 3989642117))) (.branch 20 (.branch 19 (.leaf 3896150235) (.leaf 3805303145)) (.branch 21 (.leaf 3716995885) (.leaf 3631129562)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3547610901) (.leaf 3466351827)) (.branch 25 (.leaf 3387269086) (.leaf 3310283897))) (.branch 28 (.branch 27 (.leaf 3235321635) (.leaf 3162311537)) (.branch 29 (.leaf 3091186440) (.leaf 3021882528)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2954339112) (.branch 32 (.leaf 2888498421) (.leaf 2824305409))) (.branch 35 (.branch 34 (.leaf 2761707582) (.leaf 2700654832)) (.branch 36 (.leaf 2641099290) (.leaf 2582995189)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2526298730) (.leaf 2470967971)) (.branch 40 (.leaf 2416962712) (.leaf 2364244395))) (.branch 43 (.branch 42 (.leaf 2312776013) (.leaf 2262522017)) (.branch 44 (.leaf 2213448239) (.leaf 2165521814))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2118711114) (.branch 47 (.leaf 2072985676) (.leaf 2028316147))) (.branch 50 (.branch 49 (.leaf 1984674224) (.leaf 1942032602)) (.branch 51 (.leaf 1900364925) (.leaf 1859645737)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1819850443) (.leaf 1780955264)) (.branch 55 (.leaf 1742937202) (.leaf 1705774004))) (.branch 58 (.branch 57 (.leaf 1669444125) (.leaf 1633926704)) (.branch 59 (.leaf 1599201524) (.leaf 1565248994))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1532050117) (.branch 62 (.leaf 1499586467) (.leaf 1467840166))) (.branch 65 (.branch 64 (.leaf 1436793860) (.leaf 1406430700)) (.branch 66 (.leaf 1376734325) (.leaf 1347688835)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1319278782) (.leaf 1291489150)) (.branch 70 (.leaf 1264305338) (.leaf 1237713145))) (.branch 73 (.branch 72 (.leaf 1211698759) (.leaf 1186248738)) (.branch 74 (.leaf 1161350002) (.leaf 1136989819))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1113155790) (.branch 77 (.leaf 1089835844) (.leaf 1067018221))) (.branch 80 (.branch 79 (.leaf 1044691467) (.leaf 1022844420)) (.branch 81 (.leaf 1001466204) (.leaf 980546217)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 960074124) (.leaf 940039851)) (.branch 85 (.leaf 920433572) (.leaf 901245706))) (.branch 88 (.branch 87 (.leaf 882466908) (.leaf 864088061)) (.branch 89 (.leaf 846100270) (.leaf 828494859)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 811263357) (.branch 92 (.leaf 794397502) (.leaf 777889225))) (.branch 95 (.branch 94 (.leaf 761730653) (.leaf 745914098)) (.branch 96 (.leaf 730432055) (.leaf 715277196)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 700442365) (.leaf 685920573)) (.branch 100 (.leaf 671704995) (.leaf 657788963))) (.branch 103 (.branch 102 (.leaf 644165967) (.leaf 630829643)) (.branch 104 (.leaf 617773778) (.leaf 604992299))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 592479272) (.leaf 580228901)) (.branch 108 (.leaf 568235519) (.leaf 556493590))) (.branch 111 (.branch 110 (.leaf 544997703) (.leaf 533742570)) (.branch 112 (.leaf 522723020) (.leaf 511934001)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 501370574) (.leaf 491027909)) (.branch 116 (.leaf 480901286) (.leaf 470986090))) (.branch 119 (.branch 118 (.leaf 461277809) (.leaf 451772029)) (.branch 120 (.leaf 442464437) (.leaf 433350815)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1204).prefactor = (2599039430481023/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1204).cutoff/(generalMeanRows 1204).c)).2 =
    (653655432126967/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1204).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1204).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1204).q*(generalMeanRows 1204).c/2-2 = (3259/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable253.value]
    have hcontinuation : (generalMeanRows 1204).q*(generalMeanRows 1204).cutoff/2-2 = (1600/469:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable406.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1204).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1204

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1204).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1204).criticalRate j.val*(generalMeanRows 1204).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1204).c*(generalMeanRows 1204).criticalPoint j.val)).2-
      (generalMeanRows 1204).J/2-(generalMeanRows 1204).error (generalMeanGrid j.val)+
      (generalMeanRows 1204).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1204).c)).2-
      (generalMeanRows 1204).J/2-(generalMeanRows 1204).error 4 := by
  have he : (generalMeanRows 1204).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1204) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1204)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1204

/-! Kernel-checked entropy margins for general spectral rectangle 1205. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1205
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6305239557) (.branch 2 (.leaf 6134555904) (.leaf 5970279676))) (.branch 5 (.branch 4 (.leaf 5812045471) (.leaf 5659516532)) (.branch 6 (.leaf 5512382018) (.leaf 5370354575)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5233168173) (.leaf 5100576164)) (.branch 10 (.leaf 4972349558) (.leaf 4848275461))) (.branch 13 (.branch 12 (.leaf 4728155681) (.leaf 4611805474)) (.branch 14 (.leaf 4499052404) (.leaf 4389735321))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4283703437) (.branch 17 (.leaf 4180815486) (.leaf 4080938962))) (.branch 20 (.branch 19 (.leaf 3983949429) (.leaf 3889729894)) (.branch 21 (.leaf 3798170237) (.leaf 3709166686)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3622621346) (.leaf 3538441764)) (.branch 25 (.leaf 3456540532) (.leaf 3376834927))) (.branch 28 (.branch 27 (.leaf 3299246576) (.leaf 3223701151)) (.branch 29 (.leaf 3150128095) (.leaf 3078460360)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3008634173) (.branch 32 (.leaf 2940588820) (.leaf 2874266447))) (.branch 35 (.branch 34 (.leaf 2809611873) (.leaf 2746572424)) (.branch 36 (.leaf 2685097773) (.leaf 2625139798)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2566652448) (.leaf 2509591616)) (.branch 40 (.leaf 2453915030) (.leaf 2399582141))) (.branch 43 (.branch 42 (.leaf 2346554028) (.leaf 2294793307)) (.branch 44 (.leaf 2244264042) (.leaf 2194931672))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2146762930) (.branch 47 (.leaf 2099725782) (.leaf 2053789359))) (.branch 50 (.branch 49 (.leaf 2008923896) (.leaf 1965100683)) (.branch 51 (.leaf 1922292003) (.leaf 1880471095)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1839612098) (.leaf 1799690015)) (.branch 55 (.leaf 1760680670) (.leaf 1722560674))) (.branch 58 (.branch 57 (.leaf 1685307383) (.leaf 1648898875)) (.branch 59 (.leaf 1613313907) (.leaf 1578531897))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1544532889) (.branch 62 (.leaf 1511297528) (.leaf 1478807039))) (.branch 65 (.branch 64 (.leaf 1447043201) (.leaf 1415988325)) (.branch 66 (.leaf 1385625234) (.leaf 1355937244)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1326908142) (.leaf 1298522174)) (.branch 70 (.leaf 1270764024) (.leaf 1243618799))) (.branch 73 (.branch 72 (.leaf 1217072014) (.leaf 1191109578)) (.branch 74 (.leaf 1165717781) (.leaf 1140883278))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1116593082) (.branch 77 (.leaf 1092834544) (.leaf 1069595350))) (.branch 80 (.branch 79 (.leaf 1046863506) (.leaf 1024627328)) (.branch 81 (.leaf 1002875431) (.leaf 981596722)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 960780391) (.leaf 940415900)) (.branch 85 (.leaf 920492974) (.leaf 901001599))) (.branch 88 (.branch 87 (.leaf 881932005) (.leaf 863274668)) (.branch 89 (.leaf 845020297) (.leaf 827159827)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 809684418) (.branch 92 (.leaf 792585442) (.leaf 775854481))) (.branch 95 (.branch 94 (.leaf 759483319) (.leaf 743463938)) (.branch 96 (.leaf 727788512) (.leaf 712449402)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 697439148) (.leaf 682750470)) (.branch 100 (.leaf 668376257) (.leaf 654309567))) (.branch 103 (.branch 102 (.leaf 640543620) (.leaf 627071795)) (.branch 104 (.leaf 613887625) (.leaf 600984792))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 588357128) (.leaf 575998605)) (.branch 108 (.leaf 563903333) (.leaf 552065560))) (.branch 111 (.branch 110 (.leaf 540479665) (.leaf 529140155)) (.branch 112 (.leaf 518041664) (.leaf 507178948)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 496546880) (.leaf 486140453)) (.branch 116 (.leaf 475954771) (.leaf 465985049))) (.branch 119 (.branch 118 (.leaf 456226610) (.leaf 446674883)) (.branch 120 (.leaf 437325400) (.leaf 428173792)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1205).prefactor = (5422766042552667/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1205).cutoff/(generalMeanRows 1205).c)).2 =
    (648870734003627/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1205).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1205).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1205).q*(generalMeanRows 1205).cutoff/2-2 = (1600/469:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable406.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1205).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1205

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1205).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1205).criticalRate j.val*(generalMeanRows 1205).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1205).c*(generalMeanRows 1205).criticalPoint j.val)).2-
      (generalMeanRows 1205).J/2-(generalMeanRows 1205).error (generalMeanGrid j.val)+
      (generalMeanRows 1205).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1205).c)).2-
      (generalMeanRows 1205).J/2-(generalMeanRows 1205).error 4 := by
  have he : (generalMeanRows 1205).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1205) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1205)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1205

/-! Kernel-checked entropy margins for general spectral rectangle 1206. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1206
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6487269176) (.branch 2 (.leaf 6309490897) (.leaf 6138421413))) (.branch 5 (.branch 4 (.leaf 5973678614) (.leaf 5814910283)) (.branch 6 (.leaf 5661791248) (.leaf 5514020851)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5371320690) (.leaf 5233432601)) (.branch 10 (.leaf 5100116853) (.leaf 4971150524))) (.branch 13 (.branch 12 (.leaf 4846326047) (.leaf 4725449899)) (.branch 14 (.leaf 4608341415) (.leaf 4494831724))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4384762781) (.branch 17 (.leaf 4277986493) (.leaf 4174363924))) (.branch 20 (.branch 19 (.leaf 4073764577) (.leaf 3976065736)) (.branch 21 (.leaf 3881151873) (.leaf 3788914103)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3699249689) (.leaf 3612061587)) (.branch 25 (.leaf 3527258038) (.leaf 3444752185))) (.branch 28 (.branch 27 (.leaf 3364461725) (.leaf 3286308597)) (.branch 29 (.leaf 3210218685) (.leaf 3136121554)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3063950199) (.branch 32 (.leaf 2993640824) (.leaf 2925132630))) (.branch 35 (.branch 34 (.leaf 2858367625) (.leaf 2793290444)) (.branch 36 (.leaf 2729848186) (.leaf 2667990266)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2607668270) (.leaf 2548835829)) (.branch 40 (.leaf 2491448499) (.leaf 2435463649))) (.branch 43 (.branch 42 (.leaf 2380840356) (.leaf 2327539314)) (.branch 44 (.leaf 2275522741) (.leaf 2224754297))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2175199008) (.branch 47 (.leaf 2126823195) (.leaf 2079594402))) (.branch 50 (.branch 49 (.leaf 2033481343) (.leaf 1988453833)) (.branch 51 (.leaf 1944482742) (.leaf 1901539938)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1859598245) (.leaf 1818631392)) (.branch 55 (.leaf 1778613977) (.leaf 1739521423))) (.branch 58 (.branch 57 (.leaf 1701329944) (.leaf 1664016508)) (.branch 59 (.leaf 1627558807) (.leaf 1591935225))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1557124806) (.branch 62 (.leaf 1523107231) (.leaf 1489862792))) (.branch 65 (.branch 64 (.leaf 1457372363) (.leaf 1425617382)) (.branch 66 (.leaf 1394579827) (.leaf 1364242194)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1334587480) (.leaf 1305599164)) (.branch 70 (.leaf 1277261186) (.leaf 1249557935))) (.branch 73 (.branch 72 (.leaf 1222474230) (.leaf 1195995305)) (.branch 74 (.leaf 1170106798) (.leaf 1144794730))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1120045500) (.branch 77 (.leaf 1095845867) (.leaf 1072182940))) (.branch 80 (.branch 79 (.leaf 1049044166) (.leaf 1026417322)) (.branch 81 (.leaf 1004290498) (.leaf 982652093)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 961490805) (.leaf 940795617)) (.branch 85 (.leaf 920555793) (.leaf 900760868))) (.branch 88 (.branch 87 (.leaf 881400639) (.leaf 862465159)) (.branch 89 (.leaf 843944728) (.leaf 825829885)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 808111404) (.branch 92 (.leaf 790780286) (.leaf 773827749))) (.branch 95 (.branch 94 (.leaf 757245228) (.leaf 741024364)) (.branch 96 (.leaf 725157002) (.leaf 709635182)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 694451135) (.leaf 679597280)) (.branch 100 (.leaf 665066214) (.leaf 650850712))) (.branch 103 (.branch 102 (.leaf 636943721) (.leaf 623338352)) (.branch 104 (.leaf 610027882) (.leaf 597005742))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 584265522) (.leaf 571800957)) (.branch 108 (.leaf 559605932) (.leaf 547674473))) (.branch 111 (.branch 110 (.leaf 536000744) (.leaf 524579045)) (.branch 112 (.leaf 513403808) (.leaf 502469594)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 491771087) (.leaf 481303096)) (.branch 116 (.leaf 471060548) (.leaf 461038484))) (.branch 119 (.branch 118 (.leaf 451232063) (.leaf 441636549)) (.branch 120 (.leaf 432247319) (.leaf 423059851)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1206).prefactor = (1414291334299797/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1206).cutoff/(generalMeanRows 1206).c)).2 =
    (80513602530423/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1206).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1206).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1206).q*(generalMeanRows 1206).c/2-2 = (3367/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable405.value]
    have hcontinuation : (generalMeanRows 1206).q*(generalMeanRows 1206).cutoff/2-2 = (1600/469:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable406.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1206).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1206

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1206).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1206).criticalRate j.val*(generalMeanRows 1206).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1206).c*(generalMeanRows 1206).criticalPoint j.val)).2-
      (generalMeanRows 1206).J/2-(generalMeanRows 1206).error (generalMeanGrid j.val)+
      (generalMeanRows 1206).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1206).c)).2-
      (generalMeanRows 1206).J/2-(generalMeanRows 1206).error 4 := by
  have he : (generalMeanRows 1206).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1206) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1206)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1206

/-! Kernel-checked entropy margins for general spectral rectangle 1207. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1207
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6674629881) (.branch 2 (.leaf 6489487740) (.leaf 6311369331))) (.branch 5 (.branch 4 (.leaf 6139875061) (.leaf 5974636532)) (.branch 6 (.leaf 5815313571) (.leaf 5661591593)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5513179244) (.leaf 5369806299)) (.branch 10 (.leaf 5231221781) (.leaf 5097192264))) (.branch 13 (.branch 12 (.leaf 4967500360) (.leaf 4841943351)) (.branch 14 (.leaf 4720331952) (.leaf 4602489201))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4488249449) (.branch 17 (.leaf 4377457451) (.leaf 4269967531))) (.branch 20 (.branch 19 (.leaf 4165642840) (.leaf 4064354666)) (.branch 21 (.leaf 3965981813) (.leaf 3870410036)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3777531524) (.leaf 3687244424)) (.branch 25 (.leaf 3599452414) (.leaf 3514064303))) (.branch 28 (.branch 27 (.leaf 3430993676) (.leaf 3350158554)) (.branch 29 (.leaf 3271481095) (.leaf 3194887313)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3120306820) (.branch 32 (.leaf 3047672589) (.leaf 2976920738))) (.branch 35 (.branch 34 (.leaf 2907990328) (.leaf 2840823178)) (.branch 36 (.leaf 2775363693) (.leaf 2711558705)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2649357331) (.leaf 2588710834)) (.branch 40 (.leaf 2529572495) (.leaf 2471897505))) (.branch 43 (.branch 42 (.leaf 2415642850) (.leaf 2360767210)) (.branch 44 (.leaf 2307230874) (.leaf 2254995644))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2204024760) (.branch 47 (.leaf 2154282824) (.leaf 2105735725))) (.branch 50 (.branch 49 (.leaf 2058350584) (.leaf 2012095680)) (.branch 51 (.leaf 1966940404) (.leaf 1922855199)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1879811511) (.leaf 1837781744)) (.branch 55 (.leaf 1796739215) (.leaf 1756658112))) (.branch 58 (.branch 57 (.leaf 1717513454) (.leaf 1679281059)) (.branch 59 (.leaf 1641937505) (.leaf 1605460099))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1569826848) (.branch 62 (.leaf 1535016429) (.leaf 1501008160))) (.branch 65 (.branch 64 (.leaf 1467781978) (.leaf 1435318413)) (.branch 66 (.leaf 1403598562) (.leaf 1372604074)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1342317122) (.leaf 1312720388)) (.branch 70 (.leaf 1283797044) (.leaf 1255530732))) (.branch 73 (.branch 72 (.leaf 1227905549) (.leaf 1200906031)) (.branch 74 (.leaf 1174517137) (.leaf 1148724236))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1123513088) (.branch 77 (.leaf 1098869840) (.leaf 1074781004))) (.branch 80 (.branch 79 (.leaf 1051233452) (.leaf 1028214398)) (.branch 81 (.leaf 1005711394) (.leaf 983712313)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 962205344) (.leaf 941178977)) (.branch 85 (.leaf 920621999) (.leaf 900523482))) (.branch 88 (.branch 87 (.leaf 880872775) (.leaf 861659496)) (.branch 89 (.leaf 842873523) (.leaf 824504987)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 806544267) (.branch 92 (.leaf 788981978) (.leaf 771808968))) (.branch 95 (.branch 94 (.leaf 755016311) (.leaf 738595300)) (.branch 96 (.leaf 722537439) (.leaf 706834441)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 691478218) (.leaf 676460881)) (.branch 100 (.leaf 661774729) (.leaf 647412246))) (.branch 103 (.branch 102 (.leaf 633366098) (.leaf 619629125)) (.branch 104 (.leaf 606194338) (.leaf 593054914))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 580204195) (.leaf 567635675)) (.branch 108 (.leaf 555343007) (.leaf 543319990))) (.branch 111 (.branch 110 (.leaf 531560571) (.leaf 520058838)) (.branch 112 (.leaf 508809017) (.leaf 497805469)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 487042688) (.leaf 476515294)) (.branch 116 (.leaf 466218034) (.leaf 456145774))) (.branch 119 (.branch 118 (.leaf 446293502) (.leaf 436656319)) (.branch 120 (.leaf 427229442) (.leaf 418008195)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1207).prefactor = (1475424137851191/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1207).cutoff/(generalMeanRows 1207).c)).2 =
    (639369474879489/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1207).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1207).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1207).q*(generalMeanRows 1207).c/2-2 = (3421/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable252.value]
    have hcontinuation : (generalMeanRows 1207).q*(generalMeanRows 1207).cutoff/2-2 = (1600/469:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable406.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1207).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1207

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1207).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1207).criticalRate j.val*(generalMeanRows 1207).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1207).c*(generalMeanRows 1207).criticalPoint j.val)).2-
      (generalMeanRows 1207).J/2-(generalMeanRows 1207).error (generalMeanGrid j.val)+
      (generalMeanRows 1207).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1207).c)).2-
      (generalMeanRows 1207).J/2-(generalMeanRows 1207).error 4 := by
  have he : (generalMeanRows 1207).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1207) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1207)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1207

/-! Kernel-checked entropy margins for general spectral rectangle 1208. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1208
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6867479933) (.branch 2 (.leaf 6674694945) (.leaf 6489262771))) (.branch 5 (.branch 4 (.leaf 6310765524) (.leaf 6138817870)) (.branch 6 (.leaf 5973063936) (.leaf 5813174557)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5658844820) (.leaf 5509791873)) (.branch 10 (.leaf 5365752957) (.leaf 5226483650))) (.branch 13 (.branch 12 (.leaf 5091756277) (.leaf 4961358487)) (.branch 14 (.leaf 4835091967) (.leaf 4712771276))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4594222801) (.branch 17 (.leaf 4479283799) (.leaf 4367801539))) (.branch 20 (.branch 19 (.leaf 4259632511) (.leaf 4154641719)) (.branch 21 (.leaf 4052702032) (.leaf 3953693586)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3857503253) (.leaf 3764024140)) (.branch 25 (.leaf 3673155144) (.leaf 3584800537))) (.branch 28 (.branch 27 (.leaf 3498869588) (.leaf 3415276219)) (.branch 29 (.leaf 3333938683) (.leaf 3254779274)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3177724058) (.branch 32 (.leaf 3102702628) (.leaf 3029647872))) (.branch 35 (.branch 34 (.leaf 2958495766) (.leaf 2889185179)) (.branch 36 (.leaf 2821657695) (.leaf 2755857447)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2691730964) (.leaf 2629227030)) (.branch 40 (.leaf 2568296552) (.leaf 2508892439))) (.branch 43 (.branch 42 (.leaf 2450969489) (.leaf 2394484281)) (.branch 44 (.leaf 2339395083) (.leaf 2285661759))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2233245680) (.branch 47 (.leaf 2182109652) (.leaf 2132217840))) (.branch 50 (.branch 49 (.leaf 2083535696) (.leaf 2036029902)) (.branch 51 (.leaf 1989668301) (.leaf 1944419849)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1900254558) (.leaf 1857143450)) (.branch 55 (.leaf 1815058504) (.leaf 1773972623))) (.branch 58 (.branch 57 (.leaf 1733859583) (.leaf 1694694000)) (.branch 59 (.leaf 1656451295) (.leaf 1619107656))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1582640008) (.branch 62 (.leaf 1547025982) (.leaf 1512243889))) (.branch 65 (.branch 64 (.leaf 1478272688) (.leaf 1445091965)) (.branch 66 (.leaf 1412681906) (.leaf 1381023276)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1350097395) (.leaf 1319886119)) (.branch 70 (.leaf 1290371822) (.leaf 1261537371))) (.branch 73 (.branch 72 (.leaf 1233366116) (.leaf 1205841869)) (.branch 74 (.leaf 1178948886) (.leaf 1152671859))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1126995892) (.branch 77 (.leaf 1101906493) (.leaf 1077389561))) (.branch 80 (.branch 79 (.leaf 1053431368) (.leaf 1030018555)) (.branch 81 (.leaf 1007138110) (.leaf 984777367)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 962923988) (.leaf 941565957)) (.branch 85 (.leaf 920691567) (.leaf 900289413))) (.branch 88 (.branch 87 (.leaf 880348382) (.leaf 860857644)) (.branch 89 (.leaf 841806643) (.leaf 823185091)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 804982958) (.branch 92 (.leaf 787190466) (.leaf 769798080))) (.branch 95 (.branch 94 (.leaf 752796504) (.leaf 736176671)) (.branch 96 (.leaf 719929739) (.leaf 704047084)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 688520291) (.leaf 673341155)) (.branch 100 (.leaf 658501668) (.leaf 643994018))) (.branch 103 (.branch 102 (.leaf 629810583) (.leaf 615943924)) (.branch 104 (.leaf 602386784) (.leaf 589132078))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 576172892) (.leaf 563502478)) (.branch 108 (.leaf 551114249) (.leaf 539001776))) (.branch 111 (.branch 110 (.leaf 527158781) (.leaf 515579137)) (.branch 112 (.leaf 504256860) (.leaf 493186110)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 482361183) (.leaf 471776510)) (.branch 116 (.leaf 461426654) (.leaf 451306303))) (.branch 119 (.branch 118 (.leaf 441410271) (.leaf 431733495)) (.branch 120 (.leaf 422271027) (.leaf 413018037)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1208).prefactor = (3078398818913341/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1208).cutoff/(generalMeanRows 1208).c)).2 =
    (634652485001349/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1208).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1208).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1208).q*(generalMeanRows 1208).cutoff/2-2 = (1600/469:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable406.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1208).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1208

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1208).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1208).criticalRate j.val*(generalMeanRows 1208).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1208).c*(generalMeanRows 1208).criticalPoint j.val)).2-
      (generalMeanRows 1208).J/2-(generalMeanRows 1208).error (generalMeanGrid j.val)+
      (generalMeanRows 1208).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1208).c)).2-
      (generalMeanRows 1208).J/2-(generalMeanRows 1208).error 4 := by
  have he : (generalMeanRows 1208).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1208) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1208)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1208

/-! Kernel-checked entropy margins for general spectral rectangle 1209. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1209
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5785541924) (.branch 2 (.leaf 5619564718) (.leaf 5459893319))) (.branch 5 (.branch 4 (.leaf 5306171824) (.leaf 5158072384)) (.branch 6 (.leaf 5015292479) (.leaf 4877552503)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4744593613) (.leaf 4616175813)) (.branch 10 (.leaf 4492076238) (.leaf 4372087622))) (.branch 13 (.branch 12 (.leaf 4256016921) (.leaf 4143684078)) (.branch 14 (.leaf 4034920915) (.leaf 3929570125))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3827484375) (.branch 17 (.leaf 3728525485) (.leaf 3632563692))) (.branch 20 (.branch 19 (.leaf 3539476980) (.leaf 3449150473)) (.branch 21 (.leaf 3361475885) (.leaf 3276351019)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3193679310) (.leaf 3113369409)) (.branch 25 (.leaf 3035334807) (.leaf 2959493485))) (.branch 28 (.branch 27 (.leaf 2885767602) (.leaf 2814083200)) (.branch 29 (.leaf 2744369946) (.leaf 2676560881)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2610592203) (.branch 32 (.leaf 2546403061) (.leaf 2483935361))) (.branch 35 (.branch 34 (.leaf 2423133601) (.leaf 2363944703)) (.branch 36 (.leaf 2306317871) (.leaf 2250204453)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2195557812) (.leaf 2142333216)) (.branch 40 (.leaf 2090487723) (.leaf 2039980087))) (.branch 43 (.branch 42 (.leaf 1990770661) (.leaf 1942821313)) (.branch 44 (.leaf 1896095345) (.leaf 1850557417))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1806173482) (.branch 47 (.leaf 1762910716) (.leaf 1720737461))) (.branch 50 (.branch 49 (.leaf 1679623166) (.leaf 1639538338)) (.branch 51 (.leaf 1600454487) (.leaf 1562344084)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1525180515) (.leaf 1488938045)) (.branch 55 (.leaf 1453591770) (.leaf 1419117592))) (.branch 58 (.branch 57 (.leaf 1385492176) (.leaf 1352692925)) (.branch 59 (.leaf 1320697944) (.leaf 1289486015))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1259036570) (.branch 62 (.leaf 1229329662) (.leaf 1200345945))) (.branch 65 (.branch 64 (.leaf 1172066650) (.leaf 1144473561)) (.branch 66 (.leaf 1117548997) (.leaf 1091275793)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1065637278) (.leaf 1040617259)) (.branch 70 (.leaf 1016200005) (.leaf 992370232))) (.branch 73 (.branch 72 (.leaf 969113083) (.leaf 946414117)) (.branch 74 (.leaf 924259296) (.leaf 902634968))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 881527858) (.branch 77 (.leaf 860925052) (.leaf 840813988))) (.branch 80 (.branch 79 (.leaf 821182444) (.leaf 802018529)) (.branch 81 (.leaf 783310667) (.leaf 765047595)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 747218346) (.leaf 729812246)) (.branch 85 (.leaf 712818901) (.leaf 696228190))) (.branch 88 (.branch 87 (.leaf 680030258) (.leaf 664215506)) (.branch 89 (.leaf 648774584) (.leaf 633698386)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 618978039) (.branch 92 (.leaf 604604900) (.leaf 590570547))) (.branch 95 (.branch 94 (.leaf 576866773) (.leaf 563485582)) (.branch 96 (.leaf 550419179) (.leaf 537659970)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 525200550) (.leaf 513033704)) (.branch 100 (.leaf 501152395) (.leaf 489549767))) (.branch 103 (.branch 102 (.leaf 478219132) (.leaf 467153973)) (.branch 104 (.leaf 456347934) (.leaf 445794816))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 435488576) (.leaf 425423320)) (.branch 108 (.leaf 415593302) (.leaf 405992915))) (.branch 111 (.branch 110 (.leaf 396616693) (.leaf 387459303)) (.branch 112 (.leaf 378515544) (.leaf 369780342)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 361248749) (.leaf 352915937)) (.branch 116 (.leaf 344777195) (.leaf 336827930))) (.branch 119 (.branch 118 (.leaf 329063657) (.leaf 321480005)) (.branch 120 (.leaf 314072704) (.leaf 306837592)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1209).prefactor = (5407617040083821/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1209).cutoff/(generalMeanRows 1209).c)).2 =
    (337037449583589/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1209).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1209).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1209).q*(generalMeanRows 1209).c/2-2 = (183/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable021.value]
    have hcontinuation : (generalMeanRows 1209).q*(generalMeanRows 1209).cutoff/2-2 = (3240/871:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable407.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1209).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1209

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1209).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1209).criticalRate j.val*(generalMeanRows 1209).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1209).c*(generalMeanRows 1209).criticalPoint j.val)).2-
      (generalMeanRows 1209).J/2-(generalMeanRows 1209).error (generalMeanGrid j.val)+
      (generalMeanRows 1209).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1209).c)).2-
      (generalMeanRows 1209).J/2-(generalMeanRows 1209).error 4 := by
  have he : (generalMeanRows 1209).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1209) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1209)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1209

/-! Kernel-checked entropy margins for general spectral rectangle 1210. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1210
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6253001415) (.branch 2 (.leaf 6079727550) (.leaf 5912926434))) (.branch 5 (.branch 4 (.leaf 5752231896) (.leaf 5597306816)) (.branch 6 (.leaf 5447840300) (.leaf 5303545165)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5164155710) (.leaf 5029425720)) (.branch 10 (.leaf 4899126691) (.leaf 4773046230))) (.branch 13 (.branch 12 (.leaf 4650986637) (.leaf 4532763612)) (.branch 14 (.leaf 4418205111) (.leaf 4307150298))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4199448617) (.branch 17 (.leaf 4094958939) (.leaf 3993548798))) (.branch 20 (.branch 19 (.leaf 3895093698) (.leaf 3799476485)) (.branch 21 (.leaf 3706586774) (.leaf 3616320434)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3528579111) (.leaf 3443269801)) (.branch 25 (.leaf 3360304460) (.leaf 3279599643))) (.branch 28 (.branch 27 (.leaf 3201076176) (.leaf 3124658862)) (.branch 29 (.leaf 3050276203) (.leaf 2977860150)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2907345873) (.branch 32 (.leaf 2838671552) (.leaf 2771778177))) (.branch 35 (.branch 34 (.leaf 2706609375) (.leaf 2643111243)) (.branch 36 (.leaf 2581232195) (.leaf 2520922825)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2462135773) (.leaf 2404825611)) (.branch 40 (.leaf 2348948727) (.leaf 2294463229))) (.branch 43 (.branch 42 (.leaf 2241328840) (.leaf 2189506822)) (.branch 44 (.leaf 2138959882) (.leaf 2089652105))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2041548878) (.branch 47 (.leaf 1994616825) (.leaf 1948823748))) (.branch 50 (.branch 49 (.leaf 1904138564) (.leaf 1860531256)) (.branch 51 (.leaf 1817972821) (.leaf 1776435221)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1735891343) (.leaf 1696314954)) (.branch 55 (.leaf 1657680664) (.leaf 1619963887))) (.branch 58 (.branch 57 (.leaf 1583140810) (.leaf 1547188358)) (.branch 59 (.leaf 1512084165) (.leaf 1477806544))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1444334461) (.branch 62 (.leaf 1411647508) (.leaf 1379725879))) (.branch 65 (.branch 64 (.leaf 1348550349) (.leaf 1318102247)) (.branch 66 (.leaf 1288363443) (.leaf 1259316320)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1230943762) (.leaf 1203229132)) (.branch 70 (.leaf 1176156259) (.leaf 1149709415))) (.branch 73 (.branch 72 (.leaf 1123873310) (.leaf 1098633066)) (.branch 74 (.leaf 1073974212) (.leaf 1049882667))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1026344727) (.branch 77 (.leaf 1003347051) (.leaf 980876655))) (.branch 80 (.branch 79 (.leaf 958920896) (.leaf 937467462)) (.branch 81 (.leaf 916504362) (.leaf 896019918)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 876002753) (.leaf 856441782)) (.branch 85 (.leaf 837326206) (.leaf 818645499))) (.branch 88 (.branch 87 (.leaf 800389406) (.leaf 782547928)) (.branch 89 (.leaf 765111321) (.leaf 748070083)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 731414953) (.branch 92 (.leaf 715136899) (.leaf 699227115))) (.branch 95 (.branch 94 (.leaf 683677012) (.leaf 668478215)) (.branch 96 (.leaf 653622554) (.leaf 639102060)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 624908960) (.leaf 611035671)) (.branch 100 (.leaf 597474793) (.leaf 584219108))) (.branch 103 (.branch 102 (.leaf 571261572) (.leaf 558595313)) (.branch 104 (.leaf 546213622) (.leaf 534109954))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 522277921) (.leaf 510711288)) (.branch 108 (.leaf 499403967) (.leaf 488350019))) (.branch 111 (.branch 110 (.leaf 477543645) (.leaf 466979184)) (.branch 112 (.leaf 456651108) (.leaf 446554023)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 436682661) (.leaf 427031877)) (.branch 116 (.leaf 417596651) (.leaf 408372078))) (.branch 119 (.branch 118 (.leaf 399353370) (.leaf 390535850)) (.branch 120 (.leaf 381914953) (.leaf 373486218)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1210).prefactor = (1402326051178223/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1210).cutoff/(generalMeanRows 1210).c)).2 =
    (687805091979083/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1210).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1210).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1210).q*(generalMeanRows 1210).cutoff/2-2 = (3240/871:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable407.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1210).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1210

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1210).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1210).criticalRate j.val*(generalMeanRows 1210).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1210).c*(generalMeanRows 1210).criticalPoint j.val)).2-
      (generalMeanRows 1210).J/2-(generalMeanRows 1210).error (generalMeanGrid j.val)+
      (generalMeanRows 1210).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1210).c)).2-
      (generalMeanRows 1210).J/2-(generalMeanRows 1210).error 4 := by
  have he : (generalMeanRows 1210).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1210) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1210)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1210

/-! Kernel-checked entropy margins for general spectral rectangle 1211. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1211
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6846176525) (.branch 2 (.leaf 6667623824) (.leaf 6495561211))) (.branch 5 (.branch 4 (.leaf 6329619250) (.leaf 6169458159)) (.branch 6 (.leaf 6014764899) (.leaf 5865250604)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5720648289) (.leaf 5580710808)) (.branch 10 (.leaf 5445209030) (.leaf 5313930206))) (.branch 13 (.branch 12 (.leaf 5186676507) (.leaf 5063263711)) (.branch 14 (.leaf 4943520019) (.leaf 4827284996))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4714408610) (.branch 17 (.leaf 4604750367) (.leaf 4498178524))) (.branch 20 (.branch 19 (.leaf 4394569387) (.leaf 4293806665)) (.branch 21 (.leaf 4195780886) (.leaf 4100388871)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4007533250) (.leaf 3917122026)) (.branch 25 (.leaf 3829068173) (.leaf 3743289274))) (.branch 28 (.branch 27 (.leaf 3659707186) (.leaf 3578247741)) (.branch 29 (.leaf 3498840459) (.leaf 3421418303)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3345917439) (.branch 32 (.leaf 3272277023) (.leaf 3200439008))) (.branch 35 (.branch 34 (.leaf 3130347955) (.leaf 3061950877)) (.branch 36 (.leaf 2995197076) (.leaf 2930038007)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2866427149) (.leaf 2804319880)) (.branch 40 (.leaf 2743673366) (.leaf 2684446464))) (.branch 43 (.branch 42 (.leaf 2626599619) (.leaf 2570094780)) (.branch 44 (.leaf 2514895317) (.leaf 2460965945))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2408272653) (.branch 47 (.leaf 2356782635) (.leaf 2306464236))) (.branch 50 (.branch 49 (.leaf 2257286888) (.leaf 2209221057)) (.branch 51 (.leaf 2162238198) (.leaf 2116310702)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2071411860) (.leaf 2027515813)) (.branch 55 (.leaf 1984597520) (.leaf 1942632722))) (.branch 58 (.branch 57 (.leaf 1901597903) (.leaf 1861470265)) (.branch 59 (.leaf 1822227692) (.leaf 1783848726))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1746312539) (.branch 62 (.leaf 1709598906) (.leaf 1673688186))) (.branch 65 (.branch 64 (.leaf 1638561294) (.leaf 1604199684)) (.branch 66 (.leaf 1570585326) (.leaf 1537700689)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1505528723) (.leaf 1474052839)) (.branch 70 (.leaf 1443256897) (.leaf 1413125187))) (.branch 73 (.branch 72 (.leaf 1383642415) (.leaf 1354793690)) (.branch 74 (.leaf 1326564509) (.leaf 1298940747))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1271908640) (.branch 77 (.leaf 1245454778) (.leaf 1219566092))) (.branch 80 (.branch 79 (.leaf 1194229842) (.leaf 1169433610)) (.branch 81 (.leaf 1145165285) (.leaf 1121413060)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1098165418) (.leaf 1075411126)) (.branch 85 (.leaf 1053139223) (.leaf 1031339019))) (.branch 88 (.branch 87 (.leaf 1010000080) (.leaf 989112223)) (.branch 89 (.leaf 968665512) (.leaf 948650247)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 929056959) (.branch 92 (.leaf 909876404) (.leaf 891099555))) (.branch 95 (.branch 94 (.leaf 872717599) (.leaf 854721929)) (.branch 96 (.leaf 837104139) (.leaf 819856020)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 802969551) (.leaf 786436898)) (.branch 100 (.leaf 770250408) (.leaf 754402605))) (.branch 103 (.branch 102 (.leaf 738886181) (.leaf 723693998)) (.branch 104 (.leaf 708819081) (.leaf 694254612))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 679993927) (.leaf 666030516)) (.branch 108 (.leaf 652358013) (.leaf 638970196))) (.branch 111 (.branch 110 (.leaf 625860984) (.leaf 613024430)) (.branch 112 (.leaf 600454724) (.leaf 588146181)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 576093245) (.leaf 564290484)) (.branch 116 (.leaf 552732585) (.leaf 541414355))) (.branch 119 (.branch 118 (.leaf 530330713) (.leaf 519476691)) (.branch 120 (.leaf 508847432) (.leaf 498438184)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1211).prefactor = (286695474079043/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1211).cutoff/(generalMeanRows 1211).c)).2 =
    (355558085423773/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1211).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1211).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1211).q*(generalMeanRows 1211).cutoff/2-2 = (3240/871:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable407.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1211).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1211

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1211).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1211).criticalRate j.val*(generalMeanRows 1211).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1211).c*(generalMeanRows 1211).criticalPoint j.val)).2-
      (generalMeanRows 1211).J/2-(generalMeanRows 1211).error (generalMeanGrid j.val)+
      (generalMeanRows 1211).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1211).c)).2-
      (generalMeanRows 1211).J/2-(generalMeanRows 1211).error 4 := by
  have he : (generalMeanRows 1211).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1211) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1211)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1211

/-! Kernel-checked entropy margins for general spectral rectangle 1212. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1212
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6140605516) (.branch 2 (.leaf 5962441003) (.leaf 5791083962))) (.branch 5 (.branch 4 (.leaf 5626150387) (.leaf 5467286477)) (.branch 6 (.leaf 5314165704) (.leaf 5166486218)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5023968531) (.leaf 4886353456)) (.branch 10 (.leaf 4753400265) (.leaf 4624885036))) (.branch 13 (.branch 12 (.leaf 4500599176) (.leaf 4380348092)) (.branch 14 (.leaf 4263949993) (.leaf 4151234813))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4042043243) (.branch 17 (.leaf 3936225844) (.leaf 3833642261))) (.branch 20 (.branch 19 (.leaf 3734160497) (.leaf 3637656263)) (.branch 21 (.leaf 3544012382) (.leaf 3453118252)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3364869355) (.leaf 3279166807)) (.branch 25 (.leaf 3195916951) (.leaf 3115030987))) (.branch 28 (.branch 27 (.leaf 3036424626) (.leaf 2960017783)) (.branch 29 (.leaf 2885734289) (.leaf 2813501626)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2743250692) (.branch 32 (.leaf 2674915578) (.leaf 2608433361))) (.branch 35 (.branch 34 (.leaf 2543743921) (.leaf 2480789766)) (.branch 36 (.leaf 2419515876) (.leaf 2359869550)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2301800277) (.leaf 2245259605)) (.branch 40 (.leaf 2190201025) (.leaf 2136579867))) (.branch 43 (.branch 42 (.leaf 2084353194) (.leaf 2033479713)) (.branch 44 (.leaf 1983919688) (.leaf 1935634856))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1888588356) (.branch 47 (.leaf 1842744655) (.leaf 1798069487))) (.branch 50 (.branch 49 (.leaf 1754529787) (.leaf 1712093638)) (.branch 51 (.leaf 1670730215) (.leaf 1630409735)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1591103410) (.leaf 1552783402)) (.branch 55 (.leaf 1515422785) (.leaf 1478995501))) (.branch 58 (.branch 57 (.leaf 1443476325) (.leaf 1408840832)) (.branch 59 (.leaf 1375065362) (.leaf 1342126988))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1310003491) (.branch 62 (.leaf 1278673329) (.leaf 1248115609))) (.branch 65 (.branch 64 (.leaf 1218310068) (.leaf 1189237044)) (.branch 66 (.leaf 1160877454) (.leaf 1133212779)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1106225034) (.leaf 1079896756)) (.branch 70 (.leaf 1054210982) (.leaf 1029151236))) (.branch 73 (.branch 72 (.leaf 1004701505) (.leaf 980846230)) (.branch 74 (.leaf 957570287) (.leaf 934858972))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 912697992) (.branch 77 (.leaf 891073445) (.leaf 869971812))) (.branch 80 (.branch 79 (.leaf 849379942) (.leaf 829285042)) (.branch 81 (.leaf 809674665) (.leaf 790536701)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 771859362) (.leaf 753631178)) (.branch 85 (.leaf 735840981) (.leaf 718477903))) (.branch 88 (.branch 87 (.leaf 701531360) (.leaf 684991049)) (.branch 89 (.leaf 668846935) (.leaf 653089248)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 637708472) (.branch 92 (.leaf 622695338) (.leaf 608040817))) (.branch 95 (.branch 94 (.leaf 593736115) (.leaf 579772663)) (.branch 96 (.leaf 566142113) (.leaf 552836332)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 539847393) (.leaf 527167573)) (.branch 100 (.leaf 514789345) (.leaf 502705375))) (.branch 103 (.branch 102 (.leaf 490908511) (.leaf 479391786)) (.branch 104 (.leaf 468148407) (.leaf 457171752))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 446455365) (.leaf 435992955)) (.branch 108 (.leaf 425778385) (.leaf 415805674))) (.branch 111 (.branch 110 (.leaf 406068988) (.leaf 396562641)) (.branch 112 (.leaf 387281088) (.leaf 378218919)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 369370862) (.leaf 360731773)) (.branch 116 (.leaf 352296636) (.leaf 344060560))) (.branch 119 (.branch 118 (.leaf 336018774) (.leaf 328166622)) (.branch 120 (.leaf 320499568) (.leaf 313013182)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1212).prefactor = (5818513668364729/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1212).cutoff/(generalMeanRows 1212).c)).2 =
    (66953974400179/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1212).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1212).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1212).q*(generalMeanRows 1212).cutoff/2-2 = (3240/871:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable407.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1212).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1212

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1212).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1212).criticalRate j.val*(generalMeanRows 1212).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1212).c*(generalMeanRows 1212).criticalPoint j.val)).2-
      (generalMeanRows 1212).J/2-(generalMeanRows 1212).error (generalMeanGrid j.val)+
      (generalMeanRows 1212).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1212).c)).2-
      (generalMeanRows 1212).J/2-(generalMeanRows 1212).error 4 := by
  have he : (generalMeanRows 1212).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1212) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1212)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1212

/-! Kernel-checked entropy margins for general spectral rectangle 1213. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1213
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6283177919) (.branch 2 (.leaf 6098829297) (.leaf 5921564833))) (.branch 5 (.branch 4 (.leaf 5750985094) (.leaf 5586721993)) (.branch 6 (.leaf 5428435760) (.leaf 5275812244)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5128560514) (.leaf 4986410726)) (.branch 10 (.leaf 4849112205) (.leaf 4716431738))) (.branch 13 (.branch 12 (.leaf 4588152038) (.leaf 4464070365)) (.branch 14 (.leaf 4343997287) (.leaf 4227755561))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4115179127) (.branch 17 (.leaf 4006112191) (.leaf 3900408405))) (.branch 20 (.branch 19 (.leaf 3797930120) (.leaf 3698547703)) (.branch 21 (.leaf 3602138927) (.leaf 3508588407)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3417787094) (.leaf 3329631806)) (.branch 25 (.leaf 3244024808) (.leaf 3160873420))) (.branch 28 (.branch 27 (.leaf 3080089670) (.leaf 3001589963)) (.branch 29 (.leaf 2925294787) (.leaf 2851128442)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2779018788) (.branch 32 (.leaf 2708897014) (.leaf 2640697429))) (.branch 35 (.branch 34 (.leaf 2574357266) (.leaf 2509816502)) (.branch 36 (.leaf 2447017695) (.leaf 2385905827)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2326428163) (.leaf 2268534123)) (.branch 40 (.leaf 2212175160) (.leaf 2157304643))) (.branch 43 (.branch 42 (.leaf 2103877759) (.leaf 2051851410)) (.branch 44 (.leaf 2001184126) (.leaf 1951835982))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1903768516) (.branch 47 (.leaf 1856944657) (.leaf 1811328659))) (.branch 50 (.branch 49 (.leaf 1766886035) (.leaf 1723583497)) (.branch 51 (.leaf 1681388901) (.leaf 1640271195)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1600200368) (.leaf 1561147405)) (.branch 55 (.leaf 1523084244) (.leaf 1485983732))) (.branch 58 (.branch 57 (.leaf 1449819592) (.leaf 1414566381)) (.branch 59 (.leaf 1380199459) (.leaf 1346694954))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1314029734) (.branch 62 (.leaf 1282181378) (.leaf 1251128145))) (.branch 65 (.branch 64 (.leaf 1220848951) (.leaf 1191323345)) (.branch 66 (.leaf 1162531483) (.leaf 1134454106)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1107072520) (.leaf 1080368576)) (.branch 70 (.leaf 1054324649) (.leaf 1028923621))) (.branch 73 (.branch 72 (.leaf 1004148864) (.leaf 979984220)) (.branch 74 (.leaf 956413990) (.leaf 933422915))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 910996163) (.branch 77 (.leaf 889119313) (.leaf 867778345))) (.branch 80 (.branch 79 (.leaf 846959625) (.leaf 826649891)) (.branch 81 (.leaf 806836245) (.leaf 787506140)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 768647368) (.leaf 750248050)) (.branch 85 (.leaf 732296627) (.leaf 714781849))) (.branch 88 (.branch 87 (.leaf 697692766) (.leaf 681018721)) (.branch 89 (.leaf 664749338) (.leaf 648874514)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 633384415) (.branch 92 (.leaf 618269464) (.leaf 603520335))) (.branch 95 (.branch 94 (.leaf 589127944) (.leaf 575083446)) (.branch 96 (.leaf 561378225) (.leaf 548003888)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 534952260) (.leaf 522215375)) (.branch 100 (.leaf 509785474) (.leaf 497654997))) (.branch 103 (.branch 102 (.leaf 485816577) (.leaf 474263035)) (.branch 104 (.leaf 462987377) (.leaf 451982786))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 441242618) (.leaf 430760398)) (.branch 108 (.leaf 420529817) (.leaf 410544722))) (.branch 111 (.branch 110 (.leaf 400799118) (.leaf 391287161)) (.branch 112 (.leaf 382003153) (.leaf 372941539)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 364096906) (.leaf 355463973)) (.branch 116 (.leaf 347037594) (.leaf 338812751))) (.branch 119 (.branch 118 (.leaf 330784550) (.leaf 322948220)) (.branch 120 (.leaf 315299109) (.leaf 307832681)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1213).prefactor = (6035525989213141/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1213).cutoff/(generalMeanRows 1213).c)).2 =
    (665025063647263/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1213).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1213).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1213).q*(generalMeanRows 1213).cutoff/2-2 = (3240/871:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable407.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1213).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1213

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1213).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1213).criticalRate j.val*(generalMeanRows 1213).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1213).c*(generalMeanRows 1213).criticalPoint j.val)).2-
      (generalMeanRows 1213).J/2-(generalMeanRows 1213).error (generalMeanGrid j.val)+
      (generalMeanRows 1213).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1213).c)).2-
      (generalMeanRows 1213).J/2-(generalMeanRows 1213).error 4 := by
  have he : (generalMeanRows 1213).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1213) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1213)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1213

/-! Kernel-checked entropy margins for general spectral rectangle 1214. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1214
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6790462593) (.branch 2 (.leaf 6597868993) (.leaf 6412551083))) (.branch 5 (.branch 4 (.leaf 6234097950) (.leaf 6062131139)) (.branch 6 (.leaf 5896301499) (.leaf 5736286388)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5581787178) (.leaf 5432527036)) (.branch 10 (.leaf 5288248941) (.leaf 5148713902))) (.branch 13 (.branch 12 (.leaf 5013699373) (.leaf 4882997817)) (.branch 14 (.leaf 4756415418) (.leaf 4633770928))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4514894615) (.branch 17 (.leaf 4399627321) (.leaf 4287819605))) (.branch 20 (.branch 19 (.leaf 4179330972) (.leaf 4074029167)) (.branch 21 (.leaf 3971789541) (.leaf 3872494467)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3776032819) (.leaf 3682299483)) (.branch 25 (.leaf 3591194927) (.leaf 3502624795))) (.branch 28 (.branch 27 (.leaf 3416499544) (.leaf 3332734109)) (.branch 29 (.leaf 3251247595) (.leaf 3171962999)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3094806948) (.branch 32 (.leaf 3019709467) (.leaf 2946603758))) (.branch 35 (.branch 34 (.leaf 2875425997) (.leaf 2806115158)) (.branch 36 (.leaf 2738612831) (.leaf 2672863077)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2608812271) (.leaf 2546408977)) (.branch 40 (.leaf 2485603817) (.leaf 2426349360))) (.branch 43 (.branch 42 (.leaf 2368600013) (.leaf 2312311921)) (.branch 44 (.leaf 2257442876) (.leaf 2203952233))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2151800823) (.branch 47 (.leaf 2100950886) (.leaf 2051366000))) (.branch 50 (.branch 49 (.leaf 2003011011) (.leaf 1955851977)) (.branch 51 (.leaf 1909856110) (.leaf 1864991721)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1821228175) (.leaf 1778535836)) (.branch 55 (.leaf 1736886029) (.leaf 1696250999))) (.branch 58 (.branch 57 (.leaf 1656603866) (.leaf 1617918595)) (.branch 59 (.leaf 1580169958) (.leaf 1543333501))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1507385513) (.branch 62 (.leaf 1472302999) (.leaf 1438063650))) (.branch 65 (.branch 64 (.leaf 1404645818) (.leaf 1372028490)) (.branch 66 (.leaf 1340191265) (.leaf 1309114332)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1278778447) (.leaf 1249164918)) (.branch 70 (.leaf 1220255576) (.leaf 1192032767))) (.branch 73 (.branch 72 (.leaf 1164479326) (.leaf 1137578568)) (.branch 74 (.leaf 1111314264) (.leaf 1085670633))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1060632321) (.branch 77 (.leaf 1036184393) (.leaf 1012312316))) (.branch 80 (.branch 79 (.leaf 989001945) (.leaf 966239515)) (.branch 81 (.leaf 944011626) (.leaf 922305230)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 901107628) (.leaf 880406449)) (.branch 85 (.leaf 860189647) (.leaf 840445489))) (.branch 88 (.branch 87 (.leaf 821162548) (.leaf 802329689)) (.branch 89 (.leaf 783936065) (.leaf 765971109)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 748424519) (.branch 92 (.leaf 731286261) (.leaf 714546553))) (.branch 95 (.branch 94 (.leaf 698195861) (.leaf 682224891)) (.branch 96 (.leaf 666624585) (.leaf 651386110)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 636500856) (.leaf 621960427)) (.branch 100 (.leaf 607756638) (.leaf 593881504))) (.branch 103 (.branch 102 (.leaf 580327242) (.leaf 567086258)) (.branch 104 (.leaf 554151149) (.leaf 541514691))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 529169840) (.leaf 517109724)) (.branch 108 (.leaf 505327639) (.leaf 493817045))) (.branch 111 (.branch 110 (.leaf 482571563) (.leaf 471584966)) (.branch 112 (.leaf 460851183) (.leaf 450364286)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 440118494) (.leaf 430108164)) (.branch 116 (.leaf 420327789) (.leaf 410771997))) (.branch 119 (.branch 118 (.leaf 401435543) (.leaf 392313310)) (.branch 120 (.leaf 383400303) (.leaf 374691647)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1214).prefactor = (6260632189372349/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1214).cutoff/(generalMeanRows 1214).c)).2 =
    (678630715703041/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1214).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1214).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1214).q*(generalMeanRows 1214).cutoff/2-2 = (3240/871:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable407.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1214).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1214

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1214).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1214).criticalRate j.val*(generalMeanRows 1214).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1214).c*(generalMeanRows 1214).criticalPoint j.val)).2-
      (generalMeanRows 1214).J/2-(generalMeanRows 1214).error (generalMeanGrid j.val)+
      (generalMeanRows 1214).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1214).c)).2-
      (generalMeanRows 1214).J/2-(generalMeanRows 1214).error 4 := by
  have he : (generalMeanRows 1214).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1214) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1214)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1214

/-! Kernel-checked entropy margins for general spectral rectangle 1215. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1215
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7440729823) (.branch 2 (.leaf 7239394102) (.leaf 7045496562))) (.branch 5 (.branch 4 (.leaf 6858615524) (.leaf 6678362915)) (.branch 6 (.leaf 6504380993) (.leaf 6336339434)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6173932745) (.leaf 6016877951)) (.branch 10 (.leaf 5864912540) (.leaf 5717792609))) (.branch 13 (.branch 12 (.leaf 5575291216) (.leaf 5437196892)) (.branch 14 (.leaf 5303312304) (.leaf 5173453052))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5047446586) (.branch 17 (.leaf 4925131223) (.leaf 4806355262))) (.branch 20 (.branch 19 (.leaf 4690976182) (.leaf 4578859911)) (.branch 21 (.leaf 4469880170) (.leaf 4363917872)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4260860574) (.leaf 4160601982)) (.branch 25 (.leaf 4063041495) (.leaf 3968083798))) (.branch 28 (.branch 27 (.leaf 3875638475) (.leaf 3785619672)) (.branch 29 (.leaf 3697945776) (.leaf 3612539127)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3529325753) (.branch 32 (.leaf 3448235125) (.leaf 3369199932))) (.branch 35 (.branch 34 (.leaf 3292155878) (.leaf 3217041490)) (.branch 36 (.leaf 3143797942) (.leaf 3072368898)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3002700359) (.leaf 2934740526)) (.branch 40 (.leaf 2868439677) (.leaf 2803750042))) (.branch 43 (.branch 42 (.leaf 2740625699) (.leaf 2679022473)) (.branch 44 (.leaf 2618897837) (.leaf 2560210830))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2502921972) (.branch 47 (.leaf 2446993190) (.leaf 2392387748))) (.branch 50 (.branch 49 (.leaf 2339070179) (.leaf 2287006223)) (.branch 51 (.leaf 2236162775) (.leaf 2186507822)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2138010402) (.leaf 2090640550)) (.branch 55 (.leaf 2044369256) (.leaf 1999168424))) (.branch 58 (.branch 57 (.leaf 1955010831) (.leaf 1911870094)) (.branch 59 (.leaf 1869720629) (.leaf 1828537623))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1788297001) (.branch 62 (.leaf 1748975399) (.leaf 1710550134))) (.branch 65 (.branch 64 (.leaf 1672999179) (.leaf 1636301136)) (.branch 66 (.leaf 1600435216) (.leaf 1565381216)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1531119496) (.leaf 1497630959)) (.branch 70 (.leaf 1464897034) (.leaf 1432899656))) (.branch 73 (.branch 72 (.leaf 1401621249) (.leaf 1371044710)) (.branch 74 (.leaf 1341153393) (.leaf 1311931092))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1283362031) (.branch 77 (.leaf 1255430845) (.leaf 1228122571))) (.branch 80 (.branch 79 (.leaf 1201422634) (.leaf 1175316833)) (.branch 81 (.leaf 1149791333) (.leaf 1124832649)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1100427641) (.leaf 1076563501)) (.branch 85 (.leaf 1053227741) (.leaf 1030408186))) (.branch 88 (.branch 87 (.leaf 1008092967) (.leaf 986270507)) (.branch 89 (.leaf 964929515) (.leaf 944058980)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 923648161) (.branch 92 (.leaf 903686579) (.leaf 884164009))) (.branch 95 (.branch 94 (.leaf 865070476) (.leaf 846396247)) (.branch 96 (.leaf 828131821) (.leaf 810267929)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 792795522) (.leaf 775705768)) (.branch 100 (.leaf 758990046) (.leaf 742639938))) (.branch 103 (.branch 102 (.leaf 726647228) (.leaf 711003894)) (.branch 104 (.leaf 695702103) (.leaf 680734206))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 666092733) (.leaf 651770391)) (.branch 108 (.leaf 637760056) (.leaf 624054771))) (.branch 111 (.branch 110 (.leaf 610647741) (.leaf 597532328)) (.branch 112 (.leaf 584702049) (.leaf 572150569)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 559871704) (.leaf 547859407)) (.branch 116 (.leaf 536107774) (.leaf 524611035))) (.branch 119 (.branch 118 (.leaf 513363553) (.leaf 502359820)) (.branch 120 (.leaf 491594454) (.leaf 481062196)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1215).prefactor = (6494134145169207/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1215).cutoff/(generalMeanRows 1215).c)).2 =
    (87133052173987/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1215).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1215).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1215).q*(generalMeanRows 1215).c/2-2 = (679/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable164.value]
    have hcontinuation : (generalMeanRows 1215).q*(generalMeanRows 1215).cutoff/2-2 = (3240/871:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable407.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1215).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1215

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1215).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1215).criticalRate j.val*(generalMeanRows 1215).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1215).c*(generalMeanRows 1215).criticalPoint j.val)).2-
      (generalMeanRows 1215).J/2-(generalMeanRows 1215).error (generalMeanGrid j.val)+
      (generalMeanRows 1215).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1215).c)).2-
      (generalMeanRows 1215).J/2-(generalMeanRows 1215).error 4 := by
  have he : (generalMeanRows 1215).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1215) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1215)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1215

/-! Kernel-checked entropy margins for general spectral rectangle 1216. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1216
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7957844782) (.branch 2 (.leaf 7752893334) (.leaf 7555352069))) (.branch 5 (.branch 4 (.leaf 7364798502) (.leaf 7180844134)) (.branch 6 (.leaf 7003131123) (.leaf 6831329326)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6665133675) (.leaf 6504261833)) (.branch 10 (.leaf 6348452097) (.leaf 6197461533))) (.branch 13 (.branch 12 (.leaf 6051064292) (.leaf 5909050104)) (.branch 14 (.leaf 5771222928) (.leaf 5637399728))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5507409374) (.branch 17 (.leaf 5381091650) (.leaf 5258296355))) (.branch 20 (.branch 19 (.leaf 5138882493) (.leaf 5022717534)) (.branch 21 (.leaf 4909676746) (.leaf 4799642591)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4692504169) (.leaf 4588156721)) (.branch 25 (.leaf 4486501165) (.leaf 4387443685))) (.branch 28 (.branch 27 (.leaf 4290895345) (.leaf 4196771744)) (.branch 29 (.leaf 4104992694) (.leaf 4015481933)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3928166852) (.branch 32 (.leaf 3842978254) (.leaf 3759850127))) (.branch 35 (.branch 34 (.leaf 3678719438) (.leaf 3599525939)) (.branch 36 (.leaf 3522211999) (.leaf 3446722432)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3373004359) (.leaf 3301007060)) (.branch 40 (.leaf 3230681857) (.leaf 3161981985))) (.branch 43 (.branch 42 (.leaf 3094862493) (.leaf 3029280137)) (.branch 44 (.leaf 2965193290) (.leaf 2902561850))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2841347166) (.branch 47 (.leaf 2781511955) (.leaf 2723020238))) (.branch 50 (.branch 49 (.leaf 2665837273) (.leaf 2609929494)) (.branch 51 (.leaf 2555264451) (.leaf 2501810762)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2449538060) (.leaf 2398416948)) (.branch 55 (.leaf 2348418953) (.leaf 2299516489))) (.branch 58 (.branch 57 (.leaf 2251682813) (.leaf 2204891994)) (.branch 59 (.leaf 2159118877) (.leaf 2114339049))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2070528811) (.branch 62 (.leaf 2027665152) (.leaf 1985725715))) (.branch 65 (.branch 64 (.leaf 1944688777) (.leaf 1904533225)) (.branch 66 (.leaf 1865238530) (.leaf 1826784728)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1789152398) (.leaf 1752322643)) (.branch 70 (.leaf 1716277073) (.leaf 1680997784))) (.branch 73 (.branch 72 (.leaf 1646467345) (.leaf 1612668780)) (.branch 74 (.leaf 1579585552) (.leaf 1547201550))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1515501077) (.branch 77 (.leaf 1484468831) (.leaf 1454089899))) (.branch 80 (.branch 79 (.leaf 1424349739) (.leaf 1395234174)) (.branch 81 (.leaf 1366729375) (.leaf 1338821856)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1311498460) (.leaf 1284746352)) (.branch 85 (.leaf 1258553005) (.leaf 1232906197))) (.branch 88 (.branch 87 (.leaf 1207793997) (.leaf 1183204761)) (.branch 89 (.leaf 1159127119) (.leaf 1135549974)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1112462487) (.branch 92 (.leaf 1089854075) (.leaf 1067714402))) (.branch 95 (.branch 94 (.leaf 1046033374) (.leaf 1024801129)) (.branch 96 (.leaf 1004008034) (.leaf 983644678)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 963701867) (.leaf 944170616)) (.branch 100 (.leaf 925042145) (.leaf 906307875))) (.branch 103 (.branch 102 (.leaf 887959420) (.leaf 869988584)) (.branch 104 (.leaf 852387357) (.leaf 835147907))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 818262579) (.leaf 801723889)) (.branch 108 (.leaf 785524520) (.leaf 769657316))) (.branch 111 (.branch 110 (.leaf 754115284) (.leaf 738891581)) (.branch 112 (.leaf 723979518) (.leaf 709372554)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 695064290) (.leaf 681048469)) (.branch 116 (.leaf 667318970) (.leaf 653869807))) (.branch 119 (.branch 118 (.leaf 640695123) (.leaf 627789191)) (.branch 120 (.leaf 615146407) (.leaf 602761288)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1216).prefactor = (6573887643755597/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1216).cutoff/(generalMeanRows 1216).c)).2 =
    (715844312043493/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1216).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1216).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1216).q*(generalMeanRows 1216).cutoff/2-2 = (3240/871:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable407.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1216).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1216

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1216).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1216).criticalRate j.val*(generalMeanRows 1216).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1216).c*(generalMeanRows 1216).criticalPoint j.val)).2-
      (generalMeanRows 1216).J/2-(generalMeanRows 1216).error (generalMeanGrid j.val)+
      (generalMeanRows 1216).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1216).c)).2-
      (generalMeanRows 1216).J/2-(generalMeanRows 1216).error 4 := by
  have he : (generalMeanRows 1216).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1216) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1216)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1216

/-! Kernel-checked entropy margins for general spectral rectangle 1217. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1217
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6113764444) (.branch 2 (.leaf 5941851999) (.leaf 5776291122))) (.branch 5 (.branch 4 (.leaf 5616727625) (.leaf 5462835677)) (.branch 6 (.leaf 5314314985) (.leaf 5170888287)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5032299131) (.leaf 4898309903)) (.branch 10 (.leaf 4768700069) (.leaf 4643264604))) (.branch 13 (.branch 12 (.leaf 4521812589) (.leaf 4404165955)) (.branch 14 (.leaf 4290158360) (.leaf 4179634173))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4072447568) (.branch 17 (.leaf 3968461702) (.leaf 3867547980))) (.branch 20 (.branch 19 (.leaf 3769585383) (.leaf 3674459871)) (.branch 21 (.leaf 3582063830) (.leaf 3492295582)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3405058936) (.leaf 3320262776)) (.branch 25 (.leaf 3237820693) (.leaf 3157650646))) (.branch 28 (.branch 27 (.leaf 3079674653) (.leaf 3003818511)) (.branch 29 (.leaf 2930011537) (.leaf 2858186334)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2788278574) (.branch 32 (.leaf 2720226801) (.leaf 2653972251))) (.branch 35 (.branch 34 (.leaf 2589458682) (.leaf 2526632222)) (.branch 36 (.leaf 2465441228) (.leaf 2405836153)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2347769429) (.leaf 2291195354)) (.branch 40 (.leaf 2236069986) (.leaf 2182351053))) (.branch 43 (.branch 42 (.leaf 2129997859) (.leaf 2078971206)) (.branch 44 (.leaf 2029233311) (.leaf 1980747745))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1933479354) (.branch 47 (.leaf 1887394209) (.leaf 1842459538))) (.branch 50 (.branch 49 (.leaf 1798643679) (.leaf 1755916024)) (.branch 51 (.leaf 1714246977) (.leaf 1673607904)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1633971094) (.leaf 1595309719)) (.branch 55 (.leaf 1557597796) (.leaf 1520810154))) (.branch 58 (.branch 57 (.leaf 1484922400) (.leaf 1449910886)) (.branch 59 (.leaf 1415752684) (.leaf 1382425553))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1349907916) (.branch 62 (.leaf 1318178834) (.leaf 1287217982))) (.branch 65 (.branch 64 (.leaf 1257005627) (.leaf 1227522608)) (.branch 66 (.leaf 1198750311) (.leaf 1170670654)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1143266067) (.leaf 1116519475)) (.branch 70 (.leaf 1090414280) (.leaf 1064934347))) (.branch 73 (.branch 72 (.leaf 1040063983) (.leaf 1015787933)) (.branch 74 (.leaf 992091353) (.leaf 968959808))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 946379251) (.branch 77 (.leaf 924336014) (.leaf 902816798))) (.branch 80 (.branch 79 (.leaf 881808657) (.leaf 861298991)) (.branch 81 (.leaf 841275532) (.leaf 821726338)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 802639780) (.leaf 784004534)) (.branch 85 (.leaf 765809571) (.leaf 748044149))) (.branch 88 (.branch 87 (.leaf 730697805) (.leaf 713760347)) (.branch 89 (.leaf 697221844) (.leaf 681072622)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 665303252) (.branch 92 (.leaf 649904549) (.leaf 634867560))) (.branch 95 (.branch 94 (.leaf 620183561) (.leaf 605844046)) (.branch 96 (.leaf 591840728) (.leaf 578165526)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564810564) (.leaf 551768162)) (.branch 100 (.leaf 539030834) (.leaf 526591280))) (.branch 103 (.branch 102 (.leaf 514442382) (.leaf 502577200)) (.branch 104 (.leaf 490988966) (.leaf 479671080))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 468617104) (.leaf 457820761)) (.branch 108 (.leaf 447275928) (.leaf 436976631))) (.branch 111 (.branch 110 (.leaf 426917046) (.leaf 417091489)) (.branch 112 (.leaf 407494417) (.leaf 398120422)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 388964228) (.leaf 380020688)) (.branch 116 (.leaf 371284780) (.leaf 362751604))) (.branch 119 (.branch 118 (.leaf 354416379) (.leaf 346274441)) (.branch 120 (.leaf 338321237) (.leaf 330552327)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1217).prefactor = (5647097634721877/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1217).cutoff/(generalMeanRows 1217).c)).2 =
    (147219820267611/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1217).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1217).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1217).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1217

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1217).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1217).criticalRate j.val*(generalMeanRows 1217).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1217).c*(generalMeanRows 1217).criticalPoint j.val)).2-
      (generalMeanRows 1217).J/2-(generalMeanRows 1217).error (generalMeanGrid j.val)+
      (generalMeanRows 1217).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1217).c)).2-
      (generalMeanRows 1217).J/2-(generalMeanRows 1217).error 4 := by
  have he : (generalMeanRows 1217).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1217) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1217)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1217

/-! Kernel-checked entropy margins for general spectral rectangle 1218. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1218
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5907349234) (.branch 2 (.leaf 5759532745) (.leaf 5616899150))) (.branch 5 (.branch 4 (.leaf 5479155829) (.leaf 5346034042)) (.branch 6 (.leaf 5217286538) (.leaf 5092685440)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4972020365) (.leaf 4855096753)) (.branch 10 (.leaf 4741734380) (.leaf 4631766029))) (.branch 13 (.branch 12 (.leaf 4525036299) (.leaf 4421400545)) (.branch 14 (.leaf 4320723925) (.leaf 4222880536))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4127752654) (.branch 17 (.leaf 4035230030) (.leaf 3945209269))) (.branch 20 (.branch 19 (.leaf 3857593267) (.leaf 3772290696)) (.branch 21 (.leaf 3689215541) (.leaf 3608286689)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3529427538) (.leaf 3452565661)) (.branch 25 (.leaf 3377632488) (.leaf 3304563018))) (.branch 28 (.branch 27 (.leaf 3233295567) (.leaf 3163771521)) (.branch 29 (.leaf 3095935128) (.leaf 3029733294)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2965115402) (.branch 32 (.leaf 2902033153) (.leaf 2840440403))) (.branch 35 (.branch 34 (.leaf 2780293032) (.leaf 2721548814)) (.branch 36 (.leaf 2664167296) (.leaf 2608109691)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2553338778) (.leaf 2499818812)) (.branch 40 (.leaf 2447515433) (.leaf 2396395594))) (.branch 43 (.branch 42 (.leaf 2346427481) (.leaf 2297580451)) (.branch 44 (.leaf 2249824968) (.leaf 2203132542))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2157475677) (.branch 47 (.leaf 2112827821) (.leaf 2069163319))) (.branch 50 (.branch 49 (.leaf 2026457369) (.leaf 1984685978)) (.branch 51 (.leaf 1943825931) (.leaf 1903854749)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1864750657) (.leaf 1826492555)) (.branch 55 (.leaf 1789059987) (.leaf 1752433111))) (.branch 58 (.branch 57 (.leaf 1716592680) (.leaf 1681520008)) (.branch 59 (.leaf 1647196956) (.leaf 1613605905))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1580729736) (.branch 62 (.leaf 1548551813) (.leaf 1517055962))) (.branch 65 (.branch 64 (.leaf 1486226457) (.leaf 1456047998)) (.branch 66 (.leaf 1426505702) (.leaf 1397585085)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1369272046) (.leaf 1341552858)) (.branch 70 (.leaf 1314414150) (.leaf 1287842902))) (.branch 73 (.branch 72 (.leaf 1261826427) (.leaf 1236352362)) (.branch 74 (.leaf 1211408659) (.leaf 1186983572))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1163065653) (.branch 77 (.leaf 1139643734) (.leaf 1116706928))) (.branch 80 (.branch 79 (.leaf 1094244612) (.leaf 1072246424)) (.branch 81 (.leaf 1050702255) (.leaf 1029602240)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1008936749) (.leaf 988696386)) (.branch 85 (.leaf 968871977) (.leaf 949454565))) (.branch 88 (.branch 87 (.leaf 930435405) (.leaf 911805958)) (.branch 89 (.leaf 893557883) (.leaf 875683036)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 858173458) (.branch 92 (.leaf 841021378) (.leaf 824219202))) (.branch 95 (.branch 94 (.leaf 807759509) (.leaf 791635049)) (.branch 96 (.leaf 775838738) (.leaf 760363651)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 745203019) (.leaf 730350229)) (.branch 100 (.leaf 715798813) (.leaf 701542450))) (.branch 103 (.branch 102 (.leaf 687574959) (.leaf 673890299)) (.branch 104 (.leaf 660482559) (.leaf 647345964))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 634474864) (.leaf 621863732)) (.branch 108 (.leaf 609507166) (.leaf 597399880))) (.branch 111 (.branch 110 (.leaf 585536705) (.leaf 573912583)) (.branch 112 (.leaf 562522570) (.leaf 551361824)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 540425614) (.leaf 529709306)) (.branch 116 (.leaf 519208370) (.leaf 508918371))) (.branch 119 (.branch 118 (.leaf 498834972) (.leaf 488953927)) (.branch 120 (.leaf 479271082) (.leaf 469782372)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1218).prefactor = (2378123518475113/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1218).cutoff/(generalMeanRows 1218).c)).2 =
    (766954052386103/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1218).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1218).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1218).q*(generalMeanRows 1218).cutoff/2-2 = (407/102:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable408.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1218).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1218

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1218).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1218).criticalRate j.val*(generalMeanRows 1218).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1218).c*(generalMeanRows 1218).criticalPoint j.val)).2-
      (generalMeanRows 1218).J/2-(generalMeanRows 1218).error (generalMeanGrid j.val)+
      (generalMeanRows 1218).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1218).c)).2-
      (generalMeanRows 1218).J/2-(generalMeanRows 1218).error 4 := by
  have he : (generalMeanRows 1218).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1218) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1218)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1218

/-! Kernel-checked entropy margins for general spectral rectangle 1219. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1219
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6052642858) (.branch 2 (.leaf 5899266921) (.leaf 5751298079))) (.branch 5 (.branch 4 (.leaf 5608431588) (.leaf 5470387506)) (.branch 6 (.leaf 5336908223) (.leaf 5207756257)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5082712308) (.leaf 4961573520)) (.branch 10 (.leaf 4844151943) (.leaf 4730273146))) (.branch 13 (.branch 12 (.leaf 4619774988) (.leaf 4512506514)) (.branch 14 (.leaf 4408326963) (.leaf 4307104879))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4208717311) (.branch 17 (.leaf 4113049092) (.leaf 4019992190))) (.branch 20 (.branch 19 (.leaf 3929445121) (.leaf 3841312416)) (.branch 21 (.leaf 3755504144) (.leaf 3671935478)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3590526293) (.leaf 3511200817)) (.branch 25 (.leaf 3433887298) (.leaf 3358517709))) (.branch 28 (.branch 27 (.leaf 3285027480) (.leaf 3213355247)) (.branch 29 (.leaf 3143442631) (.leaf 3075234029)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3008676429) (.branch 32 (.leaf 2943719232) (.leaf 2880314100))) (.branch 35 (.branch 34 (.leaf 2818414803) (.leaf 2757977096)) (.branch 36 (.leaf 2698958585) (.leaf 2641318621)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2585018196) (.leaf 2530019840)) (.branch 40 (.leaf 2476287539) (.leaf 2423786653))) (.branch 43 (.branch 42 (.leaf 2372483832) (.leaf 2322346955)) (.branch 44 (.leaf 2273345059) (.leaf 2225448280))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2178627795) (.branch 47 (.leaf 2132855773) (.leaf 2088105321))) (.branch 50 (.branch 49 (.leaf 2044350442) (.leaf 2001565991)) (.branch 51 (.leaf 1959727638) (.leaf 1918811824)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1878795733) (.leaf 1839657255)) (.branch 55 (.leaf 1801374958) (.leaf 1763928057))) (.branch 58 (.branch 57 (.leaf 1727296387) (.leaf 1691460381)) (.branch 59 (.leaf 1656401039) (.leaf 1622099912))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1588539077) (.branch 62 (.leaf 1555701117) (.leaf 1523569104))) (.branch 65 (.branch 64 (.leaf 1492126577) (.leaf 1461357527)) (.branch 66 (.leaf 1431246383) (.leaf 1401777991)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1372937604) (.leaf 1344710866)) (.branch 70 (.leaf 1317083798) (.leaf 1290042788))) (.branch 73 (.branch 72 (.leaf 1263574575) (.leaf 1237666240)) (.branch 74 (.leaf 1212305194) (.leaf 1187479170))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1163176208) (.branch 77 (.leaf 1139384648) (.leaf 1116093123))) (.branch 80 (.branch 79 (.leaf 1093290545) (.leaf 1070966102)) (.branch 81 (.leaf 1049109246) (.leaf 1027709685)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1006757378) (.leaf 986242528)) (.branch 85 (.leaf 966155569) (.leaf 946487169))) (.branch 88 (.branch 87 (.leaf 927228214) (.leaf 908369810)) (.branch 89 (.leaf 889903269) (.leaf 871820110)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 854112051) (.branch 92 (.leaf 836771002) (.leaf 819789060))) (.branch 95 (.branch 94 (.leaf 803158508) (.leaf 786871805)) (.branch 96 (.leaf 770921584) (.leaf 755300648)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 740001964) (.leaf 725018657)) (.branch 100 (.leaf 710344012) (.leaf 695971464))) (.branch 103 (.branch 102 (.leaf 681894597) (.leaf 668107139)) (.branch 104 (.leaf 654602958) (.leaf 641376062))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 628420592) (.leaf 615730818)) (.branch 108 (.leaf 603301139) (.leaf 591126079))) (.branch 111 (.branch 110 (.leaf 579200281) (.leaf 567518508)) (.branch 112 (.leaf 556075638) (.leaf 544866663)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 533886683) (.leaf 523130905)) (.branch 116 (.leaf 512594644) (.leaf 502273314))) (.branch 119 (.branch 118 (.leaf 492162431) (.leaf 482257607)) (.branch 120 (.leaf 472554550) (.leaf 463049062)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1219).prefactor = (987987857652987/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1219).cutoff/(generalMeanRows 1219).c)).2 =
    (762292039280291/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1219).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1219).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1219).q*(generalMeanRows 1219).cutoff/2-2 = (407/102:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable408.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1219).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1219

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1219).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1219).criticalRate j.val*(generalMeanRows 1219).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1219).c*(generalMeanRows 1219).criticalPoint j.val)).2-
      (generalMeanRows 1219).J/2-(generalMeanRows 1219).error (generalMeanGrid j.val)+
      (generalMeanRows 1219).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1219).c)).2-
      (generalMeanRows 1219).J/2-(generalMeanRows 1219).error 4 := by
  have he : (generalMeanRows 1219).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1219) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1219)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1219

/-! Kernel-checked entropy margins for general spectral rectangle 1220. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1220
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6201561256) (.branch 2 (.leaf 6042440508) (.leaf 5888960240))) (.branch 5 (.branch 4 (.leaf 5740803063) (.leaf 5597677364)) (.branch 6 (.leaf 5459314726) (.leaf 5325467652)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5195907539) (.leaf 5070422879)) (.branch 10 (.leaf 4948817657) (.leaf 4830909918))) (.branch 13 (.branch 12 (.leaf 4716530483) (.leaf 4605521812)) (.branch 14 (.leaf 4497736965) (.leaf 4393038686))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4291298571) (.branch 17 (.leaf 4192396315) (.leaf 4096219042))) (.branch 20 (.branch 19 (.leaf 4002660694) (.leaf 3911621480)) (.branch 21 (.leaf 3823007377) (.leaf 3736729677)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3652704579) (.leaf 3570852814)) (.branch 25 (.leaf 3491099308) (.leaf 3413372872))) (.branch 28 (.branch 27 (.leaf 3337605923) (.leaf 3263734225)) (.branch 29 (.leaf 3191696656) (.leaf 3121434994)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3052893722) (.branch 32 (.leaf 2986019845) (.leaf 2920762729))) (.branch 35 (.branch 34 (.leaf 2857073947) (.leaf 2794907143)) (.branch 36 (.leaf 2734217900) (.leaf 2674963627)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2617103447) (.leaf 2560598095)) (.branch 40 (.leaf 2505409834) (.leaf 2451502356))) (.branch 43 (.branch 42 (.leaf 2398840717) (.leaf 2347391252)) (.branch 44 (.leaf 2297121512) (.leaf 2248000201))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2199997115) (.branch 47 (.leaf 2153083089) (.leaf 2107229943))) (.branch 50 (.branch 49 (.leaf 2062410438) (.leaf 2018598228)) (.branch 51 (.leaf 1975767822) (.leaf 1933894541)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1892954484) (.leaf 1852924494)) (.branch 55 (.leaf 1813782123) (.leaf 1775505605))) (.branch 58 (.branch 57 (.leaf 1738073828) (.leaf 1701466301)) (.branch 59 (.leaf 1665663138) (.leaf 1630645026))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1596393209) (.branch 62 (.leaf 1562889460) (.leaf 1530116067))) (.branch 65 (.branch 64 (.leaf 1498055810) (.leaf 1466691947)) (.branch 66 (.leaf 1436008191) (.leaf 1405988698)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1376618051) (.leaf 1347881243)) (.branch 70 (.leaf 1319763666) (.leaf 1292251096))) (.branch 73 (.branch 72 (.leaf 1265329681) (.leaf 1238985925)) (.branch 74 (.leaf 1213206685) (.leaf 1187979148))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1163290833) (.branch 77 (.leaf 1139129571) (.leaf 1115483499))) (.branch 80 (.branch 79 (.leaf 1092341051) (.leaf 1069690950)) (.branch 81 (.leaf 1047522195) (.leaf 1025824058)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1004586072) (.leaf 983798027)) (.branch 85 (.leaf 963449959) (.leaf 943532144))) (.branch 88 (.branch 87 (.leaf 924035095) (.leaf 904949548)) (.branch 89 (.leaf 886266462) (.leaf 867977012)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 850072578) (.branch 92 (.leaf 832544748) (.leaf 815385304))) (.branch 95 (.branch 94 (.leaf 798586221) (.leaf 782139663)) (.branch 96 (.leaf 766037974) (.leaf 750273677)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 734839467) (.leaf 719728207)) (.branch 100 (.leaf 704932925) (.leaf 690446809))) (.branch 103 (.branch 102 (.leaf 676263200) (.leaf 662375593)) (.branch 104 (.leaf 648777631) (.leaf 635463101))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 622425929) (.leaf 609660178)) (.branch 108 (.leaf 597160048) (.leaf 584919865))) (.branch 111 (.branch 110 (.leaf 572934085) (.leaf 561197287)) (.branch 112 (.leaf 549704170) (.leaf 538449553)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 527428369) (.leaf 516635663)) (.branch 116 (.leaf 506066590) (.leaf 495716413))) (.branch 119 (.branch 118 (.leaf 485580499) (.leaf 475654316)) (.branch 120 (.leaf 465933432) (.leaf 456413515)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1220).prefactor = (5130725965695637/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1220).cutoff/(generalMeanRows 1220).c)).2 =
    (75765165972379/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1220).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1220).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1220).q*(generalMeanRows 1220).c/2-2 = (101/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable286.value]
    have hcontinuation : (generalMeanRows 1220).q*(generalMeanRows 1220).cutoff/2-2 = (407/102:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable408.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1220).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1220

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1220).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1220).criticalRate j.val*(generalMeanRows 1220).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1220).c*(generalMeanRows 1220).criticalPoint j.val)).2-
      (generalMeanRows 1220).J/2-(generalMeanRows 1220).error (generalMeanGrid j.val)+
      (generalMeanRows 1220).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1220).c)).2-
      (generalMeanRows 1220).J/2-(generalMeanRows 1220).error 4 := by
  have he : (generalMeanRows 1220).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1220) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1220)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1220

/-! Kernel-checked entropy margins for general spectral rectangle 1221. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1221
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6441073363) (.branch 2 (.leaf 6275807171) (.leaf 6116399301))) (.branch 5 (.branch 4 (.leaf 5962520108) (.leaf 5813866714)) (.branch 6 (.leaf 5670160337) (.leaf 5531143920)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5396580032) (.leaf 5266248997)) (.branch 10 (.leaf 5139947229) (.leaf 5017485743))) (.branch 13 (.branch 12 (.leaf 4898688831) (.leaf 4783392865)) (.branch 14 (.leaf 4671445231) (.leaf 4562703374))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4457033927) (.branch 17 (.leaf 4354311941) (.leaf 4254420180))) (.branch 20 (.branch 19 (.leaf 4157248491) (.leaf 4062693228)) (.branch 21 (.leaf 3970656737) (.leaf 3881046884)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3793776630) (.leaf 3708763647)) (.branch 25 (.leaf 3625929960) (.leaf 3545201632))) (.branch 28 (.branch 27 (.leaf 3466508468) (.leaf 3389783751)) (.branch 29 (.leaf 3314964001) (.leaf 3241988745)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3170800323) (.branch 32 (.leaf 3101343692) (.leaf 3033566264))) (.branch 35 (.branch 34 (.leaf 2967417742) (.leaf 2902849977)) (.branch 36 (.leaf 2839816839) (.leaf 2778274092)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2718179278) (.leaf 2659491619)) (.branch 40 (.leaf 2602171917) (.leaf 2546182465))) (.branch 43 (.branch 42 (.leaf 2491486967) (.leaf 2438050458)) (.branch 44 (.leaf 2385839238) (.leaf 2334820800))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2284963775) (.branch 47 (.leaf 2236237869) (.leaf 2188613817))) (.branch 50 (.branch 49 (.leaf 2142063326) (.leaf 2096559034)) (.branch 51 (.leaf 2052074464) (.leaf 2008583984)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1966062770) (.leaf 1924486771)) (.branch 55 (.leaf 1883832673) (.leaf 1844077868))) (.branch 58 (.branch 57 (.leaf 1805200428) (.leaf 1767179073)) (.branch 59 (.leaf 1729993146) (.leaf 1693622591))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1658047925) (.branch 62 (.leaf 1623250219) (.leaf 1589211076))) (.branch 65 (.branch 64 (.leaf 1555912613) (.leaf 1523337438)) (.branch 66 (.leaf 1491468636) (.leaf 1460289752)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1429784774) (.leaf 1399938114)) (.branch 70 (.leaf 1370734601) (.leaf 1342159461))) (.branch 73 (.branch 72 (.leaf 1314198307) (.leaf 1286837122)) (.branch 74 (.leaf 1260062255) (.leaf 1233860399))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1208218590) (.branch 77 (.leaf 1183124190) (.leaf 1158564876))) (.branch 80 (.branch 79 (.leaf 1134528638) (.leaf 1111003761)) (.branch 81 (.leaf 1087978821) (.leaf 1065442675)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1043384452) (.leaf 1021793546)) (.branch 85 (.leaf 1000659610) (.leaf 979972544))) (.branch 88 (.branch 87 (.leaf 959722494) (.leaf 939899839)) (.branch 89 (.leaf 920495189) (.leaf 901499377)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 882903452) (.branch 92 (.leaf 864698675) (.leaf 846876511))) (.branch 95 (.branch 94 (.leaf 829428627) (.leaf 812346882)) (.branch 96 (.leaf 795623326) (.leaf 779250192)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 763219893) (.leaf 747525017)) (.branch 100 (.leaf 732158323) (.leaf 717112734))) (.branch 103 (.branch 102 (.leaf 702381336) (.leaf 687957373)) (.branch 104 (.leaf 673834241) (.leaf 660005486))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 646464802) (.leaf 633206022)) (.branch 108 (.leaf 620223121) (.leaf 607510207))) (.branch 111 (.branch 110 (.leaf 595061521) (.leaf 582871433)) (.branch 112 (.leaf 570934438) (.leaf 559245153)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 547798317) (.leaf 536588783)) (.branch 116 (.leaf 525611519) (.leaf 514861605))) (.branch 119 (.branch 118 (.leaf 504334229) (.leaf 494024684)) (.branch 120 (.leaf 483928368) (.leaf 474040779)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1221).prefactor = (5328881064914743/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1221).cutoff/(generalMeanRows 1221).c)).2 =
    (75765165972379/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1221).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1221).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1221).q*(generalMeanRows 1221).c/2-2 = (101/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable286.value]
    have hcontinuation : (generalMeanRows 1221).q*(generalMeanRows 1221).cutoff/2-2 = (407/102:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable408.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1221).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1221

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1221).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1221).criticalRate j.val*(generalMeanRows 1221).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1221).c*(generalMeanRows 1221).criticalPoint j.val)).2-
      (generalMeanRows 1221).J/2-(generalMeanRows 1221).error (generalMeanGrid j.val)+
      (generalMeanRows 1221).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1221).c)).2-
      (generalMeanRows 1221).J/2-(generalMeanRows 1221).error 4 := by
  have he : (generalMeanRows 1221).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1221) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1221)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1221

/-! Kernel-checked entropy margins for general spectral rectangle 1222. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1222
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5319217026) (.branch 2 (.leaf 5173925951) (.leaf 5033826387))) (.branch 5 (.branch 4 (.leaf 4898634091) (.leaf 4768087782)) (.branch 6 (.leaf 4641946803) (.leaf 4519989052)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4402009155) (.leaf 4287816847)) (.branch 10 (.leaf 4177235531) (.leaf 4070100997))) (.branch 13 (.branch 12 (.leaf 3966260281) (.leaf 3865570650)) (.branch 14 (.leaf 3767898683) (.leaf 3673119463))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3581115841) (.branch 17 (.leaf 3491777781) (.leaf 3405001768))) (.branch 20 (.branch 19 (.leaf 3320690274) (.leaf 3238751283)) (.branch 21 (.leaf 3159097852) (.leaf 3081647722)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3006322962) (.leaf 2933049646)) (.branch 25 (.leaf 2861757563) (.leaf 2792379950))) (.branch 28 (.branch 27 (.leaf 2724853248) (.leaf 2659116885)) (.branch 29 (.leaf 2595113074) (.leaf 2532786626)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2472084784) (.branch 32 (.leaf 2412957070) (.leaf 2355355140))) (.branch 35 (.branch 34 (.leaf 2299232657) (.leaf 2244545171)) (.branch 36 (.leaf 2191250006) (.leaf 2139306161)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2088674217) (.leaf 2039316248)) (.branch 40 (.leaf 1991195740) (.leaf 1944277520))) (.branch 43 (.branch 42 (.leaf 1898527684) (.leaf 1853913532)) (.branch 44 (.leaf 1810403513) (.leaf 1767967162))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1726575055) (.branch 47 (.leaf 1686198755) (.leaf 1646810770))) (.branch 50 (.branch 49 (.leaf 1608384510) (.leaf 1570894245)) (.branch 51 (.leaf 1534315068) (.leaf 1498622863)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1463794268) (.leaf 1429806647)) (.branch 55 (.leaf 1396638055) (.leaf 1364267219))) (.branch 58 (.branch 57 (.leaf 1332673504) (.leaf 1301836892)) (.branch 59 (.leaf 1271737956) (.leaf 1242357842))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1213678243) (.branch 62 (.leaf 1185681382) (.leaf 1158349991))) (.branch 65 (.branch 64 (.leaf 1131667294) (.leaf 1105616992)) (.branch 66 (.leaf 1080183239) (.leaf 1055350637)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1031104211) (.leaf 1007429402)) (.branch 70 (.leaf 984312048) (.leaf 961738374))) (.branch 73 (.branch 72 (.leaf 939694979) (.leaf 918168824)) (.branch 74 (.leaf 897147220) (.leaf 876617816))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 856568591) (.branch 77 (.leaf 836987842) (.leaf 817864173))) (.branch 80 (.branch 79 (.leaf 799186490) (.leaf 780943987)) (.branch 81 (.leaf 763126140) (.leaf 745722699)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 728723677) (.leaf 712119346)) (.branch 85 (.leaf 695900228) (.leaf 680057086))) (.branch 88 (.branch 87 (.leaf 664580919) (.leaf 649462955)) (.branch 89 (.leaf 634694646) (.leaf 620267657)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 606173866) (.branch 92 (.leaf 592405352) (.leaf 578954396))) (.branch 95 (.branch 94 (.leaf 565813469) (.leaf 552975231)) (.branch 96 (.leaf 540432524) (.leaf 528178369)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 516205958) (.leaf 504508653)) (.branch 100 (.leaf 493079978) (.leaf 481913616))) (.branch 103 (.branch 102 (.leaf 471003407) (.leaf 460343340)) (.branch 104 (.leaf 449927551) (.leaf 439750321))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 429806067) (.leaf 420089346)) (.branch 108 (.leaf 410594843) (.leaf 401317373))) (.branch 111 (.branch 110 (.leaf 392251878) (.leaf 383393420)) (.branch 112 (.leaf 374737181) (.leaf 366278459)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 358012664) (.leaf 349935317)) (.branch 116 (.leaf 342042047) (.leaf 334328586))) (.branch 119 (.branch 118 (.leaf 326790769) (.leaf 319424530)) (.branch 120 (.leaf 312225900) (.leaf 305191003)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1222).prefactor = (595136863151553/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1222).cutoff/(generalMeanRows 1222).c)).2 =
    (397495713458091/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1222).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1222).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1222).q*(generalMeanRows 1222).cutoff/2-2 = (97/22:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable409.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1222).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1222

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1222).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1222).criticalRate j.val*(generalMeanRows 1222).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1222).c*(generalMeanRows 1222).criticalPoint j.val)).2-
      (generalMeanRows 1222).J/2-(generalMeanRows 1222).error (generalMeanGrid j.val)+
      (generalMeanRows 1222).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1222).c)).2-
      (generalMeanRows 1222).J/2-(generalMeanRows 1222).error 4 := by
  have he : (generalMeanRows 1222).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1222) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1222)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1222

/-! Kernel-checked entropy margins for general spectral rectangle 1223. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1223
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6068129824) (.branch 2 (.leaf 5893146287) (.leaf 5724730421))) (.branch 5 (.branch 4 (.leaf 5562516164) (.leaf 5406166483)) (.branch 6 (.leaf 5255370508) (.leaf 5109840991)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4969312054) (.leaf 4833537181)) (.branch 10 (.leaf 4702287428) (.leaf 4575349826))) (.branch 13 (.branch 12 (.leaf 4452525952) (.leaf 4333630645)) (.branch 14 (.leaf 4218490859) (.leaf 4106944625))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3998840126) (.branch 17 (.leaf 3894034851) (.leaf 3792394843))) (.branch 20 (.branch 19 (.leaf 3693794012) (.leaf 3598113513)) (.branch 21 (.leaf 3505241188) (.leaf 3415071056)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3327502846) (.leaf 3242441579)) (.branch 25 (.leaf 3159797187) (.leaf 3079484155))) (.branch 28 (.branch 27 (.leaf 3001421212) (.leaf 2925531031)) (.branch 29 (.leaf 2851739968) (.leaf 2779977815)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2710177573) (.branch 32 (.leaf 2642275254) (.leaf 2576209685))) (.branch 35 (.branch 34 (.leaf 2511922337) (.leaf 2449357165)) (.branch 36 (.leaf 2388460458) (.leaf 2329180706)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2271468473) (.leaf 2215276278)) (.branch 40 (.leaf 2160558489) (.leaf 2107271224))) (.branch 43 (.branch 42 (.leaf 2055372256) (.leaf 2004820927)) (.branch 44 (.leaf 1955578068) (.leaf 1907605925))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1860868088) (.branch 47 (.leaf 1815329425) (.leaf 1770956023))) (.branch 50 (.branch 49 (.leaf 1727715131) (.leaf 1685575104)) (.branch 51 (.leaf 1644505356) (.leaf 1604476313)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1565459364) (.leaf 1527426828)) (.branch 55 (.leaf 1490351907) (.leaf 1454208653))) (.branch 58 (.branch 57 (.leaf 1418971932) (.leaf 1384617392)) (.branch 59 (.leaf 1351121433) (.leaf 1318461175))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1286614430) (.branch 62 (.leaf 1255559682) (.leaf 1225276051))) (.branch 65 (.branch 64 (.leaf 1195743280) (.leaf 1166941706)) (.branch 66 (.leaf 1138852239) (.leaf 1111456347)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1084736027) (.leaf 1058673796)) (.branch 70 (.leaf 1033252667) (.leaf 1008456135))) (.branch 73 (.branch 72 (.leaf 984268159) (.leaf 960673149)) (.branch 74 (.leaf 937655947) (.leaf 915201819))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 893296435) (.branch 77 (.leaf 871925860) (.leaf 851076540))) (.branch 80 (.branch 79 (.leaf 830735290) (.leaf 810889284)) (.branch 81 (.leaf 791526042) (.leaf 772633419)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 754199597) (.leaf 736213075)) (.branch 85 (.leaf 718662655) (.leaf 701537439))) (.branch 88 (.branch 87 (.leaf 684826817) (.leaf 668520460)) (.branch 89 (.leaf 652608307) (.leaf 637080565)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 621927694) (.branch 92 (.leaf 607140406) (.leaf 592709652))) (.branch 95 (.branch 94 (.leaf 578626619) (.leaf 564882722)) (.branch 96 (.leaf 551469598) (.leaf 538379098)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 525603284) (.leaf 513134422)) (.branch 100 (.leaf 500964974) (.leaf 489087596))) (.branch 103 (.branch 102 (.leaf 477495131) (.leaf 466180605)) (.branch 104 (.leaf 455137219) (.leaf 444358348))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 433837535) (.leaf 423568483)) (.branch 108 (.leaf 413545058) (.leaf 403761279))) (.branch 111 (.branch 110 (.leaf 394211313) (.leaf 384889477)) (.branch 112 (.leaf 375790228) (.leaf 366908163)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 358238013) (.leaf 349774642)) (.branch 116 (.leaf 341513040) (.leaf 333448324))) (.branch 119 (.branch 118 (.leaf 325575730) (.leaf 317890613)) (.branch 120 (.leaf 310388446) (.leaf 303064809)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1223).prefactor = (2874222915195057/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1223).cutoff/(generalMeanRows 1223).c)).2 =
    (712395068135669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1223).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1223).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1223).q*(generalMeanRows 1223).c/2-2 = (469/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable410.value]
    have hcontinuation : (generalMeanRows 1223).q*(generalMeanRows 1223).cutoff/2-2 = (407/102:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable408.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1223).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1223

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1223).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1223).criticalRate j.val*(generalMeanRows 1223).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1223).c*(generalMeanRows 1223).criticalPoint j.val)).2-
      (generalMeanRows 1223).J/2-(generalMeanRows 1223).error (generalMeanGrid j.val)+
      (generalMeanRows 1223).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1223).c)).2-
      (generalMeanRows 1223).J/2-(generalMeanRows 1223).error 4 := by
  have he : (generalMeanRows 1223).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1223) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1223)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1223

/-! Kernel-checked entropy margins for general spectral rectangle 1224. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1224
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6732520769) (.branch 2 (.leaf 6551216979) (.leaf 6376485808))) (.branch 5 (.branch 4 (.leaf 6207959343) (.leaf 6045299255)) (.branch 6 (.leaf 5888193858) (.leaf 5736355504)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5589518269) (.leaf 5447435897)) (.branch 10 (.leaf 5309879961) (.leaf 5176638230))) (.branch 13 (.branch 12 (.leaf 5047513204) (.leaf 4922320796)) (.branch 14 (.leaf 4800889164) (.leaf 4683057646))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4568675812) (.branch 17 (.leaf 4457602604) (.leaf 4349705565))) (.branch 20 (.branch 19 (.leaf 4244860138) (.leaf 4142949035)) (.branch 21 (.leaf 4043861664) (.leaf 3947493610)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3853746164) (.leaf 3762525895)) (.branch 25 (.leaf 3673744258) (.leaf 3587317244))) (.branch 28 (.branch 27 (.leaf 3503165052) (.leaf 3421211794)) (.branch 29 (.leaf 3341385228) (.leaf 3263616509)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3187839961) (.branch 32 (.leaf 3113992872) (.leaf 3042015305))) (.branch 35 (.branch 34 (.leaf 2971849918) (.leaf 2903441809)) (.branch 36 (.leaf 2836738363) (.leaf 2771689118)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2708245638) (.leaf 2646361397)) (.branch 40 (.leaf 2585991671) (.leaf 2527093439))) (.branch 43 (.branch 42 (.leaf 2469625288) (.leaf 2413547332)) (.branch 44 (.leaf 2358821127) (.leaf 2305409600))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2253276980) (.branch 47 (.leaf 2202388731) (.leaf 2152711497))) (.branch 50 (.branch 49 (.leaf 2104213040) (.leaf 2056862193)) (.branch 51 (.leaf 2010628808) (.leaf 1965483709)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1921398652) (.leaf 1878346283)) (.branch 55 (.leaf 1836300101) (.leaf 1795234418))) (.branch 58 (.branch 57 (.leaf 1755124332) (.leaf 1715945690)) (.branch 59 (.leaf 1677675059) (.leaf 1640289700))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1603767538) (.branch 62 (.leaf 1568087140) (.leaf 1533227688))) (.branch 65 (.branch 64 (.leaf 1499168956) (.leaf 1465891293)) (.branch 66 (.leaf 1433375595) (.leaf 1401603293)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1370556330) (.leaf 1340217142)) (.branch 70 (.leaf 1310568647) (.leaf 1281594223))) (.branch 73 (.branch 72 (.leaf 1253277695) (.leaf 1225603321)) (.branch 74 (.leaf 1198555776) (.leaf 1172120140))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1146281885) (.branch 77 (.leaf 1121026863) (.leaf 1096341292))) (.branch 80 (.branch 79 (.leaf 1072211749) (.leaf 1048625153)) (.branch 81 (.leaf 1025568760) (.leaf 1003030152)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 980997222) (.leaf 959458174)) (.branch 85 (.leaf 938401506) (.leaf 917816004))) (.branch 88 (.branch 87 (.leaf 897690737) (.leaf 878015042)) (.branch 89 (.leaf 858778524) (.leaf 839971043)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 821582709) (.branch 92 (.leaf 803603875) (.leaf 786025129))) (.branch 95 (.branch 94 (.leaf 768837291) (.leaf 752031402)) (.branch 96 (.leaf 735598721) (.leaf 719530719)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 703819071) (.leaf 688455655)) (.branch 100 (.leaf 673432542) (.leaf 658741993))) (.branch 103 (.branch 102 (.leaf 644376454) (.leaf 630328551)) (.branch 104 (.leaf 616591085) (.leaf 603157029))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 590019521) (.leaf 577171862)) (.branch 108 (.leaf 564607508) (.leaf 552320074))) (.branch 111 (.branch 110 (.leaf 540303321) (.leaf 528551158)) (.branch 112 (.leaf 517057635) (.leaf 505816943)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 494823406) (.leaf 484071483)) (.branch 116 (.leaf 473555759) (.leaf 463270946))) (.branch 119 (.branch 118 (.leaf 453211879) (.leaf 443373510)) (.branch 120 (.leaf 433750911) (.leaf 424339266)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1224).prefactor = (1470160590083471/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1224).cutoff/(generalMeanRows 1224).c)).2 =
    (92412815131949/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1224).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1224).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1224).q*(generalMeanRows 1224).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 1224).q*(generalMeanRows 1224).cutoff/2-2 = (407/102:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable408.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1224).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1224

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1224).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1224).criticalRate j.val*(generalMeanRows 1224).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1224).c*(generalMeanRows 1224).criticalPoint j.val)).2-
      (generalMeanRows 1224).J/2-(generalMeanRows 1224).error (generalMeanGrid j.val)+
      (generalMeanRows 1224).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1224).c)).2-
      (generalMeanRows 1224).J/2-(generalMeanRows 1224).error 4 := by
  have he : (generalMeanRows 1224).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1224) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1224)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1224

/-! Kernel-checked entropy margins for general spectral rectangle 1225. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1225
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5758153396) (.branch 2 (.leaf 5602653493) (.leaf 5452676791))) (.branch 5 (.branch 4 (.leaf 5307920661) (.leaf 5168106985)) (.branch 6 (.leaf 5032979650) (.leaf 4902302348)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4775856615) (.leaf 4653440105)) (.branch 10 (.leaf 4534865047) (.leaf 4419956881))) (.branch 13 (.branch 12 (.leaf 4308553037) (.leaf 4200501846)) (.branch 14 (.leaf 4095661568) (.leaf 3993899519))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3895091292) (.branch 17 (.leaf 3799120055) (.leaf 3705875917))) (.branch 20 (.branch 19 (.leaf 3615255364) (.leaf 3527160744)) (.branch 21 (.leaf 3441499804) (.leaf 3358185272)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3277134480) (.leaf 3198269017)) (.branch 25 (.leaf 3121514421) (.leaf 3046799892))) (.branch 28 (.branch 27 (.leaf 2974058037) (.leaf 2903224632)) (.branch 29 (.leaf 2834238409) (.leaf 2767040860)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2701576060) (.branch 32 (.leaf 2637790495) (.leaf 2575632922))) (.branch 35 (.branch 34 (.leaf 2515054220) (.leaf 2456007270)) (.branch 36 (.leaf 2398446836) (.leaf 2342329455)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2287613338) (.leaf 2234258280)) (.branch 40 (.leaf 2182225570) (.leaf 2131477916))) (.branch 43 (.branch 42 (.leaf 2081979371) (.leaf 2033695261)) (.branch 44 (.leaf 1986592127) (.leaf 1940637660))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1895800653) (.branch 47 (.leaf 1852050941) (.leaf 1809359358))) (.branch 50 (.branch 49 (.leaf 1767697694) (.leaf 1727038645)) (.branch 51 (.leaf 1687355781) (.leaf 1648623504)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1610817015) (.leaf 1573912281)) (.branch 55 (.leaf 1537886003) (.leaf 1502715585))) (.branch 58 (.branch 57 (.leaf 1468379111) (.leaf 1434855315)) (.branch 59 (.leaf 1402123555) (.leaf 1370163794))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1338956574) (.branch 62 (.leaf 1308482996) (.leaf 1278724700))) (.branch 65 (.branch 64 (.leaf 1249663845) (.leaf 1221283092)) (.branch 66 (.leaf 1193565584) (.leaf 1166494934)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1140055205) (.leaf 1114230897)) (.branch 70 (.leaf 1089006931) (.leaf 1064368637))) (.branch 73 (.branch 72 (.leaf 1040301739) (.leaf 1016792345)) (.branch 74 (.leaf 993826932) (.leaf 971392334))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 949475735) (.branch 77 (.leaf 928064653) (.leaf 907146935))) (.branch 80 (.branch 79 (.leaf 886710743) (.leaf 866744544)) (.branch 81 (.leaf 847237107) (.leaf 828177485)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 809555015) (.leaf 791359305)) (.branch 85 (.leaf 773580227) (.leaf 756207910))) (.branch 88 (.branch 87 (.leaf 739232733) (.leaf 722645315)) (.branch 89 (.leaf 706436514) (.leaf 690597414)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 675119322) (.branch 92 (.leaf 659993762) (.leaf 645212468))) (.branch 95 (.branch 94 (.leaf 630767378) (.leaf 616650630)) (.branch 96 (.leaf 602854554) (.leaf 589371670)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 576194681) (.leaf 563316467)) (.branch 100 (.leaf 550730083) (.leaf 538428752))) (.branch 103 (.branch 102 (.leaf 526405862) (.leaf 514654961)) (.branch 104 (.leaf 503169754) (.leaf 491944096))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 480971991) (.leaf 470247588)) (.branch 108 (.leaf 459765175) (.leaf 449519177))) (.branch 111 (.branch 110 (.leaf 439504154) (.leaf 429714792)) (.branch 112 (.leaf 420145908) (.leaf 410792440)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 401649446) (.leaf 392712103)) (.branch 116 (.leaf 383975700) (.leaf 375435638))) (.branch 119 (.branch 118 (.leaf 367087429) (.leaf 358926687)) (.branch 120 (.leaf 350949132) (.leaf 343150583)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1225).prefactor = (1017111479873937/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1225).cutoff/(generalMeanRows 1225).c)).2 =
    (799406445125299/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1225).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1225).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1225).q*(generalMeanRows 1225).c/2-2 = (1763/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable411.value]
    have hcontinuation : (generalMeanRows 1225).q*(generalMeanRows 1225).cutoff/2-2 = (97/22:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable409.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1225).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1225

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1225).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1225).criticalRate j.val*(generalMeanRows 1225).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1225).c*(generalMeanRows 1225).criticalPoint j.val)).2-
      (generalMeanRows 1225).J/2-(generalMeanRows 1225).error (generalMeanGrid j.val)+
      (generalMeanRows 1225).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1225).c)).2-
      (generalMeanRows 1225).J/2-(generalMeanRows 1225).error 4 := by
  have he : (generalMeanRows 1225).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1225) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1225)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1225

/-! Kernel-checked entropy margins for general spectral rectangle 1226. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1226
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5951125256) (.branch 2 (.leaf 5790414115) (.leaf 5635411274))) (.branch 5 (.branch 4 (.leaf 5485803960) (.leaf 5341304736)) (.branch 6 (.leaf 5201648905) (.leaf 5066592241)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4935908957) (.leaf 4809389926)) (.branch 10 (.leaf 4686841086) (.leaf 4568082025))) (.branch 13 (.branch 12 (.leaf 4452944726) (.leaf 4341272437)) (.branch 14 (.leaf 4232918667) (.leaf 4127746286))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4025626719) (.branch 17 (.leaf 3926439217) (.leaf 3830070207))) (.branch 20 (.branch 19 (.leaf 3736412705) (.leaf 3645365787)) (.branch 21 (.leaf 3556834108) (.leaf 3470727473)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3386960442) (.leaf 3305451976)) (.branch 25 (.leaf 3226125119) (.leaf 3148906697))) (.branch 28 (.branch 27 (.leaf 3073727058) (.leaf 3000519827)) (.branch 29 (.leaf 2929221682) (.leaf 2859772155)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2792113446) (.branch 32 (.leaf 2726190248) (.leaf 2661949600))) (.branch 35 (.branch 34 (.leaf 2599340736) (.leaf 2538314958)) (.branch 36 (.leaf 2478825512) (.leaf 2420827481)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2364277673) (.leaf 2309134537)) (.branch 40 (.leaf 2255358065) (.leaf 2202909716))) (.branch 43 (.branch 42 (.leaf 2151752335) (.leaf 2101850089)) (.branch 44 (.leaf 2053168397) (.leaf 2005673868))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1959334247) (.branch 47 (.leaf 1914118359) (.leaf 1869996062))) (.branch 50 (.branch 49 (.leaf 1826938198) (.leaf 1784916551)) (.branch 51 (.leaf 1743903803) (.leaf 1703873498)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1664800008) (.leaf 1626658493)) (.branch 55 (.leaf 1589424873) (.leaf 1553075796))) (.branch 58 (.branch 57 (.leaf 1517588611) (.leaf 1482941338)) (.branch 59 (.leaf 1449112645) (.leaf 1416081823))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1383828762) (.branch 62 (.leaf 1352333929) (.leaf 1321578349))) (.branch 65 (.branch 64 (.leaf 1291543583) (.leaf 1262211711)) (.branch 66 (.leaf 1233565312) (.leaf 1205587449)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1178261651) (.leaf 1151571897)) (.branch 70 (.leaf 1125502606) (.leaf 1100038613))) (.branch 73 (.branch 72 (.leaf 1075165167) (.leaf 1050867907)) (.branch 74 (.leaf 1027132858) (.leaf 1003946414))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 981295328) (.branch 77 (.leaf 959166701) (.leaf 937547972))) (.branch 80 (.branch 79 (.leaf 916426905) (.leaf 895791583)) (.branch 81 (.leaf 875630397) (.leaf 855932034)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 836685473) (.leaf 817879973)) (.branch 85 (.leaf 799505069) (.leaf 781550557))) (.branch 88 (.branch 87 (.leaf 764006494) (.leaf 746863185)) (.branch 89 (.leaf 730111182) (.leaf 713741269)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 697744463) (.branch 92 (.leaf 682112003) (.leaf 666835346))) (.branch 95 (.branch 94 (.leaf 651906161) (.leaf 637316321)) (.branch 96 (.leaf 623057900) (.leaf 609123167)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 595504580) (.leaf 582194781)) (.branch 100 (.leaf 569186592) (.leaf 556473009))) (.branch 103 (.branch 102 (.leaf 544047198) (.leaf 531902492)) (.branch 104 (.leaf 520032383) (.leaf 508430522))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 497090711) (.leaf 486006903)) (.branch 108 (.leaf 475173195) (.leaf 464583825))) (.branch 111 (.branch 110 (.leaf 454233170) (.leaf 444115739)) (.branch 112 (.leaf 434226175) (.leaf 424559246)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 415109845) (.leaf 405872986)) (.branch 116 (.leaf 396843802) (.leaf 388017539))) (.branch 119 (.branch 118 (.leaf 379389557) (.leaf 370955326)) (.branch 120 (.leaf 362710421) (.leaf 354650521)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1226).prefactor = (1051197736455863/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1226).cutoff/(generalMeanRows 1226).c)).2 =
    (799406445125299/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1226).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1226).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1226).q*(generalMeanRows 1226).c/2-2 = (1763/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable411.value]
    have hcontinuation : (generalMeanRows 1226).q*(generalMeanRows 1226).cutoff/2-2 = (97/22:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable409.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1226).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1226

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1226).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1226).criticalRate j.val*(generalMeanRows 1226).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1226).c*(generalMeanRows 1226).criticalPoint j.val)).2-
      (generalMeanRows 1226).J/2-(generalMeanRows 1226).error (generalMeanGrid j.val)+
      (generalMeanRows 1226).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1226).c)).2-
      (generalMeanRows 1226).J/2-(generalMeanRows 1226).error 4 := by
  have he : (generalMeanRows 1226).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1226) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1226)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1226

/-! Kernel-checked entropy margins for general spectral rectangle 1227. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1227
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6798709543) (.branch 2 (.leaf 6602658655) (.leaf 6413966160))) (.branch 5 (.branch 4 (.leaf 6232221924) (.leaf 6057048337)) (.branch 6 (.leaf 5888097101) (.leaf 5725046384)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5567598299) (.leaf 5415476648)) (.branch 10 (.leaf 5268424925) (.leaf 5126204519))) (.branch 13 (.branch 12 (.leaf 4988593118) (.leaf 4855383269)) (.branch 14 (.leaf 4726381091) (.leaf 4601405116))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4480285246) (.branch 17 (.leaf 4362861816) (.leaf 4248984738))) (.branch 20 (.branch 19 (.leaf 4138512742) (.leaf 4031312675)) (.branch 21 (.leaf 3927258877) (.leaf 3826232604)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3728121515) (.leaf 3632819196)) (.branch 25 (.leaf 3540224733) (.leaf 3450242318))) (.branch 28 (.branch 27 (.leaf 3362780894) (.leaf 3277753825)) (.branch 29 (.leaf 3195078599) (.leaf 3114676555)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3036472631) (.branch 32 (.leaf 2960395131) (.leaf 2886375519))) (.branch 35 (.branch 34 (.leaf 2814348219) (.leaf 2744250438)) (.branch 36 (.leaf 2676022000) (.leaf 2609605192)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2544944626) (.leaf 2481987104)) (.branch 40 (.leaf 2420681502) (.leaf 2360978653))) (.branch 43 (.branch 42 (.leaf 2302831247) (.leaf 2246193731)) (.branch 44 (.leaf 2191022219) (.leaf 2137274413))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2084909518) (.branch 47 (.leaf 2033888174) (.leaf 1984172383))) (.branch 50 (.branch 49 (.leaf 1935725452) (.leaf 1888511926)) (.branch 51 (.leaf 1842497537) (.leaf 1797649149)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1753934709) (.leaf 1711323201)) (.branch 55 (.leaf 1669784600) (.leaf 1629289836))) (.branch 58 (.branch 57 (.leaf 1589810748) (.leaf 1551320052)) (.branch 59 (.leaf 1513791307) (.leaf 1477198878))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1441517907) (.branch 62 (.leaf 1406724285) (.leaf 1372794621))) (.branch 65 (.branch 64 (.leaf 1339706217) (.leaf 1307437042)) (.branch 66 (.leaf 1275965711) (.leaf 1245271458)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1215334113) (.leaf 1186134089)) (.branch 70 (.leaf 1157652353) (.leaf 1129870412))) (.branch 73 (.branch 72 (.leaf 1102770296) (.leaf 1076334537)) (.branch 74 (.leaf 1050546152) (.leaf 1025388632))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1000845923) (.branch 77 (.leaf 976902412) (.leaf 953542913))) (.branch 80 (.branch 79 (.leaf 930752655) (.leaf 908517265)) (.branch 81 (.leaf 886822763) (.leaf 865655540)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 845002356) (.leaf 824850325)) (.branch 85 (.leaf 805186901) (.leaf 785999875))) (.branch 88 (.branch 87 (.leaf 767277358) (.leaf 749007777)) (.branch 89 (.leaf 731179861) (.leaf 713782638)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 696805420) (.branch 92 (.leaf 680237798) (.leaf 664069637))) (.branch 95 (.branch 94 (.leaf 648291060) (.leaf 632892450)) (.branch 96 (.leaf 617864437) (.leaf 603197890)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 588883917) (.leaf 574913851)) (.branch 100 (.leaf 561279248) (.leaf 547971880))) (.branch 103 (.branch 102 (.leaf 534983727) (.leaf 522306974)) (.branch 104 (.leaf 509934007) (.leaf 497857401))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 486069921) (.leaf 474564515)) (.branch 108 (.leaf 463334308) (.leaf 452372599))) (.branch 111 (.branch 110 (.leaf 441672854) (.leaf 431228704)) (.branch 112 (.leaf 421033940) (.leaf 411082509)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 401368506) (.leaf 391886177)) (.branch 116 (.leaf 382629910) (.leaf 373594232))) (.branch 119 (.branch 118 (.leaf 364773807) (.leaf 356163432)) (.branch 120 (.leaf 347758032) (.leaf 339552658)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1227).prefactor = (257621472562503/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1227).cutoff/(generalMeanRows 1227).c)).2 =
    (712395068135669/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1227).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1227).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1227).q*(generalMeanRows 1227).c/2-2 = (469/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable410.value]
    have hcontinuation : (generalMeanRows 1227).q*(generalMeanRows 1227).cutoff/2-2 = (407/102:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable408.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1227).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1227

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1227).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1227).criticalRate j.val*(generalMeanRows 1227).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1227).c*(generalMeanRows 1227).criticalPoint j.val)).2-
      (generalMeanRows 1227).J/2-(generalMeanRows 1227).error (generalMeanGrid j.val)+
      (generalMeanRows 1227).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1227).c)).2-
      (generalMeanRows 1227).J/2-(generalMeanRows 1227).error 4 := by
  have he : (generalMeanRows 1227).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1227) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1227)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1227

/-! Kernel-checked entropy margins for general spectral rectangle 1228. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1228
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7353468886) (.branch 2 (.leaf 7148431757) (.leaf 6950956855))) (.branch 5 (.branch 4 (.leaf 6760621993) (.leaf 6577038694)) (.branch 6 (.leaf 6399848850) (.leaf 6228721764)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6063351520) (.leaf 5903454651)) (.branch 10 (.leaf 5748768048) (.leaf 5599047103))) (.branch 13 (.branch 12 (.leaf 5454064045) (.leaf 5313606447)) (.branch 14 (.leaf 5177475886) (.leaf 5045486745))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4917465122) (.branch 17 (.leaf 4793247866) (.leaf 4672681684))) (.branch 20 (.branch 19 (.leaf 4555622354) (.leaf 4441934002)) (.branch 21 (.leaf 4331488448) (.leaf 4224164618)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4119848005) (.leaf 4018430179)) (.branch 25 (.leaf 3919808344) (.leaf 3823884933))) (.branch 28 (.branch 27 (.leaf 3730567239) (.leaf 3639767076)) (.branch 29 (.leaf 3551400469) (.leaf 3465387375)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3381651422) (.branch 32 (.leaf 3300119673) (.leaf 3220722402))) (.branch 35 (.branch 34 (.leaf 3143392904) (.leaf 3068067301)) (.branch 36 (.leaf 2994684374) (.leaf 2923185411)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2853514055) (.leaf 2785616175)) (.branch 40 (.leaf 2719439740) (.leaf 2654934703))) (.branch 43 (.branch 42 (.leaf 2592052899) (.leaf 2530747939)) (.branch 44 (.leaf 2470975125) (.leaf 2412691359))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2355855065) (.branch 47 (.leaf 2300426117) (.leaf 2246365765))) (.branch 50 (.branch 49 (.leaf 2193636574) (.leaf 2142202360)) (.branch 51 (.leaf 2092028136) (.leaf 2043080056)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1995325367) (.leaf 1948732360)) (.branch 55 (.leaf 1903270328) (.leaf 1858909519))) (.branch 58 (.branch 57 (.leaf 1815621104) (.leaf 1773377136)) (.branch 59 (.leaf 1732150513) (.leaf 1691914947))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1652644936) (.branch 62 (.leaf 1614315725) (.leaf 1576903289))) (.branch 65 (.branch 64 (.leaf 1540384298) (.leaf 1504736094)) (.branch 66 (.leaf 1469936667) (.leaf 1435964635)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1402799216) (.leaf 1370420211)) (.branch 70 (.leaf 1338807985) (.leaf 1307943444))) (.branch 73 (.branch 72 (.leaf 1277808021) (.leaf 1248383656)) (.branch 74 (.leaf 1219652781) (.leaf 1191598303))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1164203588) (.branch 77 (.leaf 1137452450) (.leaf 1111329133))) (.branch 80 (.branch 79 (.leaf 1085818298) (.leaf 1060905014)) (.branch 81 (.leaf 1036574740) (.leaf 1012813317)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 989606957) (.leaf 966942228)) (.branch 85 (.leaf 944806046) (.leaf 923185667))) (.branch 88 (.branch 87 (.leaf 902068672) (.leaf 881442960)) (.branch 89 (.leaf 861296743) (.leaf 841618528)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 822397116) (.branch 92 (.leaf 803621593) (.leaf 785281318))) (.branch 95 (.branch 94 (.leaf 767365918) (.leaf 749865282)) (.branch 96 (.leaf 732769550) (.leaf 716069109)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 699754587) (.leaf 683816842)) (.branch 100 (.leaf 668246961) (.leaf 653036250))) (.branch 103 (.branch 102 (.leaf 638176230) (.leaf 623658631)) (.branch 104 (.leaf 609475386) (.leaf 595618625))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 582080674) (.leaf 568854042)) (.branch 108 (.leaf 555931424) (.leaf 543305690))) (.branch 111 (.branch 110 (.leaf 530969887) (.leaf 518917228)) (.branch 112 (.leaf 507141091) (.leaf 495635014)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 484392691) (.leaf 473407969)) (.branch 116 (.leaf 462674842) (.leaf 452187448))) (.branch 119 (.branch 118 (.leaf 441940068) (.leaf 431927117)) (.branch 120 (.leaf 422143147) (.leaf 412582838)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1228).prefactor = (267571138320899/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1228).cutoff/(generalMeanRows 1228).c)).2 =
    (725758295947837/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1228).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1228).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1228).q*(generalMeanRows 1228).cutoff/2-2 = (407/102:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable408.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1228).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1228

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1228).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1228).criticalRate j.val*(generalMeanRows 1228).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1228).c*(generalMeanRows 1228).criticalPoint j.val)).2-
      (generalMeanRows 1228).J/2-(generalMeanRows 1228).error (generalMeanGrid j.val)+
      (generalMeanRows 1228).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1228).c)).2-
      (generalMeanRows 1228).J/2-(generalMeanRows 1228).error 4 := by
  have he : (generalMeanRows 1228).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1228) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1228)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1228

/-! Kernel-checked entropy margins for general spectral rectangle 1229. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1229
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 8077734657) (.branch 2 (.leaf 7867907223) (.leaf 7665559018))) (.branch 5 (.branch 4 (.leaf 7470269816) (.leaf 7281653430)) (.branch 6 (.leaf 7099354315) (.leaf 6923044562)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6752421227) (.leaf 6587203958)) (.branch 10 (.leaf 6427132876) (.leaf 6271966685))) (.branch 13 (.branch 12 (.leaf 6121480989) (.leaf 5975466771)) (.branch 14 (.leaf 5833729040) (.leaf 5696085612))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5562366014) (.branch 17 (.leaf 5432410490) (.leaf 5306069120))) (.branch 20 (.branch 19 (.leaf 5183201006) (.leaf 5063673549)) (.branch 21 (.leaf 4947361790) (.leaf 4834147812)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4723920197) (.leaf 4616573537)) (.branch 25 (.leaf 4512007983) (.leaf 4410128839))) (.branch 28 (.branch 27 (.leaf 4310846191) (.leaf 4214074565)) (.branch 29 (.leaf 4119732621) (.leaf 4027742870)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3938031410) (.branch 32 (.leaf 3850527692) (.leaf 3765164305))) (.branch 35 (.branch 34 (.leaf 3681876768) (.leaf 3600603353)) (.branch 36 (.leaf 3521284914) (.leaf 3443864727)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3368288354) (.leaf 3294503502)) (.branch 40 (.leaf 3222459906) (.leaf 3152109212))) (.branch 43 (.branch 42 (.leaf 3083404874) (.leaf 3016302057)) (.branch 44 (.leaf 2950757542) (.leaf 2886729648))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2824178150) (.branch 47 (.leaf 2763064207) (.leaf 2703350293))) (.branch 50 (.branch 49 (.leaf 2645000138) (.leaf 2587978662)) (.branch 51 (.leaf 2532251924) (.leaf 2477787072)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2424552288) (.leaf 2372516750)) (.branch 55 (.leaf 2321650581) (.leaf 2271924818))) (.branch 58 (.branch 57 (.leaf 2223311366) (.leaf 2175782966)) (.branch 59 (.leaf 2129313162) (.leaf 2083876269))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2039447340) (.branch 62 (.leaf 1996002142) (.leaf 1953517125))) (.branch 65 (.branch 64 (.leaf 1911969399) (.leaf 1871336712)) (.branch 66 (.leaf 1831597422) (.leaf 1792730477)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1754715398) (.leaf 1717532253)) (.branch 70 (.leaf 1681161644) (.leaf 1645584687))) (.branch 73 (.branch 72 (.leaf 1610782992) (.leaf 1576738652)) (.branch 74 (.leaf 1543434222) (.leaf 1510852710))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1478977557) (.branch 77 (.leaf 1447792628) (.leaf 1417282196))) (.branch 80 (.branch 79 (.leaf 1387430929) (.leaf 1358223881)) (.branch 81 (.leaf 1329646480) (.leaf 1301684512)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1274324117) (.leaf 1247551774)) (.branch 85 (.leaf 1221354296) (.leaf 1195718814))) (.branch 88 (.branch 87 (.leaf 1170632773) (.leaf 1146083921)) (.branch 89 (.leaf 1122060300) (.leaf 1098550242)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1075542355) (.branch 92 (.leaf 1053025518) (.leaf 1030988876))) (.branch 95 (.branch 94 (.leaf 1009421829) (.leaf 988314028)) (.branch 96 (.leaf 967655367) (.leaf 947435976)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 927646216) (.leaf 908276673)) (.branch 100 (.leaf 889318151) (.leaf 870761667))) (.branch 103 (.branch 102 (.leaf 852598445) (.leaf 834819913)) (.branch 104 (.leaf 817417695) (.leaf 800383606))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 783709650) (.leaf 767388012)) (.branch 108 (.leaf 751411057) (.leaf 735771320))) (.branch 111 (.branch 110 (.leaf 720461508) (.leaf 705474494)) (.branch 112 (.leaf 690803308) (.leaf 676441141)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 662381334) (.leaf 648617381)) (.branch 116 (.leaf 635142918) (.leaf 621951726))) (.branch 119 (.branch 118 (.leaf 609037725) (.leaf 596394968)) (.branch 120 (.leaf 584017643) (.leaf 571900066)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1229).prefactor = (1693577282948463/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1229).cutoff/(generalMeanRows 1229).c)).2 =
    (150606542773499/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1229).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1229).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1229).q*(generalMeanRows 1229).cutoff/2-2 = (407/102:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable408.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1229).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1229

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1229).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1229).criticalRate j.val*(generalMeanRows 1229).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1229).c*(generalMeanRows 1229).criticalPoint j.val)).2-
      (generalMeanRows 1229).J/2-(generalMeanRows 1229).error (generalMeanGrid j.val)+
      (generalMeanRows 1229).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1229).c)).2-
      (generalMeanRows 1229).J/2-(generalMeanRows 1229).error 4 := by
  have he : (generalMeanRows 1229).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1229) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1229)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1229

/-! Kernel-checked entropy margins for general spectral rectangle 1230. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1230
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5983856256) (.branch 2 (.leaf 5809310271) (.leaf 5641231412))) (.branch 5 (.branch 4 (.leaf 5479266346) (.leaf 5323089872)) (.branch 6 (.leaf 5172402076) (.leaf 5026925822)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4886404525) (.leaf 4750600184)) (.branch 10 (.leaf 4619291628) (.leaf 4492272954))) (.branch 13 (.branch 12 (.leaf 4369352142) (.leaf 4250349811)) (.branch 14 (.leaf 4135098103) (.leaf 4023439696))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3915226903) (.branch 17 (.leaf 3810320873) (.leaf 3708590866))) (.branch 20 (.branch 19 (.leaf 3609913605) (.leaf 3514172683)) (.branch 21 (.leaf 3421258034) (.leaf 3331065454)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3243496160) (.leaf 3158456398)) (.branch 25 (.leaf 3075857081) (.leaf 2995613462))) (.branch 28 (.branch 27 (.leaf 2917644837) (.leaf 2841874270)) (.branch 29 (.leaf 2768228346) (.leaf 2696636943)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2627033021) (.branch 32 (.leaf 2559352434) (.leaf 2493533752))) (.branch 35 (.branch 34 (.leaf 2429518099) (.leaf 2367249004)) (.branch 36 (.leaf 2306672265) (.leaf 2247735819)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2190389627) (.leaf 2134585563)) (.branch 40 (.leaf 2080277315) (.leaf 2027420291))) (.branch 43 (.branch 42 (.leaf 1975971529) (.leaf 1925889619)) (.branch 44 (.leaf 1877134628) (.leaf 1829668026))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1783452620) (.branch 47 (.leaf 1738452496) (.leaf 1694632960))) (.branch 50 (.branch 49 (.leaf 1651960479) (.leaf 1610402636)) (.branch 51 (.leaf 1569928080) (.leaf 1530506479)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1492108481) (.leaf 1454705669)) (.branch 55 (.leaf 1418270529) (.leaf 1382776410))) (.branch 58 (.branch 57 (.leaf 1348197490) (.leaf 1314508747)) (.branch 59 (.leaf 1281685926) (.leaf 1249705510))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1218544695) (.branch 62 (.leaf 1188181361) (.leaf 1158594049))) (.branch 65 (.branch 64 (.leaf 1129761935) (.leaf 1101664813)) (.branch 66 (.leaf 1074283065) (.leaf 1047597648)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1021590071) (.leaf 996242377)) (.branch 70 (.leaf 971537124) (.leaf 947457368))) (.branch 73 (.branch 72 (.leaf 923986649) (.leaf 901108972)) (.branch 74 (.leaf 878808794) (.leaf 857071008))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 835880929) (.branch 77 (.leaf 815224284) (.leaf 795087194))) (.branch 80 (.branch 79 (.leaf 775456164) (.leaf 756318074)) (.branch 81 (.leaf 737660161) (.leaf 719470015)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 701735562) (.leaf 684445059)) (.branch 85 (.leaf 667587081) (.leaf 651150513))) (.branch 88 (.branch 87 (.leaf 635124538) (.leaf 619498635)) (.branch 89 (.leaf 604262560) (.leaf 589406347)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 574920296) (.branch 92 (.leaf 560794964) (.leaf 547021163))) (.branch 95 (.branch 94 (.leaf 533589945) (.leaf 520492600)) (.branch 96 (.leaf 507720650) (.leaf 495265840)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 483120132) (.leaf 471275699)) (.branch 100 (.leaf 459724919) (.leaf 448460372))) (.branch 103 (.branch 102 (.leaf 437474830) (.leaf 426761254)) (.branch 104 (.leaf 416312789) (.leaf 406122757))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 396184655) (.leaf 386492148)) (.branch 108 (.leaf 377039065) (.leaf 367819395))) (.branch 111 (.branch 110 (.leaf 358827282) (.leaf 350057022)) (.branch 112 (.leaf 341503055) (.leaf 333159968)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 325022484) (.leaf 317085463)) (.branch 116 (.leaf 309343896) (.leaf 301792902))) (.branch 119 (.branch 118 (.leaf 294427726) (.leaf 287243734)) (.branch 120 (.leaf 280236410) (.leaf 273401352)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1230).prefactor = (4533065919289/781250000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1230).cutoff/(generalMeanRows 1230).c)).2 =
    (192225747707971/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1230).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1230).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1230).q*(generalMeanRows 1230).cutoff/2-2 = (97/22:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable409.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1230).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1230

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1230).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1230).criticalRate j.val*(generalMeanRows 1230).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1230).c*(generalMeanRows 1230).criticalPoint j.val)).2-
      (generalMeanRows 1230).J/2-(generalMeanRows 1230).error (generalMeanGrid j.val)+
      (generalMeanRows 1230).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1230).c)).2-
      (generalMeanRows 1230).J/2-(generalMeanRows 1230).error 4 := by
  have he : (generalMeanRows 1230).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1230) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1230)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1230

/-! Kernel-checked entropy margins for general spectral rectangle 1231. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1231
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6207074247) (.branch 2 (.leaf 6050568003) (.leaf 5899453327))) (.branch 5 (.branch 4 (.leaf 5753432135) (.leaf 5612230767)) (.branch 6 (.leaf 5475597497) (.leaf 5343300327)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5215125035) (.leaf 5090873450)) (.branch 10 (.leaf 4970361912) (.leaf 4853419907))) (.branch 13 (.branch 12 (.leaf 4739888845) (.leaf 4629620970)) (.branch 14 (.leaf 4522478391) (.leaf 4418332205))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4317061718) (.branch 17 (.leaf 4218553737) (.leaf 4122701945))) (.branch 20 (.branch 19 (.leaf 4029406326) (.leaf 3938572653)) (.branch 21 (.leaf 3850112026) (.leaf 3763940450)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3679978457) (.leaf 3598150762)) (.branch 25 (.leaf 3518385952) (.leaf 3440616197))) (.branch 28 (.branch 27 (.leaf 3364776999) (.leaf 3290806951)) (.branch 29 (.leaf 3218647529) (.leaf 3148242888)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3079539690) (.branch 32 (.leaf 3012486936) (.leaf 2947035819))) (.branch 35 (.branch 34 (.leaf 2883139585) (.leaf 2820753404)) (.branch 36 (.leaf 2759834259) (.leaf 2700340832)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2642233414) (.leaf 2585473803)) (.branch 40 (.leaf 2530025230) (.leaf 2475852276))) (.branch 43 (.branch 42 (.leaf 2422920798) (.leaf 2371197866)) (.branch 44 (.leaf 2320651699) (.leaf 2271251607))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2222967937) (.branch 47 (.leaf 2175772024) (.leaf 2129636143))) (.branch 50 (.branch 49 (.leaf 2084533464) (.leaf 2040438016)) (.branch 51 (.leaf 1997324641) (.leaf 1955168965)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1913947361) (.leaf 1873636918)) (.branch 55 (.leaf 1834215410) (.leaf 1795661271))) (.branch 58 (.branch 57 (.leaf 1757953563) (.leaf 1721071959)) (.branch 59 (.leaf 1684996712) (.leaf 1649708635))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1615189083) (.branch 62 (.leaf 1581419929) (.leaf 1548383546))) (.branch 65 (.branch 64 (.leaf 1516062790) (.leaf 1484440984)) (.branch 66 (.leaf 1453501897) (.leaf 1423229734)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1393609118) (.leaf 1364625077)) (.branch 70 (.leaf 1336263029) (.leaf 1308508774))) (.branch 73 (.branch 72 (.leaf 1281348474) (.leaf 1254768648)) (.branch 74 (.leaf 1228756159) (.leaf 1203298201))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1178382291) (.branch 77 (.leaf 1153996258) (.leaf 1130128235))) (.branch 80 (.branch 79 (.leaf 1106766649) (.leaf 1083900210)) (.branch 81 (.leaf 1061517909) (.leaf 1039609001)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1018163006) (.leaf 997169694)) (.branch 85 (.leaf 976619085) (.leaf 956501435))) (.branch 88 (.branch 87 (.leaf 936807235) (.leaf 917527201)) (.branch 89 (.leaf 898652270) (.leaf 880173592)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 862082526) (.branch 92 (.leaf 844370633) (.leaf 827029671))) (.branch 95 (.branch 94 (.leaf 810051592) (.leaf 793428532)) (.branch 96 (.leaf 777152810) (.leaf 761216922)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 745613539) (.leaf 730335496)) (.branch 100 (.leaf 715375794) (.leaf 700727595))) (.branch 103 (.branch 102 (.leaf 686384215) (.leaf 672339121)) (.branch 104 (.leaf 658585929) (.leaf 645118399))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 631930432) (.leaf 619016064)) (.branch 108 (.leaf 606369468) (.leaf 593984944))) (.branch 111 (.branch 110 (.leaf 581856923) (.leaf 569979955)) (.branch 112 (.leaf 558348717) (.leaf 546957999)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 535802710) (.leaf 524877870)) (.branch 116 (.leaf 514178609) (.leaf 503700163))) (.branch 119 (.branch 118 (.leaf 493437876) (.leaf 483387191)) (.branch 120 (.leaf 473543653) (.leaf 463902902)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1231).prefactor = (2526622990335011/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1231).cutoff/(generalMeanRows 1231).c)).2 =
    (81171509862407/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1231).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1231).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1231).q*(generalMeanRows 1231).c/2-2 = (161/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable110.value]
    have hcontinuation : (generalMeanRows 1231).q*(generalMeanRows 1231).cutoff/2-2 = (1092/253:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable412.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1231).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1231

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1231).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1231).criticalRate j.val*(generalMeanRows 1231).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1231).c*(generalMeanRows 1231).criticalPoint j.val)).2-
      (generalMeanRows 1231).J/2-(generalMeanRows 1231).error (generalMeanGrid j.val)+
      (generalMeanRows 1231).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1231).c)).2-
      (generalMeanRows 1231).J/2-(generalMeanRows 1231).error 4 := by
  have he : (generalMeanRows 1231).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1231) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1231)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1231

/-! Kernel-checked entropy margins for general spectral rectangle 1232. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1232
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6285296877) (.branch 2 (.leaf 6122926490) (.leaf 5966214195))) (.branch 5 (.branch 4 (.leaf 5814848058) (.leaf 5668541574)) (.branch 6 (.leaf 5527031072) (.leaf 5390073433)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5257444057) (.leaf 5128935073)) (.branch 10 (.leaf 5004353739) (.leaf 4883521021))) (.branch 13 (.branch 12 (.leaf 4766270325) (.leaf 4652446367)) (.branch 14 (.leaf 4541904160) (.leaf 4434508106))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4330131184) (.branch 17 (.leaf 4228654218) (.leaf 4129965219))) (.branch 20 (.branch 19 (.leaf 4033958792) (.leaf 3940535604)) (.branch 21 (.leaf 3849601900) (.leaf 3761069066)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3674853233) (.leaf 3590874920)) (.branch 25 (.leaf 3509058709) (.leaf 3429332948))) (.branch 28 (.branch 27 (.leaf 3351629482) (.leaf 3275883409)) (.branch 29 (.leaf 3202032855) (.leaf 3130018770)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3059784740) (.branch 32 (.leaf 2991276819) (.leaf 2924443370))) (.branch 35 (.branch 34 (.leaf 2859234921) (.leaf 2795604031)) (.branch 36 (.leaf 2733505174) (.leaf 2672894621)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2613730337) (.leaf 2555971891)) (.branch 40 (.leaf 2499580359) (.leaf 2444518251))) (.branch 43 (.branch 42 (.leaf 2390749428) (.leaf 2338239038)) (.branch 44 (.leaf 2286953443) (.leaf 2236860166))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2187927830) (.branch 47 (.leaf 2140126106) (.leaf 2093425662))) (.branch 50 (.branch 49 (.leaf 2047798120) (.leaf 2003216011)) (.branch 51 (.leaf 1959652736) (.leaf 1917082525)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1875480405) (.leaf 1834822163)) (.branch 55 (.leaf 1795084317) (.leaf 1756244088))) (.branch 58 (.branch 57 (.leaf 1718279366) (.leaf 1681168688)) (.branch 59 (.leaf 1644891213) (.leaf 1609426698))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1574755472) (.branch 62 (.leaf 1540858422) (.leaf 1507716964))) (.branch 65 (.branch 64 (.leaf 1475313032) (.leaf 1443629055)) (.branch 66 (.leaf 1412647939) (.leaf 1382353057)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1352728224) (.leaf 1323757689)) (.branch 70 (.leaf 1295426118) (.leaf 1267718581))) (.branch 73 (.branch 72 (.leaf 1240620539) (.leaf 1214117829)) (.branch 74 (.leaf 1188196656) (.leaf 1162843580))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1138045503) (.branch 77 (.leaf 1113789663) (.leaf 1090063617))) (.branch 80 (.branch 79 (.leaf 1066855240) (.leaf 1044152706)) (.branch 81 (.leaf 1021944488) (.leaf 1000219344)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 978966308) (.leaf 958174688)) (.branch 85 (.leaf 937834051) (.leaf 917934220))) (.branch 88 (.branch 87 (.leaf 898465266) (.leaf 879417500)) (.branch 89 (.leaf 860781468) (.leaf 842547943)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 824707919) (.branch 92 (.leaf 807252606) (.leaf 790173423))) (.branch 95 (.branch 94 (.leaf 773461995) (.leaf 757110142)) (.branch 96 (.leaf 741109880) (.leaf 725453412)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 710133124) (.leaf 695141582)) (.branch 100 (.leaf 680471522) (.leaf 666115854))) (.branch 103 (.branch 102 (.leaf 652067650) (.leaf 638320142)) (.branch 104 (.leaf 624866722) (.leaf 611700931))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 598816462) (.leaf 586207149)) (.branch 108 (.leaf 573866972) (.leaf 561790045))) (.branch 111 (.branch 110 (.leaf 549970618) (.leaf 538403074)) (.branch 112 (.leaf 527081920) (.leaf 516001791)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 505157442) (.leaf 494543747)) (.branch 116 (.leaf 484155697) (.leaf 473988393))) (.branch 119 (.branch 118 (.leaf 464037050) (.leaf 454296989)) (.branch 120 (.leaf 444763635) (.leaf 435432518)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1232).prefactor = (5255798994837049/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1232).cutoff/(generalMeanRows 1232).c)).2 =
    (100333157888019/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1232).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1232).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1232).q*(generalMeanRows 1232).c/2-2 = (1661/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable413.value]
    have hcontinuation : (generalMeanRows 1232).q*(generalMeanRows 1232).cutoff/2-2 = (1092/253:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable412.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1232).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1232

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1232).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1232).criticalRate j.val*(generalMeanRows 1232).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1232).c*(generalMeanRows 1232).criticalPoint j.val)).2-
      (generalMeanRows 1232).J/2-(generalMeanRows 1232).error (generalMeanGrid j.val)+
      (generalMeanRows 1232).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1232).c)).2-
      (generalMeanRows 1232).J/2-(generalMeanRows 1232).error 4 := by
  have he : (generalMeanRows 1232).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1232) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1232)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1232

/-! Kernel-checked entropy margins for general spectral rectangle 1233. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1233
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6537235103) (.branch 2 (.leaf 6368356303) (.leaf 6205362392))) (.branch 5 (.branch 4 (.leaf 6047928934) (.leaf 5895757938)) (.branch 6 (.leaf 5748575166) (.leaf 5606127752)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5468182094) (.leaf 5334521990)) (.branch 10 (.leaf 5204946969) (.leaf 5079270823))) (.branch 13 (.branch 12 (.leaf 4957320280) (.leaf 4838933832)) (.branch 14 (.leaf 4723960680) (.leaf 4612259790))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4503699051) (.branch 17 (.leaf 4398154508) (.leaf 4295509684))) (.branch 20 (.branch 19 (.leaf 4195654960) (.leaf 4098487021)) (.branch 21 (.leaf 4003908354) (.leaf 3911826792)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3822155106) (.leaf 3734810628)) (.branch 25 (.leaf 3649714917) (.leaf 3566793449))) (.branch 28 (.branch 27 (.leaf 3485975338) (.leaf 3407193079)) (.branch 29 (.leaf 3330382318) (.leaf 3255481638)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3182432365) (.branch 32 (.leaf 3111178391) (.leaf 3041666007))) (.branch 35 (.branch 34 (.leaf 2973843759) (.leaf 2907662305)) (.branch 36 (.leaf 2843074294) (.leaf 2780034242)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2718498433) (.leaf 2658424812)) (.branch 40 (.leaf 2599772896) (.leaf 2542503693))) (.branch 43 (.branch 42 (.leaf 2486579614) (.leaf 2431964411)) (.branch 44 (.leaf 2378623097) (.leaf 2326521895))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2275628168) (.branch 47 (.leaf 2225910371) (.leaf 2177337998))) (.branch 50 (.branch 49 (.leaf 2129881534) (.leaf 2083512407)) (.branch 51 (.leaf 2038202953) (.leaf 1993926369)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1950656679) (.leaf 1908368703)) (.branch 55 (.leaf 1867038016) (.leaf 1826640925))) (.branch 58 (.branch 57 (.leaf 1787154434) (.leaf 1748556222)) (.branch 59 (.leaf 1710824610) (.leaf 1673938544))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1637877566) (.branch 62 (.leaf 1602621795) (.leaf 1568151904))) (.branch 65 (.branch 64 (.leaf 1534449101) (.leaf 1501495111)) (.branch 66 (.leaf 1469272157) (.leaf 1437762942)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1406950635) (.leaf 1376818852)) (.branch 70 (.leaf 1347351646) (.leaf 1318533487))) (.branch 73 (.branch 72 (.leaf 1290349254) (.leaf 1262784216)) (.branch 74 (.leaf 1235824025) (.leaf 1209454703))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1183662627) (.branch 77 (.leaf 1158434522) (.leaf 1133757448))) (.branch 80 (.branch 79 (.leaf 1109618791) (.leaf 1086006255)) (.branch 81 (.leaf 1062907849) (.leaf 1040311879)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1018206942) (.leaf 996581916)) (.branch 85 (.leaf 975425950) (.leaf 954728460))) (.branch 88 (.branch 87 (.leaf 934479117) (.leaf 914667845)) (.branch 89 (.leaf 895284811) (.leaf 876320418)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 857765299) (.branch 92 (.leaf 839610312) (.leaf 821846532))) (.branch 95 (.branch 94 (.leaf 804465247) (.leaf 787457951)) (.branch 96 (.leaf 770816338) (.leaf 754532300)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 738597918) (.leaf 723005458)) (.branch 100 (.leaf 707747368) (.leaf 692816271))) (.branch 103 (.branch 102 (.leaf 678204962) (.leaf 663906403)) (.branch 104 (.leaf 649913719) (.leaf 636220194))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 622819267) (.leaf 609704526)) (.branch 108 (.leaf 596869708) (.leaf 584308693))) (.branch 111 (.branch 110 (.leaf 572015499) (.leaf 559984284)) (.branch 112 (.leaf 548209337) (.leaf 536685074)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 525406043) (.leaf 514366912)) (.branch 116 (.leaf 503562469) (.leaf 492987622))) (.branch 119 (.branch 118 (.leaf 482637392) (.leaf 472506913)) (.branch 120 (.leaf 462591427) (.leaf 452886283)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1233).prefactor = (683308886500799/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1233).cutoff/(generalMeanRows 1233).c)).2 =
    (100333157888019/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1233).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1233).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1233).q*(generalMeanRows 1233).c/2-2 = (1661/2000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable413.value]
    have hcontinuation : (generalMeanRows 1233).q*(generalMeanRows 1233).cutoff/2-2 = (1092/253:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable412.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1233).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1233

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1233).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1233).criticalRate j.val*(generalMeanRows 1233).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1233).c*(generalMeanRows 1233).criticalPoint j.val)).2-
      (generalMeanRows 1233).J/2-(generalMeanRows 1233).error (generalMeanGrid j.val)+
      (generalMeanRows 1233).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1233).c)).2-
      (generalMeanRows 1233).J/2-(generalMeanRows 1233).error 4 := by
  have he : (generalMeanRows 1233).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1233) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1233)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1233

/-! Kernel-checked entropy margins for general spectral rectangle 1234. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1234
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5093160608) (.branch 2 (.leaf 4948117736) (.leaf 4808277999))) (.branch 5 (.branch 4 (.leaf 4673364317) (.leaf 4543121696)) (.branch 6 (.leaf 4417314947) (.leaf 4295726681)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4178155538) (.leaf 4064414622)) (.branch 10 (.leaf 3954330112) (.leaf 3847740040))) (.branch 13 (.branch 12 (.leaf 3744493191) (.leaf 3644448132)) (.branch 14 (.leaf 3547472345) (.leaf 3453441450))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3362238511) (.branch 17 (.leaf 3273753415) (.leaf 3187882311))) (.branch 20 (.branch 19 (.leaf 3104527109) (.leaf 3023595030)) (.branch 21 (.leaf 2944998191) (.leaf 2868653243)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2794481033) (.leaf 2722406303)) (.branch 25 (.leaf 2652357415) (.leaf 2584266101))) (.branch 28 (.branch 27 (.leaf 2518067234) (.leaf 2453698626)) (.branch 29 (.leaf 2391100830) (.leaf 2330216974)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2270992599) (.branch 32 (.leaf 2213375513) (.leaf 2157315659))) (.branch 35 (.branch 34 (.leaf 2102764987) (.leaf 2049677347)) (.branch 36 (.leaf 1998008379) (.leaf 1947715416)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1898757397) (.leaf 1851094783)) (.branch 40 (.leaf 1804689476) (.leaf 1759504753))) (.branch 43 (.branch 42 (.leaf 1715505192) (.leaf 1672656615)) (.branch 44 (.leaf 1630926027) (.leaf 1590281563))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1550692433) (.branch 47 (.leaf 1512128880) (.leaf 1474562129))) (.branch 50 (.branch 49 (.leaf 1437964350) (.leaf 1402308612)) (.branch 51 (.leaf 1367568852) (.leaf 1333719834)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1300737122) (.leaf 1268597039)) (.branch 55 (.leaf 1237276646) (.leaf 1206753711))) (.branch 58 (.branch 57 (.leaf 1177006677) (.leaf 1148014646)) (.branch 59 (.leaf 1119757345) (.leaf 1092215109))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1065368860) (.branch 62 (.leaf 1039200079) (.leaf 1013690793))) (.branch 65 (.branch 64 (.leaf 988823556) (.leaf 964581423)) (.branch 66 (.leaf 940947943) (.leaf 917907135)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 895443475) (.leaf 873541882)) (.branch 70 (.leaf 852187699) (.leaf 831366686))) (.branch 73 (.branch 72 (.leaf 811064999) (.leaf 791269181)) (.branch 74 (.leaf 771966152) (.leaf 753143193))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 734787936) (.branch 77 (.leaf 716888353) (.leaf 699432746))) (.branch 80 (.branch 79 (.leaf 682409737) (.leaf 665808258)) (.branch 81 (.leaf 649617540) (.leaf 633827106)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 618426762) (.leaf 603406588)) (.branch 85 (.leaf 588756930) (.leaf 574468392))) (.branch 88 (.branch 87 (.leaf 560531828) (.leaf 546938337)) (.branch 89 (.leaf 533679251) (.leaf 520746136)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 508130776) (.branch 92 (.leaf 495825175) (.leaf 483821545))) (.branch 95 (.branch 94 (.leaf 472112303) (.leaf 460690065)) (.branch 96 (.leaf 449547639) (.leaf 438678021)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 428074389) (.leaf 417730097)) (.branch 100 (.leaf 407638674) (.leaf 397793815))) (.branch 103 (.branch 102 (.leaf 388189375) (.leaf 378819373)) (.branch 104 (.leaf 369677977) (.leaf 360759507))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 352058429) (.leaf 343569351)) (.branch 108 (.leaf 335287017) (.leaf 327206307))) (.branch 111 (.branch 110 (.leaf 319322231) (.leaf 311629926)) (.branch 112 (.leaf 304124652) (.leaf 296801792)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 289656843) (.leaf 282685418)) (.branch 116 (.leaf 275883240) (.leaf 269246141))) (.branch 119 (.branch 118 (.leaf 262770058) (.leaf 256451029)) (.branch 120 (.leaf 250285194) (.leaf 244268789)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1234).prefactor = (38355411575291/8000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1234).cutoff/(generalMeanRows 1234).c)).2 =
    (6521129819131/7812500000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1234).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1234).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1234).q*(generalMeanRows 1234).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1234).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1234

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1234).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1234).criticalRate j.val*(generalMeanRows 1234).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1234).c*(generalMeanRows 1234).criticalPoint j.val)).2-
      (generalMeanRows 1234).J/2-(generalMeanRows 1234).error (generalMeanGrid j.val)+
      (generalMeanRows 1234).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1234).c)).2-
      (generalMeanRows 1234).J/2-(generalMeanRows 1234).error 4 := by
  have he : (generalMeanRows 1234).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1234) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1234)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1234

/-! Kernel-checked entropy margins for general spectral rectangle 1235. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1235
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5479195847) (.branch 2 (.leaf 5328106882) (.leaf 5182338345))) (.branch 5 (.branch 4 (.leaf 5041606756) (.leaf 4905651405)) (.branch 6 (.leaf 4774231988) (.leaf 4647126535)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4524129573) (.leaf 4405050506)) (.branch 10 (.leaf 4289712186) (.leaf 4177949634))) (.branch 13 (.branch 12 (.leaf 4069608918) (.leaf 3964546140)) (.branch 14 (.leaf 3862626544) (.leaf 3763723713))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3667718849) (.branch 17 (.leaf 3574500138) (.leaf 3483962167))) (.branch 20 (.branch 19 (.leaf 3396005408) (.leaf 3310535752)) (.branch 21 (.leaf 3227464091) (.leaf 3146705931)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3068181055) (.leaf 2991813209)) (.branch 25 (.leaf 2917529819) (.leaf 2845261738))) (.branch 28 (.branch 27 (.leaf 2774943008) (.leaf 2706510647)) (.branch 29 (.leaf 2639904460) (.leaf 2575066857)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2511942689) (.branch 32 (.leaf 2450479104) (.leaf 2390625406))) (.branch 35 (.branch 34 (.leaf 2332332930) (.leaf 2275554925)) (.branch 36 (.leaf 2220246450) (.leaf 2166364272)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2113866774) (.leaf 2062713874)) (.branch 40 (.leaf 2012866942) (.leaf 1964288729))) (.branch 43 (.branch 42 (.leaf 1916943299) (.leaf 1870795966)) (.branch 44 (.leaf 1825813232) (.leaf 1781962734))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1739213194) (.branch 47 (.leaf 1697534365) (.leaf 1656896991))) (.branch 50 (.branch 49 (.leaf 1617272761) (.leaf 1578634271)) (.branch 51 (.leaf 1540954985) (.leaf 1504209198)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1468372006) (.leaf 1433419269)) (.branch 55 (.leaf 1399327586) (.leaf 1366074265))) (.branch 58 (.branch 57 (.leaf 1333637293) (.leaf 1301995315)) (.branch 59 (.leaf 1271127607) (.leaf 1241014052))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1211635123) (.branch 62 (.leaf 1182971854) (.leaf 1155005828))) (.branch 65 (.branch 64 (.leaf 1127719155) (.leaf 1101094450)) (.branch 66 (.leaf 1075114823) (.leaf 1049763856)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1025025593) (.leaf 1000884517)) (.branch 70 (.leaf 977325545) (.leaf 954334006))) (.branch 73 (.branch 72 (.leaf 931895632) (.leaf 909996545)) (.branch 74 (.leaf 888623242) (.leaf 867762587))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 847401796) (.branch 77 (.leaf 827528430) (.leaf 808130381))) (.branch 80 (.branch 79 (.leaf 789195862) (.leaf 770713401)) (.branch 81 (.leaf 752671828) (.leaf 735060267)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 717868128) (.leaf 701085098)) (.branch 85 (.leaf 684701132) (.leaf 668706449))) (.branch 88 (.branch 87 (.leaf 653091518) (.leaf 637847056)) (.branch 89 (.leaf 622964022) (.leaf 608433603)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 594247214) (.branch 92 (.leaf 580396492) (.leaf 566873282))) (.branch 95 (.branch 94 (.leaf 553669643) (.leaf 540777831)) (.branch 96 (.leaf 528190299) (.leaf 515899694)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 503898845) (.leaf 492180762)) (.branch 100 (.leaf 480738633) (.leaf 469565815))) (.branch 103 (.branch 102 (.leaf 458655832) (.leaf 448002369)) (.branch 104 (.leaf 437599269) (.leaf 427440528))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 417520293) (.leaf 407832854)) (.branch 108 (.leaf 398372642) (.leaf 389134229))) (.branch 111 (.branch 110 (.leaf 380112319) (.leaf 371301745)) (.branch 112 (.leaf 362697470) (.leaf 354294579)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 346088279) (.leaf 338073893)) (.branch 116 (.leaf 330246860) (.leaf 322602730))) (.branch 119 (.branch 118 (.leaf 315137162) (.leaf 307845919)) (.branch 120 (.leaf 300724869) (.leaf 293769981)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1235).prefactor = (2479274508062869/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1235).cutoff/(generalMeanRows 1235).c)).2 =
    (211867686917951/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1235).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1235).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1235).q*(generalMeanRows 1235).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1235).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1235

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1235).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1235).criticalRate j.val*(generalMeanRows 1235).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1235).c*(generalMeanRows 1235).criticalPoint j.val)).2-
      (generalMeanRows 1235).J/2-(generalMeanRows 1235).error (generalMeanGrid j.val)+
      (generalMeanRows 1235).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1235).c)).2-
      (generalMeanRows 1235).J/2-(generalMeanRows 1235).error 4 := by
  have he : (generalMeanRows 1235).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1235) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1235)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1235

/-! Kernel-checked entropy margins for general spectral rectangle 1236. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1236
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6050332286) (.branch 2 (.leaf 5894422268) (.leaf 5743804982))) (.branch 5 (.branch 4 (.leaf 5598197247) (.leaf 5457339000)) (.branch 6 (.leaf 5320990872) (.leaf 5188932070)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5060958496) (.leaf 4936881094)) (.branch 10 (.leaf 4816524385) (.leaf 4699725163))) (.branch 13 (.branch 12 (.leaf 4586331349) (.leaf 4476200959)) (.branch 14 (.leaf 4369201189) (.leaf 4265207601))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4164103392) (.branch 17 (.leaf 4065778740) (.leaf 3970130219))) (.branch 20 (.branch 19 (.leaf 3877060271) (.leaf 3786476734)) (.branch 21 (.leaf 3698292412) (.leaf 3612424695)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3528795207) (.leaf 3447329495)) (.branch 25 (.leaf 3367956739) (.leaf 3290609496))) (.branch 28 (.branch 27 (.leaf 3215223467) (.leaf 3141737276)) (.branch 29 (.leaf 3070092281) (.leaf 3000232392)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2932103910) (.branch 32 (.leaf 2865655377) (.leaf 2800837438))) (.branch 35 (.branch 34 (.leaf 2737602716) (.leaf 2675905696)) (.branch 36 (.leaf 2615702621) (.leaf 2556951388)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2499611463) (.leaf 2443643794)) (.branch 40 (.leaf 2389010733) (.leaf 2335675965))) (.branch 43 (.branch 42 (.leaf 2283604441) (.leaf 2232762315)) (.branch 44 (.leaf 2183116883) (.leaf 2134636536))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2087290702) (.branch 47 (.leaf 2041049802) (.leaf 1995885207))) (.branch 50 (.branch 49 (.leaf 1951769192) (.leaf 1908674900)) (.branch 51 (.leaf 1866576307) (.leaf 1825448182)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1785266061) (.leaf 1746006211)) (.branch 55 (.leaf 1707645602) (.leaf 1670161883))) (.branch 58 (.branch 57 (.leaf 1633533353) (.leaf 1597738936)) (.branch 59 (.leaf 1562758160) (.leaf 1528571133))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1495158523) (.branch 62 (.leaf 1462501538) (.leaf 1430581906))) (.branch 65 (.branch 64 (.leaf 1399381859) (.leaf 1368884113)) (.branch 66 (.leaf 1339071854) (.leaf 1309928720)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1281438790) (.leaf 1253586563)) (.branch 70 (.leaf 1226356953) (.leaf 1199735266))) (.branch 73 (.branch 72 (.leaf 1173707196) (.leaf 1148258809)) (.branch 74 (.leaf 1123376530) (.leaf 1099047135))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1075257740) (.branch 77 (.leaf 1051995788) (.leaf 1029249043))) (.branch 80 (.branch 79 (.leaf 1007005575) (.leaf 985253758)) (.branch 81 (.leaf 963982256) (.leaf 943180016)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 922836261) (.leaf 902940479)) (.branch 85 (.leaf 883482418) (.leaf 864452081))) (.branch 88 (.branch 87 (.leaf 845839714) (.leaf 827635799)) (.branch 89 (.leaf 809831054) (.leaf 792416419)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 775383056) (.branch 92 (.leaf 758722338) (.leaf 742425846))) (.branch 95 (.branch 94 (.leaf 726485363) (.leaf 710892869)) (.branch 96 (.leaf 695640535) (.leaf 680720717)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 666125955) (.leaf 651848964)) (.branch 100 (.leaf 637882629) (.leaf 624220007))) (.branch 103 (.branch 102 (.leaf 610854314) (.leaf 597778928)) (.branch 104 (.leaf 584987379) (.leaf 572473352))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 560230675) (.leaf 548253321)) (.branch 108 (.leaf 536535405) (.leaf 525071174))) (.branch 111 (.branch 110 (.leaf 513855012) (.leaf 502881430)) (.branch 112 (.leaf 492145067) (.leaf 481640684)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 471363162) (.leaf 461307501)) (.branch 116 (.leaf 451468814) (.leaf 441842326))) (.branch 119 (.branch 118 (.leaf 432423370) (.leaf 423207386)) (.branch 120 (.leaf 414189919) (.leaf 405366612)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1236).prefactor = (2529853573596587/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1236).cutoff/(generalMeanRows 1236).c)).2 =
    (3494010345559/4000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1236).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1236).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1236).q*(generalMeanRows 1236).c/2-2 = (27/32:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable332.value]
    have hcontinuation : (generalMeanRows 1236).q*(generalMeanRows 1236).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1236).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1236

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1236).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1236).criticalRate j.val*(generalMeanRows 1236).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1236).c*(generalMeanRows 1236).criticalPoint j.val)).2-
      (generalMeanRows 1236).J/2-(generalMeanRows 1236).error (generalMeanGrid j.val)+
      (generalMeanRows 1236).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1236).c)).2-
      (generalMeanRows 1236).J/2-(generalMeanRows 1236).error 4 := by
  have he : (generalMeanRows 1236).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1236) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1236)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1236

/-! Kernel-checked entropy margins for general spectral rectangle 1237. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1237
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5817749846) (.branch 2 (.leaf 5660827647) (.leaf 5509363762))) (.branch 5 (.branch 4 (.leaf 5363067098) (.leaf 5221670067)) (.branch 6 (.leaf 5084926139) (.leaf 4952607695)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4824504129) (.leaf 4700420169)) (.branch 10 (.leaf 4580174400) (.leaf 4463597943))) (.branch 13 (.branch 12 (.leaf 4350533288) (.leaf 4240833254)) (.branch 14 (.leaf 4134360061) (.leaf 4030984502))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3930585205) (.branch 17 (.leaf 3833047962) (.leaf 3738265144))) (.branch 20 (.branch 19 (.leaf 3646135158) (.leaf 3556561967)) (.branch 21 (.leaf 3469454661) (.leaf 3384727058)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3302297353) (.leaf 3222087799)) (.branch 25 (.leaf 3144024412) (.leaf 3068036710))) (.branch 28 (.branch 27 (.leaf 2994057472) (.leaf 2922022515)) (.branch 29 (.leaf 2851870500) (.leaf 2783542745)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2716983062) (.branch 32 (.leaf 2652137597) (.leaf 2588954697))) (.branch 35 (.branch 34 (.leaf 2527384775) (.leaf 2467380193)) (.branch 36 (.leaf 2408895155) (.leaf 2351885599)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2296309109) (.leaf 2242124827)) (.branch 40 (.leaf 2189293371) (.leaf 2137776760))) (.branch 43 (.branch 42 (.leaf 2087538346) (.leaf 2038542750)) (.branch 44 (.leaf 1990755797) (.leaf 1944144466))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1898676831) (.branch 47 (.leaf 1854322017) (.leaf 1811050149))) (.branch 50 (.branch 49 (.leaf 1768832312) (.leaf 1727640509)) (.branch 51 (.leaf 1687447621) (.leaf 1648227373)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1609954298) (.leaf 1572603708)) (.branch 55 (.leaf 1536151658) (.leaf 1500574921))) (.branch 58 (.branch 57 (.leaf 1465850962) (.leaf 1431957907)) (.branch 59 (.leaf 1398874524) (.leaf 1366580196))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1335054898) (.branch 62 (.leaf 1304279181) (.leaf 1274234145))) (.branch 65 (.branch 64 (.leaf 1244901426) (.leaf 1216263173)) (.branch 66 (.leaf 1188302034) (.leaf 1161001137)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1134344074) (.leaf 1108314889)) (.branch 70 (.leaf 1082898058) (.leaf 1058078479))) (.branch 73 (.branch 72 (.leaf 1033841457) (.leaf 1010172693)) (.branch 74 (.leaf 987058269) (.leaf 964484636))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 942438606) (.branch 77 (.leaf 920907337) (.leaf 899878327))) (.branch 80 (.branch 79 (.leaf 879339398) (.leaf 859278690)) (.branch 81 (.leaf 839684653) (.leaf 820546034)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 801851871) (.leaf 783591482)) (.branch 85 (.leaf 765754461) (.leaf 748330665))) (.branch 88 (.branch 87 (.leaf 731310212) (.leaf 714683469)) (.branch 89 (.leaf 698441046) (.leaf 682573792)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 667072785) (.branch 92 (.leaf 651929326) (.leaf 637134935))) (.branch 95 (.branch 94 (.leaf 622681343) (.leaf 608560487)) (.branch 96 (.leaf 594764505) (.leaf 581285729)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 568116680) (.leaf 555250066)) (.branch 100 (.leaf 542678771) (.leaf 530395857))) (.branch 103 (.branch 102 (.leaf 518394554) (.leaf 506668258)) (.branch 104 (.leaf 495210527) (.leaf 484015076))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 473075772) (.leaf 462386632)) (.branch 108 (.leaf 451941816) (.leaf 441735629))) (.branch 111 (.branch 110 (.leaf 431762510) (.leaf 422017034)) (.branch 112 (.leaf 412493906) (.leaf 403187958)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 394094148) (.leaf 385207553)) (.branch 116 (.leaf 376523368) (.leaf 368036903))) (.branch 119 (.branch 118 (.leaf 359743581) (.leaf 351638933)) (.branch 120 (.leaf 343718596) (.leaf 335978313)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1237).prefactor = (2564144910509669/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1237).cutoff/(generalMeanRows 1237).c)).2 =
    (214018237813617/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1237).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1237).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1237).q*(generalMeanRows 1237).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1237).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1237

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1237).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1237).criticalRate j.val*(generalMeanRows 1237).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1237).c*(generalMeanRows 1237).criticalPoint j.val)).2-
      (generalMeanRows 1237).J/2-(generalMeanRows 1237).error (generalMeanGrid j.val)+
      (generalMeanRows 1237).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1237).c)).2-
      (generalMeanRows 1237).J/2-(generalMeanRows 1237).error 4 := by
  have he : (generalMeanRows 1237).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1237) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1237)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1237

/-! Kernel-checked entropy margins for general spectral rectangle 1238. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1238
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5938292540) (.branch 2 (.leaf 5776331424) (.leaf 5620038585))) (.branch 5 (.branch 4 (.leaf 5469111888) (.leaf 5323273529)) (.branch 6 (.leaf 5182267510) (.leaf 5045857412)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4913824440) (.leaf 4785965684)) (.branch 10 (.leaf 4662092589) (.leaf 4542029594))) (.branch 13 (.branch 12 (.leaf 4425612920) (.leaf 4312689501)) (.branch 14 (.leaf 4203116018) (.leaf 4096758044))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3993489281) (.branch 17 (.leaf 3893190868) (.leaf 3795750770))) (.branch 20 (.branch 19 (.leaf 3701063221) (.leaf 3609028227)) (.branch 21 (.leaf 3519551116) (.leaf 3432542133)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3347916071) (.leaf 3265591940)) (.branch 25 (.leaf 3185492667) (.leaf 3107544820))) (.branch 28 (.branch 27 (.leaf 3031678358) (.leaf 2957826406)) (.branch 29 (.leaf 2885925047) (.leaf 2815913133)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2747732109) (.branch 32 (.leaf 2681325859) (.leaf 2616640552))) (.branch 35 (.branch 34 (.leaf 2553624518) (.leaf 2492228117)) (.branch 36 (.leaf 2432403624) (.leaf 2374105132)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2317288444) (.leaf 2261910992)) (.branch 40 (.leaf 2207931747) (.leaf 2155311143))) (.branch 43 (.branch 42 (.leaf 2104011006) (.leaf 2053994485)) (.branch 44 (.leaf 2005225991) (.leaf 1957671133))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1911296672) (.branch 47 (.leaf 1866070461) (.leaf 1821961400))) (.branch 50 (.branch 49 (.leaf 1778939393) (.leaf 1736975301)) (.branch 51 (.leaf 1696040905) (.leaf 1656108866)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1617152692) (.leaf 1579146703)) (.branch 55 (.leaf 1542065997) (.leaf 1505886423))) (.branch 58 (.branch 57 (.leaf 1470584552) (.leaf 1436137648)) (.branch 59 (.leaf 1402523643) (.leaf 1369721115))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1337709260) (.branch 62 (.leaf 1306467875) (.leaf 1275977334))) (.branch 65 (.branch 64 (.leaf 1246218568) (.leaf 1217173046)) (.branch 66 (.leaf 1188822758) (.leaf 1161150196)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1134138337) (.leaf 1107770630)) (.branch 70 (.leaf 1082030976) (.leaf 1056903717))) (.branch 73 (.branch 72 (.leaf 1032373620) (.leaf 1008425865)) (.branch 74 (.leaf 985046032) (.leaf 962220084))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 939934364) (.branch 77 (.leaf 918175574) (.leaf 896930771))) (.branch 80 (.branch 79 (.leaf 876187351) (.leaf 855933045)) (.branch 81 (.leaf 836155901) (.leaf 816844282)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 797986853) (.leaf 779572573)) (.branch 85 (.leaf 761590686) (.leaf 744030713))) (.branch 88 (.branch 87 (.leaf 726882445) (.leaf 710135934)) (.branch 89 (.leaf 693781486) (.leaf 677809653)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 662211229) (.branch 92 (.leaf 646977240) (.leaf 632098939))) (.branch 95 (.branch 94 (.leaf 617567800) (.leaf 603375510)) (.branch 96 (.leaf 589513966) (.leaf 575975267)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 562751711) (.leaf 549835785)) (.branch 100 (.leaf 537220166) (.leaf 524897710))) (.branch 103 (.branch 102 (.leaf 512861453) (.leaf 501104600)) (.branch 104 (.leaf 489620526) (.leaf 478402769))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 467445024) (.leaf 456741143)) (.branch 108 (.leaf 446285128) (.leaf 436071128))) (.branch 111 (.branch 110 (.leaf 426093433) (.leaf 416346474)) (.branch 112 (.leaf 406824818) (.leaf 397523164)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 388436338) (.leaf 379559294)) (.branch 116 (.leaf 370887105) (.leaf 362414966))) (.branch 119 (.branch 118 (.leaf 354138186) (.leaf 346052189)) (.branch 120 (.leaf 338152509) (.leaf 330434785)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1238).prefactor = (5303841184758327/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1238).cutoff/(generalMeanRows 1238).c)).2 =
    (170352519950669/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1238).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1238).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1238).q*(generalMeanRows 1238).c/2-2 = (29/32:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable415.value]
    have hcontinuation : (generalMeanRows 1238).q*(generalMeanRows 1238).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1238).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1238

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1238).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1238).criticalRate j.val*(generalMeanRows 1238).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1238).c*(generalMeanRows 1238).criticalPoint j.val)).2-
      (generalMeanRows 1238).J/2-(generalMeanRows 1238).error (generalMeanGrid j.val)+
      (generalMeanRows 1238).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1238).c)).2-
      (generalMeanRows 1238).J/2-(generalMeanRows 1238).error 4 := by
  have he : (generalMeanRows 1238).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1238) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1238)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1238

/-! Kernel-checked entropy margins for general spectral rectangle 1239. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1239
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6473521150) (.branch 2 (.leaf 6304757140) (.leaf 6141756957))) (.branch 5 (.branch 4 (.leaf 5984212522) (.leaf 5831840835)) (.branch 6 (.leaf 5684381353) (.leaf 5541593692)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5403255592) (.leaf 5269161121)) (.branch 10 (.leaf 5139119089) (.leaf 5012951643))) (.branch 13 (.branch 12 (.leaf 4890493009) (.leaf 4771588384)) (.branch 14 (.leaf 4656092944) (.leaf 4543870959))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4434794999) (.branch 17 (.leaf 4328745226) (.leaf 4225608762))) (.branch 20 (.branch 19 (.leaf 4125279113) (.leaf 4027655656)) (.branch 21 (.leaf 3932643179) (.leaf 3840151460)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3750094893) (.leaf 3662392140)) (.branch 25 (.leaf 3576965830) (.leaf 3493742270))) (.branch 28 (.branch 27 (.leaf 3412651194) (.leaf 3333625527)) (.branch 29 (.leaf 3256601176) (.leaf 3181516835)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3108313805) (.branch 32 (.leaf 3036935836) (.leaf 2967328976))) (.branch 35 (.branch 34 (.leaf 2899441432) (.leaf 2833223447)) (.branch 36 (.leaf 2768627186) (.leaf 2705606622)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2644117444) (.leaf 2584116961)) (.branch 40 (.leaf 2525564021) (.leaf 2468418928))) (.branch 43 (.branch 42 (.leaf 2412643372) (.leaf 2358200361)) (.branch 44 (.leaf 2305054155) (.leaf 2253170209))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2202515118) (.branch 47 (.leaf 2153056563) (.leaf 2104763265))) (.branch 50 (.branch 49 (.leaf 2057604938) (.leaf 2011552246)) (.branch 51 (.leaf 1966576766) (.leaf 1922650945)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1879748069) (.leaf 1837842229)) (.branch 55 (.leaf 1796908284) (.leaf 1756921839))) (.branch 58 (.branch 57 (.leaf 1717859211) (.leaf 1679697403)) (.branch 59 (.leaf 1642414080) (.leaf 1605987544))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1570396711) (.branch 62 (.leaf 1535621089) (.leaf 1501640758))) (.branch 65 (.branch 64 (.leaf 1468436347) (.leaf 1435989021)) (.branch 66 (.leaf 1404280456) (.leaf 1373292829)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1343008794) (.leaf 1313411473)) (.branch 70 (.leaf 1284484436) (.leaf 1256211689))) (.branch 73 (.branch 72 (.leaf 1228577660) (.leaf 1201567186)) (.branch 74 (.leaf 1175165499) (.leaf 1149358214))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1124131320) (.branch 77 (.leaf 1099471162) (.leaf 1075364440))) (.branch 80 (.branch 79 (.leaf 1051798190) (.leaf 1028759778)) (.branch 81 (.leaf 1006236889) (.leaf 984217520)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 962689968) (.leaf 941642821)) (.branch 85 (.leaf 921064955) (.leaf 900945519))) (.branch 88 (.branch 87 (.leaf 881273933) (.leaf 862039875)) (.branch 89 (.leaf 843233279) (.leaf 824844325)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 806863433) (.branch 92 (.leaf 789281257) (.leaf 772088676))) (.branch 95 (.branch 94 (.leaf 755276792) (.leaf 738836922)) (.branch 96 (.leaf 722760590) (.leaf 707039526)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 691665657) (.leaf 676631104)) (.branch 100 (.leaf 661928175) (.leaf 647549361))) (.branch 103 (.branch 102 (.leaf 633487333) (.leaf 619734934)) (.branch 104 (.leaf 606285176) (.leaf 593131238))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 580266457) (.leaf 567684328)) (.branch 108 (.leaf 555378499) (.leaf 543342766))) (.branch 111 (.branch 110 (.leaf 531571070) (.leaf 520057494)) (.branch 112 (.leaf 508796258) (.leaf 497781717)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 487008356) (.leaf 476470789)) (.branch 116 (.leaf 466163754) (.leaf 456082110))) (.branch 119 (.branch 118 (.leaf 446220837) (.leaf 436575028)) (.branch 120 (.leaf 427139889) (.leaf 417910738)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1239).prefactor = (1371350503526491/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1239).cutoff/(generalMeanRows 1239).c)).2 =
    (173823322889299/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1239).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1239).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1239).q*(generalMeanRows 1239).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1239).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1239

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1239).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1239).criticalRate j.val*(generalMeanRows 1239).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1239).c*(generalMeanRows 1239).criticalPoint j.val)).2-
      (generalMeanRows 1239).J/2-(generalMeanRows 1239).error (generalMeanGrid j.val)+
      (generalMeanRows 1239).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1239).c)).2-
      (generalMeanRows 1239).J/2-(generalMeanRows 1239).error 4 := by
  have he : (generalMeanRows 1239).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1239) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1239)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1239

/-! Kernel-checked entropy margins for general spectral rectangle 1240. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1240
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6965168510) (.branch 2 (.leaf 6789878283) (.leaf 6620467752))) (.branch 5 (.branch 4 (.leaf 6456621586) (.leaf 6298050338)) (.branch 6 (.leaf 6144487732) (.leaf 5995688276)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5851425156) (.leaf 5711488377)) (.branch 10 (.leaf 5575683122) (.leaf 5443828290))) (.branch 13 (.branch 12 (.leaf 5315755206) (.leaf 5191306466)) (.branch 14 (.leaf 5070334911) (.leaf 4952702715))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4838280563) (.branch 17 (.leaf 4726946921) (.leaf 4618587379))) (.branch 20 (.branch 19 (.leaf 4513094058) (.leaf 4410365085)) (.branch 21 (.leaf 4310304110) (.leaf 4212819878)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4117825842) (.leaf 4025239804)) (.branch 25 (.leaf 3934983604) (.leaf 3846982823))) (.branch 28 (.branch 27 (.leaf 3761166528) (.leaf 3677467024)) (.branch 29 (.leaf 3595819644) (.leaf 3516162545)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3438436525) (.branch 32 (.leaf 3362584863) (.leaf 3288553158))) (.branch 35 (.branch 34 (.leaf 3216289196) (.leaf 3145742817)) (.branch 36 (.leaf 3076865796) (.leaf 3009611738)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2943935972) (.leaf 2879795461)) (.branch 40 (.leaf 2817148713) (.leaf 2755955705))) (.branch 43 (.branch 42 (.leaf 2696177801) (.leaf 2637777693)) (.branch 44 (.leaf 2580719328) (.leaf 2524967850))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2470489549) (.branch 47 (.leaf 2417251801) (.leaf 2365223023))) (.branch 50 (.branch 49 (.leaf 2314372629) (.leaf 2264670982)) (.branch 51 (.leaf 2216089357) (.leaf 2168599901)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2122175598) (.leaf 2076790237)) (.branch 55 (.leaf 2032418376) (.leaf 1989035314))) (.branch 58 (.branch 57 (.leaf 1946617064) (.leaf 1905140324)) (.branch 59 (.leaf 1864582451) (.leaf 1824921438))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1786135893) (.branch 62 (.leaf 1748205011) (.leaf 1711108559))) (.branch 65 (.branch 64 (.leaf 1674826854) (.leaf 1639340744)) (.branch 66 (.leaf 1604631590) (.leaf 1570681249)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1537472058) (.leaf 1504986817)) (.branch 70 (.leaf 1473208777) (.leaf 1442121621))) (.branch 73 (.branch 72 (.leaf 1411709455) (.leaf 1381956791)) (.branch 74 (.leaf 1352848536) (.leaf 1324369981))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1296506788) (.branch 77 (.leaf 1269244979) (.leaf 1242570924))) (.branch 80 (.branch 79 (.leaf 1216471334) (.leaf 1190933247)) (.branch 81 (.leaf 1165944023) (.leaf 1141491331)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1117563139) (.leaf 1094147712)) (.branch 85 (.leaf 1071233598) (.leaf 1048809619))) (.branch 88 (.branch 87 (.leaf 1026864870) (.leaf 1005388705)) (.branch 89 (.leaf 984370733) (.leaf 963800810)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 943669033) (.branch 92 (.leaf 923965734) (.leaf 904681472))) (.branch 95 (.branch 94 (.leaf 885807029) (.leaf 867333400)) (.branch 96 (.leaf 849251795) (.leaf 831553625)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 814230503) (.leaf 797274235)) (.branch 100 (.leaf 780676817) (.leaf 764430430))) (.branch 103 (.branch 102 (.leaf 748527434) (.leaf 732960363)) (.branch 104 (.leaf 717721926) (.leaf 702804994))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 688202604) (.leaf 673907949)) (.branch 108 (.leaf 659914377) (.leaf 646215386))) (.branch 111 (.branch 110 (.leaf 632804624) (.leaf 619675878)) (.branch 112 (.leaf 606823078) (.leaf 594240288)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 581921707) (.leaf 569861663)) (.branch 116 (.leaf 558054611) (.leaf 546495129))) (.branch 119 (.branch 118 (.leaf 535177916) (.leaf 524097791)) (.branch 120 (.leaf 513249684) (.leaf 502628641)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1240).prefactor = (354573626549501/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1240).cutoff/(generalMeanRows 1240).c)).2 =
    (882332665838021/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1240).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1240).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1240).q*(generalMeanRows 1240).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1240).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1240

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1240).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1240).criticalRate j.val*(generalMeanRows 1240).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1240).c*(generalMeanRows 1240).criticalPoint j.val)).2-
      (generalMeanRows 1240).J/2-(generalMeanRows 1240).error (generalMeanGrid j.val)+
      (generalMeanRows 1240).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1240).c)).2-
      (generalMeanRows 1240).J/2-(generalMeanRows 1240).error 4 := by
  have he : (generalMeanRows 1240).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1240) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1240)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1240

/-! Kernel-checked entropy margins for general spectral rectangle 1241. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1241
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7524534556) (.branch 2 (.leaf 7346495399) (.leaf 7174255948))) (.branch 5 (.branch 4 (.leaf 7007502596) (.leaf 6845947848)) (.branch 6 (.leaf 6689327567) (.leaf 6537398553)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6389936403) (.leaf 6246733631)) (.branch 10 (.leaf 6107597999) (.leaf 5972351036))) (.branch 13 (.branch 12 (.leaf 5840826733) (.leaf 5712870371)) (.branch 14 (.leaf 5588337483) (.leaf 5467092932))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5349010079) (.branch 17 (.leaf 5233970042) (.leaf 5121861037))) (.branch 20 (.branch 19 (.leaf 5012577776) (.leaf 4906020938)) (.branch 21 (.leaf 4802096683) (.leaf 4700716219)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4601795408) (.leaf 4505254417)) (.branch 25 (.leaf 4411017390) (.leaf 4319012163))) (.branch 28 (.branch 27 (.leaf 4229169996) (.leaf 4141425337)) (.branch 29 (.leaf 4055715598) (.leaf 3971980959)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3890164188) (.branch 32 (.leaf 3810210469) (.leaf 3732067254))) (.branch 35 (.branch 34 (.leaf 3655684124) (.leaf 3581012656)) (.branch 36 (.leaf 3508006308) (.leaf 3436620313)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3366811572) (.leaf 3298538568)) (.branch 40 (.leaf 3231761276) (.leaf 3166441089))) (.branch 43 (.branch 42 (.leaf 3102540737) (.leaf 3040024226)) (.branch 44 (.leaf 2978856771) (.leaf 2919004735))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2860435581) (.branch 47 (.leaf 2803117812) (.leaf 2747020929))) (.branch 50 (.branch 49 (.leaf 2692115385) (.leaf 2638372541)) (.branch 51 (.leaf 2585764628) (.leaf 2534264709)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2483846645) (.leaf 2434485064)) (.branch 55 (.leaf 2386155324) (.leaf 2338833492))) (.branch 58 (.branch 57 (.leaf 2292496311) (.leaf 2247121173)) (.branch 59 (.leaf 2202686100) (.leaf 2159169716))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2116551225) (.branch 62 (.leaf 2074810394) (.leaf 2033927528))) (.branch 65 (.branch 64 (.leaf 1993883454) (.leaf 1954659503)) (.branch 66 (.leaf 1916237492) (.leaf 1878599708)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1841728889) (.leaf 1805608218)) (.branch 70 (.leaf 1770221298) (.leaf 1735552146))) (.branch 73 (.branch 72 (.leaf 1701585177) (.leaf 1668305192)) (.branch 74 (.leaf 1635697364) (.leaf 1603747232))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1572440685) (.branch 77 (.leaf 1541763951) (.leaf 1511703592))) (.branch 80 (.branch 79 (.leaf 1482246491) (.leaf 1453379840)) (.branch 81 (.leaf 1425091137) (.leaf 1397368172)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1370199022) (.leaf 1343572043)) (.branch 85 (.leaf 1317475859) (.leaf 1291899358))) (.branch 88 (.branch 87 (.leaf 1266831683) (.leaf 1242262226)) (.branch 89 (.leaf 1218180620) (.leaf 1194576734)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1171440667) (.branch 92 (.leaf 1148762741) (.leaf 1126533493))) (.branch 95 (.branch 94 (.leaf 1104743674) (.leaf 1083384240)) (.branch 96 (.leaf 1062446350) (.leaf 1041921356)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1021800803) (.leaf 1002076419)) (.branch 100 (.leaf 982740118) (.leaf 963783986))) (.branch 103 (.branch 102 (.leaf 945200286) (.leaf 926981445)) (.branch 104 (.leaf 909120056) (.leaf 891608874))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 874440807) (.leaf 857608918)) (.branch 108 (.leaf 841106417) (.leaf 824926660))) (.branch 111 (.branch 110 (.leaf 809063144) (.leaf 793509507)) (.branch 112 (.leaf 778259520) (.leaf 763307085)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 748646236) (.leaf 734271131)) (.branch 116 (.leaf 720176051) (.leaf 706355397))) (.branch 119 (.branch 118 (.leaf 692803690) (.leaf 679515562)) (.branch 120 (.leaf 666485759) (.leaf 653709138)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1241).prefactor = (2868593872634413/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1241).cutoff/(generalMeanRows 1241).c)).2 =
    (452377564946927/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1241).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1241).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1241).q*(generalMeanRows 1241).c/2-2 = (121/160:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable416.value]
    have hcontinuation : (generalMeanRows 1241).q*(generalMeanRows 1241).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1241).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1241

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1241).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1241).criticalRate j.val*(generalMeanRows 1241).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1241).c*(generalMeanRows 1241).criticalPoint j.val)).2-
      (generalMeanRows 1241).J/2-(generalMeanRows 1241).error (generalMeanGrid j.val)+
      (generalMeanRows 1241).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1241).c)).2-
      (generalMeanRows 1241).J/2-(generalMeanRows 1241).error 4 := by
  have he : (generalMeanRows 1241).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1241) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1241)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1241

/-! Kernel-checked entropy margins for general spectral rectangle 1242. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1242
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5761540711) (.branch 2 (.leaf 5587060911) (.leaf 5419077949))) (.branch 5 (.branch 4 (.leaf 5257245268) (.leaf 5101243542)) (.branch 6 (.leaf 4950777895) (.leaf 4805575448)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4665383151) (.leaf 4529965870)) (.branch 10 (.leaf 4399104693) (.leaf 4272595418))) (.branch 13 (.branch 12 (.leaf 4150247219) (.leaf 4031881450)) (.branch 14 (.leaf 3917330577) (.leaf 3806437229))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3699053342) (.branch 17 (.leaf 3595039395) (.leaf 3494263720))) (.branch 20 (.branch 19 (.leaf 3396601884) (.leaf 3301936130)) (.branch 21 (.leaf 3210154872) (.leaf 3121152240)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3034827666) (.leaf 2951085508)) (.branch 25 (.leaf 2869834709) (.leaf 2790988490))) (.branch 28 (.branch 27 (.leaf 2714464060) (.leaf 2640182366)) (.branch 29 (.leaf 2568067850) (.leaf 2498048234)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2430054321) (.branch 32 (.leaf 2364019816) (.leaf 2299881153))) (.branch 35 (.branch 34 (.leaf 2237577339) (.leaf 2177049817)) (.branch 36 (.leaf 2118242328) (.leaf 2061100792)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2005573190) (.leaf 1951609462)) (.branch 40 (.leaf 1899161409) (.leaf 1848182598))) (.branch 43 (.branch 42 (.leaf 1798628279) (.leaf 1750455305)) (.branch 44 (.leaf 1703622057) (.leaf 1658088375))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1613815490) (.branch 47 (.leaf 1570765964) (.leaf 1528903635))) (.branch 50 (.branch 49 (.leaf 1488193556) (.leaf 1448601949)) (.branch 51 (.leaf 1410096155) (.leaf 1372644587)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1336216688) (.leaf 1300782890)) (.branch 55 (.leaf 1266314575) (.leaf 1232784038))) (.branch 58 (.branch 57 (.leaf 1200164451) (.leaf 1168429833)) (.branch 59 (.leaf 1137555014) (.leaf 1107515609))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1078287986) (.branch 62 (.leaf 1049849242) (.leaf 1022177174))) (.branch 65 (.branch 64 (.leaf 995250256) (.leaf 969047613)) (.branch 66 (.leaf 943549003) (.leaf 918734788)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 894585921) (.leaf 871083920)) (.branch 70 (.leaf 848210852) (.leaf 825949314))) (.branch 73 (.branch 72 (.leaf 804282415) (.leaf 783193760)) (.branch 74 (.leaf 762667433) (.leaf 742687982))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 723240402) (.branch 77 (.leaf 704310126) (.leaf 685883002))) (.branch 80 (.branch 79 (.leaf 667945291) (.leaf 650483644)) (.branch 81 (.leaf 633485096) (.leaf 616937051)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 600827272) (.leaf 585143871)) (.branch 85 (.leaf 569875292) (.leaf 555010312))) (.branch 88 (.branch 87 (.leaf 540538019) (.leaf 526447811)) (.branch 89 (.leaf 512729382) (.leaf 499372715)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 486368075) (.branch 92 (.leaf 473705996) (.leaf 461377277))) (.branch 95 (.branch 94 (.leaf 449372972) (.leaf 437684384)) (.branch 96 (.leaf 426303057) (.leaf 415220767)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 404429520) (.leaf 393921540)) (.branch 100 (.leaf 383689266) (.leaf 373725344))) (.branch 103 (.branch 102 (.leaf 364022623) (.leaf 354574147)) (.branch 104 (.leaf 345373150) (.leaf 336413052))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 327687451) (.leaf 319190122)) (.branch 108 (.leaf 310915007) (.leaf 302856214))) (.branch 111 (.branch 110 (.leaf 295008009) (.leaf 287364817)) (.branch 112 (.leaf 279921211) (.leaf 272671911)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 265611782) (.leaf 258735826)) (.branch 116 (.leaf 252039179) (.leaf 245517111))) (.branch 119 (.branch 118 (.leaf 239165015) (.leaf 232978412)) (.branch 120 (.leaf 226952942) (.leaf 221084361)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1242).prefactor = (2933690987298463/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1242).cutoff/(generalMeanRows 1242).c)).2 =
    (809651114403219/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1242).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1242).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1242).q*(generalMeanRows 1242).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1242).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1242

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1242).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1242).criticalRate j.val*(generalMeanRows 1242).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1242).c*(generalMeanRows 1242).criticalPoint j.val)).2-
      (generalMeanRows 1242).J/2-(generalMeanRows 1242).error (generalMeanGrid j.val)+
      (generalMeanRows 1242).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1242).c)).2-
      (generalMeanRows 1242).J/2-(generalMeanRows 1242).error 4 := by
  have he : (generalMeanRows 1242).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1242) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1242)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1242

/-! Kernel-checked entropy margins for general spectral rectangle 1243. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1243
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6680737607) (.branch 2 (.leaf 6498527028) (.leaf 6322693413))) (.branch 5 (.branch 4 (.leaf 6152896850) (.leaf 5988824804)) (.branch 6 (.leaf 5830189269) (.leaf 5676724268)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5528183651) (.leaf 5384339138)) (.branch 10 (.leaf 5244978599) (.leaf 5109904525))) (.branch 13 (.branch 12 (.leaf 4978932660) (.leaf 4851890799)) (.branch 14 (.leaf 4728617706) (.leaf 4608962147))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4492782031) (.branch 17 (.leaf 4379943640) (.leaf 4270320929))) (.branch 20 (.branch 19 (.leaf 4163794909) (.leaf 4060253084)) (.branch 21 (.leaf 3959588947) (.leaf 3861701518)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3766494939) (.leaf 3673878095)) (.branch 25 (.leaf 3583764275) (.leaf 3496070866))) (.branch 28 (.branch 27 (.leaf 3410719071) (.leaf 3327633654)) (.branch 29 (.leaf 3246742707) (.leaf 3167977434)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3091271963) (.branch 32 (.leaf 3016563158) (.leaf 2943790462))) (.branch 35 (.branch 34 (.leaf 2872895742) (.leaf 2803823151)) (.branch 36 (.leaf 2736519001) (.leaf 2670931641)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2607011351) (.leaf 2544710239)) (.branch 40 (.leaf 2483982147) (.leaf 2424782563))) (.branch 43 (.branch 42 (.leaf 2367068540) (.leaf 2310798619)) (.branch 44 (.leaf 2255932761) (.leaf 2202432277))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2150259771) (.branch 47 (.leaf 2099379076) (.leaf 2049755205))) (.branch 50 (.branch 49 (.leaf 2001354299) (.leaf 1954143575)) (.branch 51 (.leaf 1908091287) (.leaf 1863166677)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1819339942) (.leaf 1776582190)) (.branch 55 (.leaf 1734865406) (.leaf 1694162420))) (.branch 58 (.branch 57 (.leaf 1654446873) (.leaf 1615693186)) (.branch 59 (.leaf 1577876533) (.leaf 1540972813))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1504958622) (.branch 62 (.leaf 1469811231) (.leaf 1435508558))) (.branch 65 (.branch 64 (.leaf 1402029152) (.leaf 1369352165)) (.branch 66 (.leaf 1337457334) (.leaf 1306324963)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1275935901) (.leaf 1246271526)) (.branch 70 (.leaf 1217313728) (.leaf 1189044891))) (.branch 73 (.branch 72 (.leaf 1161447878) (.leaf 1134506014)) (.branch 74 (.leaf 1108203077) (.leaf 1082523277))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1057451247) (.branch 77 (.leaf 1032972028) (.leaf 1009071057))) (.branch 80 (.branch 79 (.leaf 985734157) (.leaf 962947521)) (.branch 81 (.leaf 940697706) (.leaf 918971620)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 897756509) (.leaf 877039953)) (.branch 85 (.leaf 856809850) (.leaf 837054412))) (.branch 88 (.branch 87 (.leaf 817762152) (.leaf 798921880)) (.branch 89 (.leaf 780522689) (.leaf 762553951)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 745005308) (.branch 92 (.leaf 727866664) (.leaf 711128178))) (.branch 95 (.branch 94 (.leaf 694780258) (.leaf 678813553)) (.branch 96 (.leaf 663218946) (.leaf 647987549)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 633110695) (.leaf 618579934)) (.branch 100 (.leaf 604387025) (.leaf 590523934))) (.branch 103 (.branch 102 (.leaf 576982823) (.leaf 563756050)) (.branch 104 (.leaf 550836160) (.leaf 538215884))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 525888129) (.leaf 513845977)) (.branch 108 (.leaf 502082681) (.leaf 490591658))) (.branch 111 (.branch 110 (.leaf 479366484) (.leaf 468400896)) (.branch 112 (.leaf 457688779) (.leaf 447224170)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 437001248) (.leaf 427014336)) (.branch 116 (.leaf 417257892) (.leaf 407726509))) (.branch 119 (.branch 118 (.leaf 398414912) (.leaf 389317950)) (.branch 120 (.leaf 380430598) (.leaf 371747953)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1243).prefactor = (5966962898192207/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1243).cutoff/(generalMeanRows 1243).c)).2 =
    (170352519950669/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1243).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1243).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1243).q*(generalMeanRows 1243).c/2-2 = (29/32:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable415.value]
    have hcontinuation : (generalMeanRows 1243).q*(generalMeanRows 1243).cutoff/2-2 = (332/69:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable414.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1243).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1243

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1243).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1243).criticalRate j.val*(generalMeanRows 1243).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1243).c*(generalMeanRows 1243).criticalPoint j.val)).2-
      (generalMeanRows 1243).J/2-(generalMeanRows 1243).error (generalMeanGrid j.val)+
      (generalMeanRows 1243).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1243).c)).2-
      (generalMeanRows 1243).J/2-(generalMeanRows 1243).error 4 := by
  have he : (generalMeanRows 1243).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1243) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1243)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1243

/-! Kernel-checked entropy margins for general spectral rectangle 1244. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1244
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6469673579) (.branch 2 (.leaf 6302633294) (.leaf 6141287460))) (.branch 5 (.branch 4 (.leaf 5985330392) (.leaf 5834481308)) (.branch 6 (.leaf 5688481737) (.leaf 5547093243)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5410095411) (.leaf 5277284069)) (.branch 10 (.leaf 5148469716) (.leaf 5023476121))) (.branch 13 (.branch 12 (.leaf 4902139082) (.leaf 4784305321)) (.branch 14 (.leaf 4669831495) (.leaf 4558583320))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4450434777) (.branch 17 (.leaf 4345267409) (.leaf 4242969687))) (.branch 20 (.branch 19 (.leaf 4143436439) (.leaf 4046568338)) (.branch 21 (.leaf 3952271440) (.leaf 3860456768)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3771039931) (.leaf 3683940786)) (.branch 25 (.leaf 3599083128) (.leaf 3516394407))) (.branch 28 (.branch 27 (.leaf 3435805475) (.leaf 3357250350)) (.branch 29 (.leaf 3280666008) (.leaf 3205992184)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3133171201) (.branch 32 (.leaf 3062147802) (.leaf 2992869003))) (.branch 35 (.branch 34 (.leaf 2925283958) (.leaf 2859343832)) (.branch 36 (.leaf 2795001685) (.leaf 2732212365)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2670932411) (.leaf 2611119959)) (.branch 40 (.leaf 2552734660) (.leaf 2495737599))) (.branch 43 (.branch 42 (.leaf 2440091227) (.leaf 2385759286)) (.branch 44 (.leaf 2332706755) (.leaf 2280899781))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2230305634) (.branch 47 (.leaf 2180892648) (.leaf 2132630178))) (.branch 50 (.branch 49 (.leaf 2085488551) (.leaf 2039439027)) (.branch 51 (.leaf 1994453759) (.leaf 1950505753)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1907568835) (.leaf 1865617618)) (.branch 55 (.leaf 1824627470) (.leaf 1784574484))) (.branch 58 (.branch 57 (.leaf 1745435451) (.leaf 1707187834)) (.branch 59 (.leaf 1669809739) (.leaf 1633279898))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1597577639) (.branch 62 (.leaf 1562682873) (.leaf 1528576063))) (.branch 65 (.branch 64 (.leaf 1495238215) (.leaf 1462650851)) (.branch 66 (.leaf 1430795998) (.leaf 1399656167)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1369214337) (.leaf 1339453942)) (.branch 70 (.leaf 1310358856) (.leaf 1281913374))) (.branch 73 (.branch 72 (.leaf 1254102206) (.leaf 1226910459)) (.branch 74 (.leaf 1200323626) (.leaf 1174327574))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1148908533) (.branch 77 (.leaf 1124053083) (.leaf 1099748147))) (.branch 80 (.branch 79 (.leaf 1075980979) (.leaf 1052739153)) (.branch 81 (.leaf 1030010554) (.leaf 1007783372)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 986046089) (.leaf 964787473)) (.branch 85 (.leaf 943996569) (.leaf 923662694))) (.branch 88 (.branch 87 (.leaf 903775423) (.leaf 884324589)) (.branch 89 (.leaf 865300271) (.leaf 846692789)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 828492698) (.branch 92 (.leaf 810690780) (.leaf 793278040))) (.branch 95 (.branch 94 (.leaf 776245696) (.leaf 759585180)) (.branch 96 (.leaf 743288125) (.leaf 727346365)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 711751927) (.leaf 696497027)) (.branch 100 (.leaf 681574064) (.leaf 666975617))) (.branch 103 (.branch 102 (.leaf 652694439) (.leaf 638723453)) (.branch 104 (.leaf 625055747) (.leaf 611684572))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 598603334) (.leaf 585805594)) (.branch 108 (.leaf 573285061) (.leaf 561035591))) (.branch 111 (.branch 110 (.leaf 549051181) (.leaf 537325968)) (.branch 112 (.leaf 525854221) (.leaf 514630344)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 503648868) (.leaf 492904449)) (.branch 116 (.leaf 482391866) (.leaf 472106016))) (.branch 119 (.branch 118 (.leaf 462041913) (.leaf 452194686)) (.branch 120 (.leaf 442559572) (.leaf 433131918)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1244).prefactor = (1351567035880261/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1244).cutoff/(generalMeanRows 1244).c)).2 =
    (17182276978753/20000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1244).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1244).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1244).q*(generalMeanRows 1244).c/2-2 = (27/32:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable332.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1244).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1244

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1244).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1244).criticalRate j.val*(generalMeanRows 1244).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1244).c*(generalMeanRows 1244).criticalPoint j.val)).2-
      (generalMeanRows 1244).J/2-(generalMeanRows 1244).error (generalMeanGrid j.val)+
      (generalMeanRows 1244).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1244).c)).2-
      (generalMeanRows 1244).J/2-(generalMeanRows 1244).error 4 := by
  have he : (generalMeanRows 1244).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1244) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1244)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1244

/-! Kernel-checked entropy margins for general spectral rectangle 1245. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1245
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6102248912) (.branch 2 (.leaf 5956720534) (.leaf 5815837129))) (.branch 5 (.branch 4 (.leaf 5679356799) (.leaf 5547057535)) (.branch 6 (.leaf 5418735092) (.leaf 5294201110)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5173281482) (.leaf 5055814907)) (.branch 10 (.leaf 4941651620) (.leaf 4830652265))) (.branch 13 (.branch 12 (.leaf 4722686905) (.leaf 4617634139)) (.branch 14 (.leaf 4515380319) (.leaf 4415818853))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4318849584) (.branch 17 (.leaf 4224378240) (.leaf 4132315931))) (.branch 20 (.branch 19 (.leaf 4042578710) (.leaf 3955087172)) (.branch 21 (.leaf 3869766096) (.leaf 3786544122)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3705353458) (.leaf 3626129621)) (.branch 25 (.leaf 3548811191) (.leaf 3473339602))) (.branch 28 (.branch 27 (.leaf 3399658942) (.leaf 3327715776)) (.branch 29 (.leaf 3257458979) (.leaf 3188839592)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3121810684) (.branch 32 (.leaf 3056327227) (.leaf 2992345982))) (.branch 35 (.branch 34 (.leaf 2929825393) (.leaf 2868725494)) (.branch 36 (.leaf 2809007813) (.leaf 2750635297)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2693572232) (.leaf 2637784171)) (.branch 40 (.leaf 2583237874) (.leaf 2529901240))) (.branch 43 (.branch 42 (.leaf 2477743258) (.leaf 2426733950)) (.branch 44 (.leaf 2376844320) (.leaf 2328046314))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2280312774) (.branch 47 (.leaf 2233617396) (.leaf 2187934695))) (.branch 50 (.branch 49 (.leaf 2143239968) (.leaf 2099509264)) (.branch 51 (.leaf 2056719348) (.leaf 2014847676)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1973872362) (.leaf 1933772158)) (.branch 55 (.leaf 1894526424) (.leaf 1856115109))) (.branch 58 (.branch 57 (.leaf 1818518725) (.leaf 1781718327)) (.branch 59 (.leaf 1745695494) (.leaf 1710432310))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1675911345) (.branch 62 (.leaf 1642115639) (.leaf 1609028683))) (.branch 65 (.branch 64 (.leaf 1576634409) (.leaf 1544917169)) (.branch 66 (.leaf 1513861723) (.leaf 1483453228)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1453677223) (.leaf 1424519616)) (.branch 70 (.leaf 1395966672) (.leaf 1368005005))) (.branch 73 (.branch 72 (.leaf 1340621562) (.leaf 1313803617)) (.branch 74 (.leaf 1287538761) (.leaf 1261814887))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1236620189) (.branch 77 (.leaf 1211943146) (.leaf 1187772516))) (.branch 80 (.branch 79 (.leaf 1164097331) (.leaf 1140906884)) (.branch 81 (.leaf 1118190725) (.leaf 1095938652)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1074140705) (.leaf 1052787158)) (.branch 85 (.leaf 1031868514) (.leaf 1011375499))) (.branch 88 (.branch 87 (.leaf 991299052) (.leaf 971630324)) (.branch 89 (.leaf 952360670) (.leaf 933481645)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 914984995) (.branch 92 (.leaf 896862658) (.leaf 879106752))) (.branch 95 (.branch 94 (.leaf 861709576) (.leaf 844663602)) (.branch 96 (.leaf 827961473) (.leaf 811595996)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 795560140) (.leaf 779847030)) (.branch 100 (.leaf 764449944) (.leaf 749362312))) (.branch 103 (.branch 102 (.leaf 734577705) (.leaf 720089839)) (.branch 104 (.leaf 705892569) (.leaf 691979882))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 678345899) (.leaf 664984869)) (.branch 108 (.leaf 651891166) (.leaf 639059286))) (.branch 111 (.branch 110 (.leaf 626483847) (.leaf 614159580)) (.branch 112 (.leaf 602081332) (.leaf 590244061)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 578642833) (.leaf 567272820)) (.branch 116 (.leaf 556129297) (.leaf 545207641))) (.branch 119 (.branch 118 (.leaf 534503327) (.leaf 524011928)) (.branch 120 (.leaf 513729108) (.leaf 503650626)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1245).prefactor = (4664409679116481/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1245).cutoff/(generalMeanRows 1245).c)).2 =
    (193775931612679/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1245).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1245).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1245).q*(generalMeanRows 1245).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1245).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1245

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1245).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1245).criticalRate j.val*(generalMeanRows 1245).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1245).c*(generalMeanRows 1245).criticalPoint j.val)).2-
      (generalMeanRows 1245).J/2-(generalMeanRows 1245).error (generalMeanGrid j.val)+
      (generalMeanRows 1245).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1245).c)).2-
      (generalMeanRows 1245).J/2-(generalMeanRows 1245).error 4 := by
  have he : (generalMeanRows 1245).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1245) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1245)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1245

/-! Kernel-checked entropy margins for general spectral rectangle 1246. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1246
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4814048860) (.branch 2 (.leaf 4669614163) (.leaf 4530432946))) (.branch 5 (.branch 4 (.leaf 4396233635) (.leaf 4266765739)) (.branch 6 (.leaf 4141797666) (.leaf 4021114801)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3904517818) (.leaf 3791821192)) (.branch 10 (.leaf 3682851886) (.leaf 3577448187))) (.branch 13 (.branch 12 (.leaf 3475458671) (.leaf 3376741292)) (.branch 14 (.leaf 3281162562) (.leaf 3188596823))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3098925597) (.branch 17 (.leaf 3012037002) (.leaf 2927825228))) (.branch 20 (.branch 19 (.leaf 2846190069) (.leaf 2767036497)) (.branch 21 (.leaf 2690274282) (.leaf 2615817642)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2543584935) (.leaf 2473498371)) (.branch 25 (.leaf 2405483755) (.leaf 2339470252))) (.branch 28 (.branch 27 (.leaf 2275390171) (.leaf 2213178769)) (.branch 29 (.leaf 2152774072) (.leaf 2094116709)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2037149760) (.branch 32 (.leaf 1981818617) (.leaf 1928070855))) (.branch 35 (.branch 34 (.leaf 1875856113) (.leaf 1825125985)) (.branch 36 (.leaf 1775833915) (.leaf 1727935103)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1681386420) (.leaf 1636146323)) (.branch 40 (.leaf 1592174778) (.leaf 1549433189))) (.branch 43 (.branch 42 (.leaf 1507884334) (.leaf 1467492296)) (.branch 44 (.leaf 1428222413) (.leaf 1390041212))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1352916367) (.branch 47 (.leaf 1316816644) (.leaf 1281711859))) (.branch 50 (.branch 49 (.leaf 1247572828) (.leaf 1214371334)) (.branch 51 (.leaf 1182080082) (.leaf 1150672666)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1120123532) (.leaf 1090407945)) (.branch 55 (.leaf 1061501958) (.leaf 1033382382))) (.branch 58 (.branch 57 (.leaf 1006026757) (.leaf 979413328)) (.branch 59 (.leaf 953521014) (.leaf 928329388))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 903818651) (.branch 62 (.leaf 879969610) (.leaf 856763657))) (.branch 65 (.branch 64 (.leaf 834182750) (.leaf 812209390)) (.branch 66 (.leaf 790826604) (.leaf 770017930)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 749767392) (.leaf 730059494)) (.branch 70 (.leaf 710879195) (.leaf 692211898))) (.branch 73 (.branch 72 (.leaf 674043436) (.leaf 656360055)) (.branch 74 (.leaf 639148405) (.leaf 622395522))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 606088819) (.branch 77 (.leaf 590216072) (.leaf 574765411))) (.branch 80 (.branch 79 (.leaf 559725305) (.leaf 545084556)) (.branch 81 (.leaf 530832285) (.leaf 516957923)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 503451201) (.leaf 490302144)) (.branch 85 (.leaf 477501057) (.leaf 465038520))) (.branch 88 (.branch 87 (.leaf 452905377) (.leaf 441092733)) (.branch 89 (.leaf 429591938) (.leaf 418394588)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 407492513) (.branch 92 (.leaf 396877769) (.leaf 386542637))) (.branch 95 (.branch 94 (.leaf 376479608) (.leaf 366681385)) (.branch 96 (.leaf 357140872) (.leaf 347851169)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 338805567) (.leaf 329997541)) (.branch 100 (.leaf 321420747) (.leaf 313069014))) (.branch 103 (.branch 102 (.leaf 304936342) (.leaf 297016893)) (.branch 104 (.leaf 289304992) (.leaf 281795116))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 274481894) (.leaf 267360103)) (.branch 108 (.leaf 260424659) (.leaf 253670620))) (.branch 111 (.branch 110 (.leaf 247093174) (.leaf 240687643)) (.branch 112 (.leaf 234449475) (.leaf 228374240)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 222457629) (.leaf 216695448)) (.branch 116 (.leaf 211083619) (.leaf 205618170))) (.branch 119 (.branch 118 (.leaf 200295240) (.leaf 195111069)) (.branch 120 (.leaf 190061999) (.leaf 185144471)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1246).prefactor = (4827417770817311/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1246).cutoff/(generalMeanRows 1246).c)).2 =
    (440107010488869/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1246).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1246).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1246).q*(generalMeanRows 1246).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1246).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1246

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1246).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1246).criticalRate j.val*(generalMeanRows 1246).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1246).c*(generalMeanRows 1246).criticalPoint j.val)).2-
      (generalMeanRows 1246).J/2-(generalMeanRows 1246).error (generalMeanGrid j.val)+
      (generalMeanRows 1246).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1246).c)).2-
      (generalMeanRows 1246).J/2-(generalMeanRows 1246).error 4 := by
  have he : (generalMeanRows 1246).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1246) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1246)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1246

/-! Kernel-checked entropy margins for general spectral rectangle 1247. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1247
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5313863232) (.branch 2 (.leaf 5162215098) (.leaf 5015911685))) (.branch 5 (.branch 4 (.leaf 4874677427) (.leaf 4738258416)) (.branch 6 (.leaf 4606420135) (.leaf 4478945469)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4355632960) (.leaf 4236295267)) (.branch 10 (.leaf 4120757807) (.leaf 4008857553))) (.branch 13 (.branch 12 (.leaf 3900441969) (.leaf 3795368064)) (.branch 14 (.leaf 3693501550) (.leaf 3594716092))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3498892637) (.branch 17 (.leaf 3405918814) (.leaf 3315688399))) (.branch 20 (.branch 19 (.leaf 3228100828) (.leaf 3143060764)) (.branch 21 (.leaf 3060477707) (.leaf 2980265635)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2902342690) (.leaf 2826630882)) (.branch 25 (.leaf 2753055830) (.leaf 2681546519))) (.branch 28 (.branch 27 (.leaf 2612035081) (.leaf 2544456596)) (.branch 29 (.leaf 2478748913) (.leaf 2414852475)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2352710172) (.branch 32 (.leaf 2292267198) (.leaf 2233470916))) (.branch 35 (.branch 34 (.leaf 2176270746) (.leaf 2120618049)) (.branch 36 (.leaf 2066466024) (.leaf 2013769614)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1962485418) (.leaf 1912571608)) (.branch 40 (.leaf 1863987852) (.leaf 1816695244))) (.branch 43 (.branch 42 (.leaf 1770656232) (.leaf 1725834566)) (.branch 44 (.leaf 1682195227) (.leaf 1639704380))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1598329322) (.branch 47 (.leaf 1558038429) (.leaf 1518801116))) (.branch 50 (.branch 49 (.leaf 1480587788) (.leaf 1443369803)) (.branch 51 (.leaf 1407119435) (.leaf 1371809833)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1337414991) (.leaf 1303909711)) (.branch 55 (.leaf 1271269577) (.leaf 1239470921))) (.branch 58 (.branch 57 (.leaf 1208490798) (.leaf 1178306960)) (.branch 59 (.leaf 1148897826) (.leaf 1120242464))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1092320564) (.branch 62 (.leaf 1065112416) (.leaf 1038598893))) (.branch 65 (.branch 64 (.leaf 1012761425) (.leaf 987581985)) (.branch 66 (.leaf 963043067) (.leaf 939127673)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 915819290) (.leaf 893101880)) (.branch 70 (.leaf 870959859) (.leaf 849378086))) (.branch 73 (.branch 72 (.leaf 828341849) (.leaf 807836847)) (.branch 74 (.leaf 787849183) (.leaf 768365345))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 749372200) (.branch 77 (.leaf 730856976) (.leaf 712807257))) (.branch 80 (.branch 79 (.leaf 695210968) (.leaf 678056364)) (.branch 81 (.leaf 661332023) (.leaf 645026836)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 629129994) (.leaf 613630983)) (.branch 85 (.leaf 598519574) (.leaf 583785813))) (.branch 88 (.branch 87 (.leaf 569420014) (.leaf 555412753)) (.branch 89 (.leaf 541754857) (.leaf 528437399)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 515451690) (.branch 92 (.leaf 502789273) (.leaf 490441914))) (.branch 95 (.branch 94 (.leaf 478401599) (.leaf 466660526)) (.branch 96 (.leaf 455211098) (.leaf 444045919)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 433157787) (.leaf 422539690)) (.branch 100 (.leaf 412184798) (.leaf 402086463))) (.branch 103 (.branch 102 (.leaf 392238207) (.leaf 382633723)) (.branch 104 (.leaf 373266868) (.leaf 364131659))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 355222267) (.leaf 346533016)) (.branch 108 (.leaf 338058376) (.leaf 329792959))) (.branch 111 (.branch 110 (.leaf 321731518) (.leaf 313868940)) (.branch 112 (.leaf 306200243) (.leaf 298720576)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 291425209) (.leaf 284309535)) (.branch 116 (.leaf 277369065) (.leaf 270599426))) (.branch 119 (.branch 118 (.leaf 263996355) (.leaf 257555698)) (.branch 120 (.leaf 251273408) (.leaf 245145541)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1247).prefactor = (4996122540080347/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1247).cutoff/(generalMeanRows 1247).c)).2 =
    (900622892608943/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1247).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1247).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1247).q*(generalMeanRows 1247).c/2-2 = (1553/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable418.value]
    have hcontinuation : (generalMeanRows 1247).q*(generalMeanRows 1247).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1247).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1247

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1247).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1247).criticalRate j.val*(generalMeanRows 1247).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1247).c*(generalMeanRows 1247).criticalPoint j.val)).2-
      (generalMeanRows 1247).J/2-(generalMeanRows 1247).error (generalMeanGrid j.val)+
      (generalMeanRows 1247).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1247).c)).2-
      (generalMeanRows 1247).J/2-(generalMeanRows 1247).error 4 := by
  have he : (generalMeanRows 1247).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1247) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1247)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1247

/-! Kernel-checked entropy margins for general spectral rectangle 1248. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1248
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5786249654) (.branch 2 (.leaf 5629597624) (.leaf 5478295724))) (.branch 5 (.branch 4 (.leaf 5332068138) (.leaf 5190661018)) (.branch 6 (.leaf 5053840162) (.leaf 4921388986)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4793106740) (.leaf 4668806931)) (.branch 10 (.leaf 4548315942) (.leaf 4431471803))) (.branch 13 (.branch 12 (.leaf 4318123103) (.leaf 4208128031)) (.branch 14 (.leaf 4101353515) (.leaf 3997674460))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3896973064) (.branch 17 (.leaf 3799138214) (.leaf 3704064934))) (.branch 20 (.branch 19 (.leaf 3611653899) (.leaf 3521810991)) (.branch 21 (.leaf 3434446906) (.leaf 3349476794)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3266819935) (.leaf 3186399445)) (.branch 25 (.leaf 3108142012) (.leaf 3031977655))) (.branch 28 (.branch 27 (.leaf 2957839500) (.leaf 2885663583)) (.branch 29 (.leaf 2815388666) (.leaf 2746956065)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2680309504) (.branch 32 (.leaf 2615394966) (.leaf 2552160568))) (.branch 35 (.branch 34 (.leaf 2490556438) (.leaf 2430534608)) (.branch 36 (.leaf 2372048906) (.leaf 2315054867)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2259509645) (.leaf 2205371925)) (.branch 40 (.leaf 2152601856) (.leaf 2101160974))) (.branch 43 (.branch 42 (.leaf 2051012138) (.leaf 2002119468)) (.branch 44 (.leaf 1954448290) (.leaf 1907965077))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1862637404) (.branch 47 (.leaf 1818433895) (.leaf 1775324182))) (.branch 50 (.branch 49 (.leaf 1733278861) (.leaf 1692269455)) (.branch 51 (.leaf 1652268371) (.leaf 1613248871)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1575185035) (.leaf 1538051727)) (.branch 55 (.leaf 1501824572) (.leaf 1466479920))) (.branch 58 (.branch 57 (.leaf 1431994823) (.leaf 1398347008)) (.branch 59 (.leaf 1365514854) (.leaf 1333477366))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1302214156) (.branch 62 (.leaf 1271705419) (.leaf 1241931913))) (.branch 65 (.branch 64 (.leaf 1212874943) (.leaf 1184516338)) (.branch 66 (.leaf 1156838437) (.leaf 1129824070)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1103456541) (.leaf 1077719617)) (.branch 70 (.leaf 1052597507) (.leaf 1028074854))) (.branch 73 (.branch 72 (.leaf 1004136716) (.leaf 980768555)) (.branch 74 (.leaf 957956226) (.leaf 935685961))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 913944362) (.branch 77 (.leaf 892718386) (.leaf 871995337))) (.branch 80 (.branch 79 (.leaf 851762852) (.leaf 832008896)) (.branch 81 (.leaf 812721747) (.leaf 793889991)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 775502510) (.leaf 757548476)) (.branch 85 (.leaf 740017341) (.leaf 722898828))) (.branch 88 (.branch 87 (.leaf 706182925) (.leaf 689859877)) (.branch 89 (.leaf 673920179) (.leaf 658354568)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 643154017) (.branch 92 (.leaf 628309728) (.leaf 613813126))) (.branch 95 (.branch 94 (.leaf 599655851) (.leaf 585829757)) (.branch 96 (.leaf 572326899) (.leaf 559139535)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 546260114) (.leaf 533681276)) (.branch 100 (.leaf 521395842) (.leaf 509396813))) (.branch 103 (.branch 102 (.leaf 497677364) (.leaf 486230839)) (.branch 104 (.leaf 475050746) (.leaf 464130754))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 453464688) (.leaf 443046526)) (.branch 108 (.leaf 432870391) (.leaf 422930553))) (.branch 111 (.branch 110 (.leaf 413221421) (.leaf 403737541)) (.branch 112 (.leaf 394473593) (.leaf 385424386)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 376584854) (.leaf 367950056)) (.branch 116 (.leaf 359515172) (.leaf 351275495))) (.branch 119 (.branch 118 (.leaf 343226436) (.leaf 335363514)) (.branch 120 (.leaf 327682358) (.leaf 320178703)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1248).prefactor = (2550081169374849/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1248).cutoff/(generalMeanRows 1248).c)).2 =
    (184291395902357/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1248).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1248).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1248).q*(generalMeanRows 1248).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1248).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1248

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1248).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1248).criticalRate j.val*(generalMeanRows 1248).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1248).c*(generalMeanRows 1248).criticalPoint j.val)).2-
      (generalMeanRows 1248).J/2-(generalMeanRows 1248).error (generalMeanGrid j.val)+
      (generalMeanRows 1248).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1248).c)).2-
      (generalMeanRows 1248).J/2-(generalMeanRows 1248).error 4 := by
  have he : (generalMeanRows 1248).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1248) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1248)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1248

/-! Kernel-checked entropy margins for general spectral rectangle 1249. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1249
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5790990332) (.branch 2 (.leaf 5632512901) (.leaf 5479482013))) (.branch 5 (.branch 4 (.leaf 5331616937) (.leaf 5188659238)) (.branch 6 (.leaf 5050370429) (.leaf 4916529913)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4786933174) (.leaf 4661390179)) (.branch 10 (.leaf 4539723979) (.leaf 4421769461))) (.branch 13 (.branch 12 (.leaf 4307372246) (.leaf 4196387716)) (.branch 14 (.leaf 4088680142) (.leaf 3984121909))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3882592825) (.branch 17 (.leaf 3783979502) (.leaf 3688174804))) (.branch 20 (.branch 19 (.leaf 3595077348) (.leaf 3504591056)) (.branch 21 (.leaf 3416624754) (.leaf 3331091808)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3247909793) (.leaf 3167000197)) (.branch 25 (.leaf 3088288153) (.leaf 3011702188))) (.branch 28 (.branch 27 (.leaf 2937174004) (.leaf 2864638269)) (.branch 29 (.leaf 2794032438) (.leaf 2725296574)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2658373197) (.branch 32 (.leaf 2593207137) (.leaf 2529745405))) (.branch 35 (.branch 34 (.leaf 2467937066) (.leaf 2407733132)) (.branch 36 (.leaf 2349086454) (.leaf 2291951626)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2236284896) (.leaf 2182044085)) (.branch 40 (.leaf 2129188506) (.leaf 2077678892))) (.branch 43 (.branch 42 (.leaf 2027477334) (.leaf 1978547212)) (.branch 44 (.leaf 1930853137) (.leaf 1884360899))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1839037415) (.branch 47 (.leaf 1794850676) (.leaf 1751769705))) (.branch 50 (.branch 49 (.leaf 1709764514) (.leaf 1668806061)) (.branch 51 (.leaf 1628866214) (.leaf 1589917713)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1551934138) (.leaf 1514889873)) (.branch 55 (.leaf 1478760079) (.leaf 1443520661))) (.branch 58 (.branch 57 (.leaf 1409148244) (.leaf 1375620145)) (.branch 59 (.leaf 1342914347) (.leaf 1311009474))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1279884774) (.branch 62 (.leaf 1249520091) (.leaf 1219895847))) (.branch 65 (.branch 64 (.leaf 1190993021) (.leaf 1162793133)) (.branch 66 (.leaf 1135278222) (.leaf 1108430832)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1082233991) (.leaf 1056671202)) (.branch 70 (.leaf 1031726421) (.leaf 1007384045))) (.branch 73 (.branch 72 (.leaf 983628901) (.leaf 960446225)) (.branch 74 (.leaf 937821658) (.leaf 915741227))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 894191336) (.branch 77 (.leaf 873158752) (.leaf 852630598))) (.branch 80 (.branch 79 (.leaf 832594338) (.leaf 813037770)) (.branch 81 (.leaf 793949015) (.leaf 775316504)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 757128977) (.leaf 739375464)) (.branch 85 (.leaf 722045285) (.leaf 705128036))) (.branch 88 (.branch 87 (.leaf 688613584) (.leaf 672492059)) (.branch 89 (.leaf 656753846) (.leaf 641389575)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 626390119) (.branch 92 (.leaf 611746586) (.leaf 597450309))) (.branch 95 (.branch 94 (.leaf 583492843) (.leaf 569865958)) (.branch 96 (.leaf 556561633) (.leaf 543572050)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 530889589) (.leaf 518506823)) (.branch 100 (.leaf 506416510) (.leaf 494611592))) (.branch 103 (.branch 102 (.leaf 483085187) (.leaf 471830585)) (.branch 104 (.leaf 460841246) (.leaf 450110791))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 439633001) (.leaf 429401810)) (.branch 108 (.leaf 419411306) (.leaf 409655719))) (.branch 111 (.branch 110 (.leaf 400129425) (.leaf 390826939)) (.branch 112 (.leaf 381742911) (.leaf 372872121)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 364209480) (.leaf 355750022)) (.branch 116 (.leaf 347488906) (.leaf 339421406))) (.branch 119 (.branch 118 (.leaf 331542913) (.leaf 323848932)) (.branch 120 (.leaf 316335076) (.leaf 308997066)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1249).prefactor = (2585361534938461/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1249).cutoff/(generalMeanRows 1249).c)).2 =
    (917255292658087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1249).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1249).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1249).q*(generalMeanRows 1249).c/2-2 = (7373/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable419.value]
    have hcontinuation : (generalMeanRows 1249).q*(generalMeanRows 1249).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1249).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1249

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1249).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1249).criticalRate j.val*(generalMeanRows 1249).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1249).c*(generalMeanRows 1249).criticalPoint j.val)).2-
      (generalMeanRows 1249).J/2-(generalMeanRows 1249).error (generalMeanGrid j.val)+
      (generalMeanRows 1249).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1249).c)).2-
      (generalMeanRows 1249).J/2-(generalMeanRows 1249).error 4 := by
  have he : (generalMeanRows 1249).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1249) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1249)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1249

/-! Kernel-checked entropy margins for general spectral rectangle 1250. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1250
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5993369271) (.branch 2 (.leaf 5829353497) (.leaf 5670974607))) (.branch 5 (.branch 4 (.leaf 5517942059) (.leaf 5369988387)) (.branch 6 (.leaf 5226866771) (.leaf 5088348903)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4954223119) (.leaf 4824292748)) (.branch 10 (.leaf 4698374654) (.leaf 4576297954))) (.branch 13 (.branch 12 (.leaf 4457902876) (.leaf 4343039748)) (.branch 14 (.leaf 4231568095) (.leaf 4123355843))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4018278601) (.branch 17 (.leaf 3916219018) (.leaf 3817066213))) (.branch 20 (.branch 19 (.leaf 3720715261) (.leaf 3627066726)) (.branch 21 (.leaf 3536026247) (.leaf 3447504163)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3361415169) (.leaf 3277678010)) (.branch 25 (.leaf 3196215199) (.leaf 3116952769))) (.branch 28 (.branch 27 (.leaf 3039820032) (.leaf 2964749377)) (.branch 29 (.leaf 2891676069) (.leaf 2820538078)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2751275916) (.branch 32 (.leaf 2683832485) (.leaf 2618152942))) (.branch 35 (.branch 34 (.leaf 2554184575) (.leaf 2491876681)) (.branch 36 (.leaf 2431180465) (.leaf 2372048934)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2314436808) (.leaf 2258300432)) (.branch 40 (.leaf 2203597698) (.leaf 2150287967))) (.branch 43 (.branch 42 (.leaf 2098332005) (.leaf 2047691911)) (.branch 44 (.leaf 1998331061) (.leaf 1950214050))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1903306637) (.branch 47 (.leaf 1857575694) (.leaf 1812989164))) (.branch 50 (.branch 49 (.leaf 1769516008) (.leaf 1727126172)) (.branch 51 (.leaf 1685790539) (.leaf 1645480897)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1606169902) (.leaf 1567831043)) (.branch 55 (.leaf 1530438613) (.leaf 1493967677))) (.branch 58 (.branch 57 (.leaf 1458394040) (.leaf 1423694228)) (.branch 59 (.leaf 1389845452) (.leaf 1356825594))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1324613173) (.branch 62 (.leaf 1293187329) (.leaf 1262527800))) (.branch 65 (.branch 64 (.leaf 1232614901) (.leaf 1203429506)) (.branch 66 (.leaf 1174953025) (.leaf 1147167394)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1120055047) (.leaf 1093598909)) (.branch 70 (.leaf 1067782378) (.leaf 1042589304))) (.branch 73 (.branch 72 (.leaf 1018003984) (.leaf 994011139)) (.branch 74 (.leaf 970595906) (.leaf 947743826))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 925440826) (.branch 77 (.leaf 903673212) (.leaf 882427656))) (.branch 80 (.branch 79 (.leaf 861691185) (.leaf 841451170)) (.branch 81 (.leaf 821695315) (.leaf 802411651)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 783588520) (.leaf 765214571)) (.branch 85 (.leaf 747278751) (.leaf 729770291))) (.branch 88 (.branch 87 (.leaf 712678706) (.leaf 695993779)) (.branch 89 (.leaf 679705558) (.leaf 663804349)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 648280705) (.branch 92 (.leaf 633125421) (.leaf 618329529))) (.branch 95 (.branch 94 (.leaf 603884288) (.leaf 589781182)) (.branch 96 (.leaf 576011908) (.leaf 562568375)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 549442698) (.leaf 536627188)) (.branch 100 (.leaf 524114352) (.leaf 511896885))) (.branch 103 (.branch 102 (.leaf 499967665) (.leaf 488319747)) (.branch 104 (.leaf 476946361) (.leaf 465840907))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 454996947) (.leaf 444408205)) (.branch 108 (.leaf 434068559) (.leaf 423972042))) (.branch 111 (.branch 110 (.leaf 414112831) (.leaf 404485249)) (.branch 112 (.leaf 395083759) (.leaf 385902960)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 376937584) (.leaf 368182492)) (.branch 116 (.leaf 359632673) (.leaf 351283236))) (.branch 119 (.branch 118 (.leaf 343129412) (.leaf 335166547)) (.branch 120 (.leaf 327390103) (.leaf 319795650)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1250).prefactor = (1070285080114447/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1250).cutoff/(generalMeanRows 1250).c)).2 =
    (917255292658087/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1250).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1250).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1250).q*(generalMeanRows 1250).c/2-2 = (7373/8000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable419.value]
    have hcontinuation : (generalMeanRows 1250).q*(generalMeanRows 1250).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1250).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1250

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1250).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1250).criticalRate j.val*(generalMeanRows 1250).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1250).c*(generalMeanRows 1250).criticalPoint j.val)).2-
      (generalMeanRows 1250).J/2-(generalMeanRows 1250).error (generalMeanGrid j.val)+
      (generalMeanRows 1250).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1250).c)).2-
      (generalMeanRows 1250).J/2-(generalMeanRows 1250).error 4 := by
  have he : (generalMeanRows 1250).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1250) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1250)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1250

/-! Kernel-checked entropy margins for general spectral rectangle 1251. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1251
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6448085960) (.branch 2 (.leaf 6277295551) (.leaf 6112265612))) (.branch 5 (.branch 4 (.leaf 5952698955) (.leaf 5798322194)) (.branch 6 (.leaf 5648883222) (.leaf 5504149007)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5363903653) (.leaf 5227946686)) (.branch 10 (.leaf 5096091558) (.leaf 4968164305))) (.branch 13 (.branch 12 (.leaf 4844002374) (.leaf 4723453575)) (.branch 14 (.leaf 4606375154) (.leaf 4492632957))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4382100699) (.branch 17 (.leaf 4274659298) (.leaf 4170196285))) (.branch 20 (.branch 19 (.leaf 4068605273) (.leaf 3969785478)) (.branch 21 (.leaf 3873641293) (.leaf 3780081896)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3689020904) (.leaf 3600376051)) (.branch 25 (.leaf 3514068905) (.leaf 3430024604))) (.branch 28 (.branch 27 (.leaf 3348171618) (.leaf 3268441536)) (.branch 29 (.leaf 3190768863) (.leaf 3115090842)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3041347287) (.branch 32 (.leaf 2969480431) (.leaf 2899434787))) (.branch 35 (.branch 34 (.leaf 2831157016) (.leaf 2764595812)) (.branch 36 (.leaf 2699701789) (.leaf 2636427379)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2574726741) (.leaf 2514555670)) (.branch 40 (.leaf 2455871518) (.leaf 2398633117))) (.branch 43 (.branch 42 (.leaf 2342800706) (.leaf 2288335871)) (.branch 44 (.leaf 2235201477) (.leaf 2183361615))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2132781544) (.branch 47 (.leaf 2083427642) (.leaf 2035267360))) (.branch 50 (.branch 49 (.leaf 1988269173) (.leaf 1942402539)) (.branch 51 (.leaf 1897637862) (.leaf 1853946449)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1811300481) (.leaf 1769672971)) (.branch 55 (.leaf 1729037740) (.leaf 1689369379))) (.branch 58 (.branch 57 (.leaf 1650643228) (.leaf 1612835343)) (.branch 59 (.leaf 1575922470) (.leaf 1539882026))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1504692067) (.branch 62 (.leaf 1470331273) (.leaf 1436778922))) (.branch 65 (.branch 64 (.leaf 1404014871) (.leaf 1372019537)) (.branch 66 (.leaf 1340773877) (.leaf 1310259370)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1280458002) (.leaf 1251352248)) (.branch 70 (.leaf 1222925055) (.leaf 1195159831))) (.branch 73 (.branch 72 (.leaf 1168040425) (.leaf 1141551119)) (.branch 74 (.leaf 1115676608) (.leaf 1090401995))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1065712771) (.branch 77 (.leaf 1041594809) (.leaf 1018034348))) (.branch 80 (.branch 79 (.leaf 995017987) (.leaf 972532669)) (.branch 81 (.leaf 950565676) (.leaf 929104613)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 908137406) (.leaf 887652287)) (.branch 85 (.leaf 867637787) (.leaf 848082728))) (.branch 88 (.branch 87 (.leaf 828976214) (.leaf 810307624)) (.branch 89 (.leaf 792066604) (.leaf 774243057)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 756827141) (.branch 92 (.leaf 739809257) (.leaf 723180045))) (.branch 95 (.branch 94 (.leaf 706930379) (.leaf 691051354)) (.branch 96 (.leaf 675534288) (.leaf 660370713)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 645552365) (.leaf 631071187)) (.branch 100 (.leaf 616919315) (.leaf 603089079))) (.branch 103 (.branch 102 (.leaf 589572994) (.leaf 576363758)) (.branch 104 (.leaf 563454246) (.leaf 550837505))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 538506748) (.leaf 526455354)) (.branch 108 (.leaf 514676861) (.leaf 503164962))) (.branch 111 (.branch 110 (.leaf 491913499) (.leaf 480916464)) (.branch 112 (.leaf 470167992) (.leaf 459662357)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 449393970) (.leaf 439357375)) (.branch 116 (.leaf 429547246) (.leaf 419958382))) (.branch 119 (.branch 118 (.leaf 410585706) (.leaf 401424262)) (.branch 120 (.leaf 392469208) (.leaf 383715820)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1251).prefactor = (553844277306681/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1251).cutoff/(generalMeanRows 1251).c)).2 =
    (116239211191251/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1251).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1251).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1251).q*(generalMeanRows 1251).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1251).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1251

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1251).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1251).criticalRate j.val*(generalMeanRows 1251).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1251).c*(generalMeanRows 1251).criticalPoint j.val)).2-
      (generalMeanRows 1251).J/2-(generalMeanRows 1251).error (generalMeanGrid j.val)+
      (generalMeanRows 1251).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1251).c)).2-
      (generalMeanRows 1251).J/2-(generalMeanRows 1251).error 4 := by
  have he : (generalMeanRows 1251).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1251) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1251)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1251

/-! Kernel-checked entropy margins for general spectral rectangle 1252. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1252
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7028077194) (.branch 2 (.leaf 6850165374) (.leaf 6678107196))) (.branch 5 (.branch 4 (.leaf 6511599792) (.leaf 6350364827)) (.branch 6 (.leaf 6194145892) (.leaf 6042706211)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5895826633) (.leaf 5753303861)) (.branch 10 (.leaf 5614948893) (.leaf 5480585641))) (.branch 13 (.branch 12 (.leaf 5350049716) (.leaf 5223187338)) (.branch 14 (.leaf 5099854380) (.leaf 4979915508))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4863243422) (.branch 17 (.leaf 4749718167) (.leaf 4639226528))) (.branch 20 (.branch 19 (.leaf 4531661478) (.leaf 4426921689)) (.branch 21 (.leaf 4324911091) (.leaf 4225538466)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4128717094) (.leaf 4034364427)) (.branch 25 (.leaf 3942401789) (.leaf 3852754112))) (.branch 28 (.branch 27 (.leaf 3765349691) (.leaf 3680119960)) (.branch 29 (.leaf 3596999294) (.leaf 3515924820)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3436836246) (.branch 32 (.leaf 3359675712) (.leaf 3284387640))) (.branch 35 (.branch 34 (.leaf 3210918607) (.leaf 3139217225)) (.branch 36 (.leaf 3069234022) (.leaf 3000921348)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2934233272) (.leaf 2869125499)) (.branch 40 (.leaf 2805555283) (.leaf 2743481352))) (.branch 43 (.branch 42 (.leaf 2682863837) (.leaf 2623664207)) (.branch 44 (.leaf 2565845202) (.leaf 2509370781))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2454206061) (.branch 47 (.leaf 2400317273) (.leaf 2347671707))) (.branch 50 (.branch 49 (.leaf 2296237672) (.leaf 2245984451)) (.branch 51 (.leaf 2196882263) (.leaf 2148902222)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2102016305) (.leaf 2056197317)) (.branch 55 (.leaf 2011418856) (.leaf 1967655289))) (.branch 58 (.branch 57 (.leaf 1924881718) (.leaf 1883073956)) (.branch 59 (.leaf 1842208499) (.leaf 1802262502))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1763213757) (.branch 62 (.leaf 1725040669) (.leaf 1687722238))) (.branch 65 (.branch 64 (.leaf 1651238032) (.leaf 1615568176)) (.branch 66 (.leaf 1580693327) (.leaf 1546594661)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1513253852) (.leaf 1480653059)) (.branch 70 (.leaf 1448774909) (.leaf 1417602484))) (.branch 73 (.branch 72 (.leaf 1387119304) (.leaf 1357309314)) (.branch 74 (.leaf 1328156874) (.leaf 1299646742))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1271764066) (.branch 77 (.leaf 1244494367) (.leaf 1217823534))) (.branch 80 (.branch 79 (.leaf 1191737810) (.leaf 1166223782)) (.branch 81 (.leaf 1141268370) (.leaf 1116858819)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1092982690) (.leaf 1069627848)) (.branch 85 (.leaf 1046782459) (.leaf 1024434974))) (.branch 88 (.branch 87 (.leaf 1002574129) (.leaf 981188930)) (.branch 89 (.leaf 960268652) (.leaf 939802826)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 919781237) (.branch 92 (.leaf 900193913) (.leaf 881031120))) (.branch 95 (.branch 94 (.leaf 862283356) (.leaf 843941348)) (.branch 96 (.leaf 825996037) (.leaf 808438582)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 791260350) (.leaf 774452909)) (.branch 100 (.leaf 758008026) (.leaf 741917661))) (.branch 103 (.branch 102 (.leaf 726173960) (.leaf 710769255)) (.branch 104 (.leaf 695696051) (.leaf 680947032))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 666515048) (.leaf 652393115)) (.branch 108 (.leaf 638574409) (.leaf 625052265))) (.branch 111 (.branch 110 (.leaf 611820170) (.leaf 598871758)) (.branch 112 (.leaf 586200811) (.leaf 573801253)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 561667145) (.leaf 549792683)) (.branch 116 (.leaf 538172197) (.leaf 526800142))) (.branch 119 (.branch 118 (.leaf 515671102) (.leaf 504779781)) (.branch 120 (.leaf 494121004) (.leaf 483689711)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1252).prefactor = (2865997940217569/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1252).cutoff/(generalMeanRows 1252).c)).2 =
    (189408945892039/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1252).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1252).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1252).q*(generalMeanRows 1252).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1252).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1252

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1252).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1252).criticalRate j.val*(generalMeanRows 1252).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1252).c*(generalMeanRows 1252).criticalPoint j.val)).2-
      (generalMeanRows 1252).J/2-(generalMeanRows 1252).error (generalMeanGrid j.val)+
      (generalMeanRows 1252).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1252).c)).2-
      (generalMeanRows 1252).J/2-(generalMeanRows 1252).error 4 := by
  have he : (generalMeanRows 1252).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1252) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1252)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1252

/-! Kernel-checked entropy margins for general spectral rectangle 1253. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1253
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7684429600) (.branch 2 (.leaf 7503422552) (.leaf 7328158596))) (.branch 5 (.branch 4 (.leaf 7158338137) (.leaf 6993686291)) (.branch 6 (.leaf 6833950230) (.leaf 6678896861)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6528310787) (.leaf 6381992506)) (.branch 10 (.leaf 6239756834) (.leaf 6101431508))) (.branch 13 (.branch 12 (.leaf 5966855948) (.leaf 5835880162)) (.branch 14 (.leaf 5708363773) (.leaf 5584175153))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 5463190650) (.branch 17 (.leaf 5345293902) (.leaf 5230375219))) (.branch 20 (.branch 19 (.leaf 5118331031) (.leaf 5009063392)) (.branch 21 (.leaf 4902479536) (.leaf 4798491475)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4697015636) (.leaf 4597972536)) (.branch 25 (.leaf 4501286483) (.leaf 4406885312))) (.branch 28 (.branch 27 (.leaf 4314700136) (.leaf 4224665129)) (.branch 29 (.leaf 4136717319) (.leaf 4050796408)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3966844601) (.branch 32 (.leaf 3884806450) (.leaf 3804628716))) (.branch 35 (.branch 34 (.leaf 3726260237) (.leaf 3649651806)) (.branch 36 (.leaf 3574756064) (.leaf 3501527397)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 3429921840) (.leaf 3359896992)) (.branch 40 (.leaf 3291411934) (.leaf 3224427153))) (.branch 43 (.branch 42 (.leaf 3158904476) (.leaf 3094806999)) (.branch 44 (.leaf 3032099031) (.leaf 2970746036))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2910714579) (.branch 47 (.leaf 2851972278) (.leaf 2794487755))) (.branch 50 (.branch 49 (.leaf 2738230598) (.leaf 2683171311)) (.branch 51 (.leaf 2629281285) (.leaf 2576532755)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2524898768) (.leaf 2474353152)) (.branch 55 (.leaf 2424870483) (.leaf 2376426057))) (.branch 58 (.branch 57 (.leaf 2328995865) (.leaf 2282556562)) (.branch 59 (.leaf 2237085449) (.leaf 2192560442))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 2148960057) (.branch 62 (.leaf 2106263386) (.leaf 2064450075))) (.branch 65 (.branch 64 (.leaf 2023500307) (.leaf 1983394786)) (.branch 66 (.leaf 1944114713) (.leaf 1905641777)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1867958133) (.leaf 1831046393)) (.branch 70 (.leaf 1794889604) (.leaf 1759471241))) (.branch 73 (.branch 72 (.leaf 1724775189) (.leaf 1690785734)) (.branch 74 (.leaf 1657487546) (.leaf 1624865674))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1592905528) (.branch 77 (.leaf 1561592871) (.leaf 1530913810))) (.branch 80 (.branch 79 (.leaf 1500854786) (.leaf 1471402559)) (.branch 81 (.leaf 1442544206) (.leaf 1414267108)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1386558942) (.leaf 1359407675)) (.branch 85 (.leaf 1332801550) (.leaf 1306729087))) (.branch 88 (.branch 87 (.leaf 1281179067) (.leaf 1256140532)) (.branch 89 (.leaf 1231602772) (.leaf 1207555324)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1183987959) (.branch 92 (.leaf 1160890683) (.leaf 1138253725))) (.branch 95 (.branch 94 (.leaf 1116067535) (.leaf 1094322777)) (.branch 96 (.leaf 1073010320) (.leaf 1052121241)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1031646811) (.leaf 1011578497)) (.branch 100 (.leaf 991907950) (.leaf 972627009))) (.branch 103 (.branch 102 (.leaf 953727689) (.leaf 935202180)) (.branch 104 (.leaf 917042842) (.leaf 899242202))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 881792948) (.leaf 864687926)) (.branch 108 (.leaf 847920137) (.leaf 831482732))) (.branch 111 (.branch 110 (.leaf 815369009) (.leaf 799572411)) (.branch 112 (.leaf 784086518) (.leaf 768905049)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 754021856) (.leaf 739430923)) (.branch 116 (.leaf 725126359) (.leaf 711102399))) (.branch 119 (.branch 118 (.leaf 697353399) (.leaf 683873835)) (.branch 120 (.leaf 670658298) (.leaf 657701492)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1253).prefactor = (5798005218643371/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1253).cutoff/(generalMeanRows 1253).c)).2 =
    (973304444043751/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1253).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1253).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 1253).q*(generalMeanRows 1253).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1253).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1253

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1253).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1253).criticalRate j.val*(generalMeanRows 1253).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1253).c*(generalMeanRows 1253).criticalPoint j.val)).2-
      (generalMeanRows 1253).J/2-(generalMeanRows 1253).error (generalMeanGrid j.val)+
      (generalMeanRows 1253).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1253).c)).2-
      (generalMeanRows 1253).J/2-(generalMeanRows 1253).error 4 := by
  have he : (generalMeanRows 1253).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1253) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1253)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1253

/-! Kernel-checked entropy margins for general spectral rectangle 1254. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1254
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5384005939) (.branch 2 (.leaf 5230963865) (.leaf 5083197825))) (.branch 5 (.branch 4 (.leaf 4940446838) (.leaf 4802469872)) (.branch 6 (.leaf 4669043740) (.leaf 4539961263)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4415029668) (.leaf 4294069173)) (.branch 10 (.leaf 4176911748) (.leaf 4063400017))) (.branch 13 (.branch 12 (.leaf 3953386295) (.leaf 3846731726)) (.branch 14 (.leaf 3743305525) (.leaf 3642984294))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3545651423) (.branch 17 (.leaf 3451196545) (.leaf 3359515051))) (.branch 20 (.branch 19 (.leaf 3270507655) (.leaf 3184080000)) (.branch 21 (.leaf 3100142305) (.leaf 3018609043)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2939398651) (.leaf 2862433266)) (.branch 25 (.leaf 2787638487) (.leaf 2714943151))) (.branch 28 (.branch 27 (.leaf 2644279137) (.leaf 2575581181)) (.branch 29 (.leaf 2508786707) (.leaf 2443835674)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2380670431) (.branch 32 (.leaf 2319235588) (.leaf 2259477892))) (.branch 35 (.branch 34 (.leaf 2201346116) (.leaf 2144790954)) (.branch 36 (.leaf 2089764923) (.leaf 2036222273)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1984118905) (.leaf 1933412289)) (.branch 40 (.leaf 1884061391) (.leaf 1836026607))) (.branch 43 (.branch 42 (.leaf 1789269696) (.leaf 1743753717)) (.branch 44 (.leaf 1699442978) (.leaf 1656302978))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1614300359) (.branch 47 (.leaf 1573402854) (.leaf 1533579247))) (.branch 50 (.branch 49 (.leaf 1494799330) (.leaf 1457033857)) (.branch 51 (.leaf 1420254514) (.leaf 1384433877)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1349545380) (.leaf 1315563282)) (.branch 55 (.leaf 1282462635) (.leaf 1250219258))) (.branch 58 (.branch 57 (.leaf 1218809703) (.leaf 1188211234)) (.branch 59 (.leaf 1158401799) (.leaf 1129360006))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1101065098) (.branch 62 (.leaf 1073496933) (.leaf 1046635963))) (.branch 65 (.branch 64 (.leaf 1020463213) (.leaf 994960259)) (.branch 66 (.leaf 970109215) (.leaf 945892708)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 922293869) (.leaf 899296309)) (.branch 70 (.leaf 876884107) (.leaf 855041796))) (.branch 73 (.branch 72 (.leaf 833754346) (.leaf 813007151)) (.branch 74 (.leaf 792786013) (.leaf 773077136))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 753867106) (.branch 77 (.leaf 735142882) (.leaf 716891786))) (.branch 80 (.branch 79 (.leaf 699101490) (.leaf 681760004)) (.branch 81 (.leaf 664855670) (.leaf 648377147)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 632313406) (.leaf 616653716)) (.branch 85 (.leaf 601387640) (.leaf 586505023))) (.branch 88 (.branch 87 (.leaf 571995983) (.leaf 557850908)) (.branch 89 (.leaf 544060441) (.leaf 530615478)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 517507159) (.branch 92 (.leaf 504726862) (.leaf 492266191))) (.branch 95 (.branch 94 (.leaf 480116977) (.leaf 468271268)) (.branch 96 (.leaf 456721322) (.leaf 445459600)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 434478766) (.leaf 423771675)) (.branch 100 (.leaf 413331370) (.leaf 403151079))) (.branch 103 (.branch 102 (.leaf 393224204) (.leaf 383544323)) (.branch 104 (.leaf 374105182) (.leaf 364900687))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 355924908) (.leaf 347172064)) (.branch 108 (.leaf 338636529) (.leaf 330312819))) (.branch 111 (.branch 110 (.leaf 322195597) (.leaf 314279659)) (.branch 112 (.leaf 306559938) (.leaf 299031500)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 291689535) (.leaf 284529358)) (.branch 116 (.leaf 277546404) (.leaf 270736229))) (.branch 119 (.branch 118 (.leaf 264094497) (.leaf 257616988)) (.branch 120 (.leaf 251299590) (.leaf 245138292)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1254).prefactor = (5000986074573863/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1254).cutoff/(generalMeanRows 1254).c)).2 =
    (995978892477881/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1254).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1254).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1254).q*(generalMeanRows 1254).c/2-2 = (122/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable420.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1254).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1254

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1254).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1254).criticalRate j.val*(generalMeanRows 1254).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1254).c*(generalMeanRows 1254).criticalPoint j.val)).2-
      (generalMeanRows 1254).J/2-(generalMeanRows 1254).error (generalMeanGrid j.val)+
      (generalMeanRows 1254).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1254).c)).2-
      (generalMeanRows 1254).J/2-(generalMeanRows 1254).error 4 := by
  have he : (generalMeanRows 1254).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1254) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1254)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1254

/-! Kernel-checked entropy margins for general spectral rectangle 1255. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1255
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6530095821) (.branch 2 (.leaf 6343738589) (.leaf 6163949373))) (.branch 5 (.branch 4 (.leaf 5990389536) (.leaf 5822747055)) (.branch 6 (.leaf 5660733738) (.leaf 5504082776)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5352546603) (.leaf 5205894998)) (.branch 10 (.leaf 5063913421) (.leaf 4926401530))) (.branch 13 (.branch 12 (.leaf 4793171877) (.leaf 4664048745)) (.branch 14 (.leaf 4538867108) (.leaf 4417471716))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4299716268) (.branch 17 (.leaf 4185462675) (.leaf 4074580397))) (.branch 20 (.branch 19 (.leaf 3966945856) (.leaf 3862441893)) (.branch 21 (.leaf 3760957294) (.leaf 3662386350)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3566628466) (.leaf 3473587803)) (.branch 25 (.leaf 3383172955) (.leaf 3295296652))) (.branch 28 (.branch 27 (.leaf 3209875494) (.leaf 3126829702)) (.branch 29 (.leaf 3046082899) (.leaf 2967561898)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2891196517) (.branch 32 (.leaf 2816919404) (.leaf 2744665878))) (.branch 35 (.branch 34 (.leaf 2674373782) (.leaf 2605983341)) (.branch 36 (.leaf 2539437046) (.leaf 2474679525)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2411657446) (.leaf 2350319404)) (.branch 40 (.leaf 2290615839) (.leaf 2232498937))) (.branch 43 (.branch 42 (.leaf 2175922556) (.leaf 2120842143)) (.branch 44 (.leaf 2067214668) (.leaf 2014998552))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1964153605) (.branch 47 (.leaf 1914640967) (.leaf 1866423050))) (.branch 50 (.branch 49 (.leaf 1819463487) (.leaf 1773727081)) (.branch 51 (.leaf 1729179759) (.leaf 1685788525)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1643521420) (.leaf 1602347479)) (.branch 55 (.leaf 1562236698) (.leaf 1523159992))) (.branch 58 (.branch 57 (.leaf 1485089165) (.leaf 1447996875)) (.branch 59 (.leaf 1411856603) (.leaf 1376642626))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1342329984) (.branch 62 (.leaf 1308894459) (.leaf 1276312542))) (.branch 65 (.branch 64 (.leaf 1244561416) (.leaf 1213618926)) (.branch 66 (.leaf 1183463562) (.leaf 1154074432)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1125431247) (.leaf 1097514294)) (.branch 70 (.leaf 1070304425) (.leaf 1043783035))) (.branch 73 (.branch 72 (.leaf 1017932041) (.leaf 992733871)) (.branch 74 (.leaf 968171447) (.leaf 944228165))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 920887884) (.branch 77 (.leaf 898134912) (.leaf 875953988))) (.branch 80 (.branch 79 (.leaf 854330275) (.leaf 833249339)) (.branch 81 (.leaf 812697145) (.leaf 792660040)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 773124743) (.leaf 754078331)) (.branch 85 (.leaf 735508235) (.leaf 717402223))) (.branch 88 (.branch 87 (.leaf 699748392) (.leaf 682535161)) (.branch 89 (.leaf 665751257) (.leaf 649385710)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 633427843) (.branch 92 (.leaf 617867262) (.leaf 602693851))) (.branch 95 (.branch 94 (.leaf 587897759) (.leaf 573469399)) (.branch 96 (.leaf 559399435) (.leaf 545678779)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 532298581) (.leaf 519250222)) (.branch 100 (.leaf 506525312) (.leaf 494115677))) (.branch 103 (.branch 102 (.leaf 482013360) (.leaf 470210610)) (.branch 104 (.leaf 458699878) (.leaf 447473809))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 436525244) (.leaf 425847204)) (.branch 108 (.leaf 415432895) (.leaf 405275697))) (.branch 111 (.branch 110 (.leaf 395369160) (.leaf 385707001)) (.branch 112 (.leaf 376283100) (.leaf 367091492)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 358126367) (.leaf 349382064)) (.branch 116 (.leaf 340853066) (.leaf 332533997))) (.branch 119 (.branch 118 (.leaf 324419621) (.leaf 316504832)) (.branch 120 (.leaf 308784657) (.leaf 301254248)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1255).prefactor = (3069815452329029/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1255).cutoff/(generalMeanRows 1255).c)).2 =
    (900622892608943/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1255).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1255).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1255).q*(generalMeanRows 1255).c/2-2 = (1553/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable418.value]
    have hcontinuation : (generalMeanRows 1255).q*(generalMeanRows 1255).cutoff/2-2 = (239/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable417.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1255).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1255

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1255).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1255).criticalRate j.val*(generalMeanRows 1255).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1255).c*(generalMeanRows 1255).criticalPoint j.val)).2-
      (generalMeanRows 1255).J/2-(generalMeanRows 1255).error (generalMeanGrid j.val)+
      (generalMeanRows 1255).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1255).c)).2-
      (generalMeanRows 1255).J/2-(generalMeanRows 1255).error 4 := by
  have he : (generalMeanRows 1255).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1255) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1255)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1255

/-! Kernel-checked entropy margins for general spectral rectangle 1256. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1256
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6268865832) (.branch 2 (.leaf 6120965473) (.leaf 5977658332))) (.branch 5 (.branch 4 (.leaf 5838714692) (.leaf 5703923335)) (.branch 6 (.leaf 5573089540) (.leaf 5446033339)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5322587983) (.leaf 5202598605)) (.branch 10 (.leaf 5085921046) (.leaf 4972420811))) (.branch 13 (.branch 12 (.leaf 4861972159) (.leaf 4754457292)) (.branch 14 (.leaf 4649765635) (.leaf 4547793202))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4448442023) (.branch 17 (.leaf 4351619645) (.leaf 4257238671))) (.branch 20 (.branch 19 (.leaf 4165216358) (.leaf 4075474255)) (.branch 21 (.leaf 3987937871) (.leaf 3902536381)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3819202361) (.leaf 3737871543)) (.branch 25 (.leaf 3658482599) (.leaf 3580976942))) (.branch 28 (.branch 27 (.leaf 3505298543) (.leaf 3431393766)) (.branch 29 (.leaf 3359211218) (.leaf 3288701611)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3219817636) (.branch 32 (.leaf 3152513843) (.leaf 3086746537))) (.branch 35 (.branch 34 (.leaf 3022473679) (.leaf 2959654794)) (.branch 36 (.leaf 2898250889) (.leaf 2838224369)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2779538971) (.leaf 2722159694)) (.branch 40 (.leaf 2666052737) (.leaf 2611185437))) (.branch 43 (.branch 42 (.leaf 2557526221) (.leaf 2505044550)) (.branch 44 (.leaf 2453710874) (.leaf 2403496586))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2354373981) (.branch 47 (.leaf 2306316214) (.leaf 2259297270))) (.branch 50 (.branch 49 (.leaf 2213291920) (.leaf 2168275697)) (.branch 51 (.leaf 2124224858) (.leaf 2081116359)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2038927827) (.leaf 1997637532)) (.branch 55 (.leaf 1957224363) (.leaf 1917667808))) (.branch 58 (.branch 57 (.leaf 1878947927) (.leaf 1841045331)) (.branch 59 (.leaf 1803941168) (.leaf 1767617097))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1732055272) (.branch 62 (.leaf 1697238328) (.leaf 1663149360))) (.branch 65 (.branch 64 (.leaf 1629771909) (.leaf 1597089949)) (.branch 66 (.leaf 1565087870) (.leaf 1533750464)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1503062915) (.leaf 1473010784)) (.branch 70 (.leaf 1443579998) (.leaf 1414756837))) (.branch 73 (.branch 72 (.leaf 1386527925) (.leaf 1358880220)) (.branch 74 (.leaf 1331800999) (.leaf 1305277854))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1279298681) (.branch 77 (.leaf 1253851670) (.leaf 1228925295))) (.branch 80 (.branch 79 (.leaf 1204508309) (.leaf 1180589735)) (.branch 81 (.leaf 1157158855) (.leaf 1134205209)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1111718582) (.leaf 1089688999)) (.branch 85 (.leaf 1068106719) (.leaf 1046962229))) (.branch 88 (.branch 87 (.leaf 1026246236) (.leaf 1005949661)) (.branch 89 (.leaf 986063637) (.leaf 966579499)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 947488779) (.branch 92 (.leaf 928783204) (.leaf 910454687))) (.branch 95 (.branch 94 (.leaf 892495327) (.leaf 874897398)) (.branch 96 (.leaf 857653349) (.leaf 840755798)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 824197530) (.leaf 807971487)) (.branch 100 (.leaf 792070772) (.leaf 776488636))) (.branch 103 (.branch 102 (.leaf 761218484) (.leaf 746253862)) (.branch 104 (.leaf 731588461) (.leaf 717216108))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 703130767) (.leaf 689326532)) (.branch 108 (.leaf 675797626) (.leaf 662538398))) (.branch 111 (.branch 110 (.leaf 649543318) (.leaf 636806975)) (.branch 112 (.leaf 624324078) (.leaf 612089447)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 600098013) (.leaf 588344816)) (.branch 116 (.leaf 576825004) (.leaf 565533826))) (.branch 119 (.branch 118 (.leaf 554466633) (.leaf 543618876)) (.branch 120 (.leaf 532986100) (.leaf 522563946)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1256).prefactor = (4690968656925781/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1256).cutoff/(generalMeanRows 1256).c)).2 =
    (1052805293129117/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1256).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1256).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1256).q*(generalMeanRows 1256).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 1256).q*(generalMeanRows 1256).cutoff/2-2 = (422/71:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable421.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1256).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1256

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1256).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1256).criticalRate j.val*(generalMeanRows 1256).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1256).c*(generalMeanRows 1256).criticalPoint j.val)).2-
      (generalMeanRows 1256).J/2-(generalMeanRows 1256).error (generalMeanGrid j.val)+
      (generalMeanRows 1256).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1256).c)).2-
      (generalMeanRows 1256).J/2-(generalMeanRows 1256).error 4 := by
  have he : (generalMeanRows 1256).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1256) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1256)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1256

/-! Kernel-checked entropy margins for general spectral rectangle 1257. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1257
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4619075363) (.branch 2 (.leaf 4485090027) (.leaf 4355788692))) (.branch 5 (.branch 4 (.leaf 4230938853) (.leaf 4110325712)) (.branch 6 (.leaf 3993750318) (.leaf 3881027945)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3771986671) (.leaf 3666466129)) (.branch 10 (.leaf 3564316406) (.leaf 3465397076))) (.branch 13 (.branch 12 (.leaf 3369576342) (.leaf 3276730272)) (.branch 14 (.leaf 3186742127) (.leaf 3099501757))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3014905063) (.branch 17 (.leaf 2932853517) (.leaf 2853253731))) (.branch 20 (.branch 19 (.leaf 2776017069) (.leaf 2701059297)) (.branch 21 (.leaf 2628300269) (.leaf 2557663641)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2489076610) (.leaf 2422469686)) (.branch 25 (.leaf 2357776468) (.leaf 2294933459))) (.branch 28 (.branch 27 (.leaf 2233879879) (.leaf 2174557507)) (.branch 29 (.leaf 2116910526) (.leaf 2060885390)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2006430695) (.branch 32 (.leaf 1953497058) (.leaf 1902037013))) (.branch 35 (.branch 34 (.leaf 1852004909) (.leaf 1803356814)) (.branch 36 (.leaf 1756050434) (.leaf 1710045024)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1665301320) (.leaf 1621781466)) (.branch 40 (.leaf 1579448945) (.leaf 1538268525))) (.branch 43 (.branch 42 (.leaf 1498206191) (.leaf 1459229101)) (.branch 44 (.leaf 1421305526) (.leaf 1384404810))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1348497317) (.branch 47 (.leaf 1313554394) (.leaf 1279548328))) (.branch 50 (.branch 49 (.leaf 1246452311) (.leaf 1214240396)) (.branch 51 (.leaf 1182887473) (.leaf 1152369230)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1122662123) (.leaf 1093743348)) (.branch 55 (.leaf 1065590812) (.leaf 1038183110))) (.branch 58 (.branch 57 (.leaf 1011499493) (.leaf 985519849)) (.branch 59 (.leaf 960224682) (.leaf 935595082))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 911612713) (.branch 62 (.leaf 888259788) (.leaf 865519050))) (.branch 65 (.branch 64 (.leaf 843373755) (.leaf 821807656)) (.branch 66 (.leaf 800804982) (.leaf 780350425)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 760429126) (.leaf 741026654)) (.branch 70 (.leaf 722129000) (.leaf 703722556))) (.branch 73 (.branch 72 (.leaf 685794109) (.leaf 668330820)) (.branch 74 (.leaf 651320220) (.leaf 634750193))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 618608967) (.branch 77 (.leaf 602885104) (.leaf 587567487))) (.branch 80 (.branch 79 (.leaf 572645311) (.leaf 558108076)) (.branch 81 (.leaf 543945573) (.leaf 530147878)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 516705345) (.leaf 503608592)) (.branch 85 (.leaf 490848500) (.leaf 478416199))) (.branch 88 (.branch 87 (.leaf 466303063) (.leaf 454500705)) (.branch 89 (.leaf 443000967) (.leaf 431795912)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 420877824) (.branch 92 (.leaf 410239191) (.leaf 399872711))) (.branch 95 (.branch 94 (.leaf 389771277) (.leaf 379927975)) (.branch 96 (.leaf 370336078) (.leaf 360989039)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351880489) (.leaf 343004231)) (.branch 100 (.leaf 334354232) (.leaf 325924623))) (.branch 103 (.branch 102 (.leaf 317709689) (.leaf 309703870)) (.branch 104 (.leaf 301901754) (.leaf 294298073))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 286887699) (.leaf 279665640)) (.branch 108 (.leaf 272627037) (.leaf 265767159))) (.branch 111 (.branch 110 (.leaf 259081401) (.leaf 252565278)) (.branch 112 (.leaf 246214426) (.leaf 240024594)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 233991643) (.leaf 228111544)) (.branch 116 (.leaf 222380374) (.leaf 216794311))) (.branch 119 (.branch 118 (.leaf 211349635) (.leaf 206042723)) (.branch 120 (.leaf 200870047) (.leaf 195828169)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1257).prefactor = (4399933295595671/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1257).cutoff/(generalMeanRows 1257).c)).2 =
    (980829253011753/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1257).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1257).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1257).q*(generalMeanRows 1257).c/2-2 = (1/1:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable008.value]
    have hcontinuation : (generalMeanRows 1257).q*(generalMeanRows 1257).cutoff/2-2 = (6/1:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable422.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1257).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1257

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1257).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1257).criticalRate j.val*(generalMeanRows 1257).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1257).c*(generalMeanRows 1257).criticalPoint j.val)).2-
      (generalMeanRows 1257).J/2-(generalMeanRows 1257).error (generalMeanGrid j.val)+
      (generalMeanRows 1257).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1257).c)).2-
      (generalMeanRows 1257).J/2-(generalMeanRows 1257).error 4 := by
  have he : (generalMeanRows 1257).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1257) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1257)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1257

/-! Kernel-checked entropy margins for general spectral rectangle 1258. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1258
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4814048455) (.branch 2 (.leaf 4677153825) (.leaf 4544984315))) (.branch 5 (.branch 4 (.leaf 4417305689) (.leaf 4293901641)) (.branch 6 (.leaf 4174571904) (.leaf 4059130604)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3947404812) (.leaf 3839233280)) (.branch 10 (.leaf 3734465321) (.leaf 3632959827))) (.branch 13 (.branch 12 (.leaf 3534584399) (.leaf 3439214571)) (.branch 14 (.leaf 3346733131) (.leaf 3257029505))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3169999215) (.branch 17 (.leaf 3085543391) (.leaf 3003568335))) (.branch 20 (.branch 19 (.leaf 2923985127) (.leaf 2846709272)) (.branch 21 (.leaf 2771660384) (.leaf 2698761892)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2627940783) (.leaf 2559127364)) (.branch 25 (.leaf 2492255045) (.leaf 2427260141))) (.branch 28 (.branch 27 (.leaf 2364081695) (.leaf 2302661308)) (.branch 29 (.leaf 2242942993) (.leaf 2184873034)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2128399857) (.branch 32 (.leaf 2073473911) (.leaf 2020047561))) (.branch 35 (.branch 34 (.leaf 1968074987) (.leaf 1917512087)) (.branch 36 (.leaf 1868316395) (.leaf 1820446992)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1773864440) (.leaf 1728530705)) (.branch 40 (.leaf 1684409090) (.leaf 1641464180))) (.branch 43 (.branch 42 (.leaf 1599661778) (.leaf 1558968852)) (.branch 44 (.leaf 1519353485) (.leaf 1480784829))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1443233055) (.branch 47 (.leaf 1406669311) (.leaf 1371065688))) (.branch 50 (.branch 49 (.leaf 1336395173) (.leaf 1302631619)) (.branch 51 (.leaf 1269749709) (.leaf 1237724924)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1206533510) (.leaf 1176152454)) (.branch 55 (.leaf 1146559450) (.leaf 1117732877))) (.branch 58 (.branch 57 (.leaf 1089651773) (.leaf 1062295809)) (.branch 59 (.leaf 1035645270) (.leaf 1009681029))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 984384529) (.branch 62 (.leaf 959737763) (.leaf 935723252))) (.branch 65 (.branch 64 (.leaf 912324032) (.leaf 889523632)) (.branch 66 (.leaf 867306059) (.leaf 845655784)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 824557723) (.leaf 803997224)) (.branch 70 (.leaf 783960054) (.leaf 764432384))) (.branch 73 (.branch 72 (.leaf 745400776) (.leaf 726852173)) (.branch 74 (.leaf 708773881) (.leaf 691153566))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 673979235) (.branch 77 (.leaf 657239229) (.leaf 640922214))) (.branch 80 (.branch 79 (.leaf 625017167) (.leaf 609513370)) (.branch 81 (.leaf 594400400) (.leaf 579668118)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 565306663) (.leaf 551306442)) (.branch 85 (.leaf 537658123) (.leaf 524352628))) (.branch 88 (.branch 87 (.leaf 511381122) (.leaf 498735011)) (.branch 89 (.leaf 486405930) (.leaf 474385740)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 462666520) (.branch 92 (.leaf 451240560) (.leaf 440100356))) (.branch 95 (.branch 94 (.leaf 429238604) (.leaf 418648194)) (.branch 96 (.leaf 408322204) (.leaf 398253896)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 388436710) (.leaf 378864257)) (.branch 100 (.leaf 369530320) (.leaf 360428841))) (.branch 103 (.branch 102 (.leaf 351553925) (.leaf 342899829)) (.branch 104 (.leaf 334460961) (.leaf 326231874))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 318207265) (.leaf 310381967)) (.branch 108 (.leaf 302750949) (.leaf 295309310))) (.branch 111 (.branch 110 (.leaf 288052275) (.leaf 280975195)) (.branch 112 (.leaf 274073540) (.leaf 267342896)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 260778965) (.leaf 254377557)) (.branch 116 (.leaf 248134593) (.leaf 242046097))) (.branch 119 (.branch 118 (.leaf 236108195) (.leaf 230317113)) (.branch 120 (.leaf 224669174) (.leaf 219160794)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1258).prefactor = (2235513818331677/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1258).cutoff/(generalMeanRows 1258).c)).2 =
    (988861424709019/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1258).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1258).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1258).q*(generalMeanRows 1258).c/2-2 = (122/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable420.value]
    have hcontinuation : (generalMeanRows 1258).q*(generalMeanRows 1258).cutoff/2-2 = (6/1:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable422.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1258).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1258

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1258).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1258).criticalRate j.val*(generalMeanRows 1258).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1258).c*(generalMeanRows 1258).criticalPoint j.val)).2-
      (generalMeanRows 1258).J/2-(generalMeanRows 1258).error (generalMeanGrid j.val)+
      (generalMeanRows 1258).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1258).c)).2-
      (generalMeanRows 1258).J/2-(generalMeanRows 1258).error 4 := by
  have he : (generalMeanRows 1258).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1258) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1258)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1258

/-! Kernel-checked entropy margins for general spectral rectangle 1259. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow1259
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4538377481) (.branch 2 (.leaf 4410970558) (.leaf 4287860526))) (.branch 5 (.branch 4 (.leaf 4168842706) (.leaf 4053727501)) (.branch 6 (.leaf 3942338825) (.leaf 3834512731)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3730096219) (.leaf 3628946180)) (.branch 10 (.leaf 3530928482) (.leaf 3435917150))) (.branch 13 (.branch 12 (.leaf 3343793651) (.leaf 3254446252)) (.branch 14 (.leaf 3167769458) (.leaf 3083663506))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3002033909) (.branch 17 (.leaf 2922791056) (.leaf 2845849845))) (.branch 20 (.branch 19 (.leaf 2771129359) (.leaf 2698552565)) (.branch 21 (.leaf 2628046050) (.leaf 2559539776)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2492966861) (.leaf 2428263375)) (.branch 25 (.leaf 2365368157) (.leaf 2304222646))) (.branch 28 (.branch 27 (.leaf 2244770728) (.leaf 2186958591)) (.branch 29 (.leaf 2130734597) (.leaf 2076049161)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2022854634) (.branch 32 (.leaf 1971105210) (.leaf 1920756818))) (.branch 35 (.branch 34 (.leaf 1871767042) (.leaf 1824095035)) (.branch 36 (.leaf 1777701441) (.leaf 1732548324)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1688599098) (.leaf 1645818469)) (.branch 40 (.leaf 1604172369) (.leaf 1563627909))) (.branch 43 (.branch 42 (.leaf 1524153318) (.leaf 1485717899)) (.branch 44 (.leaf 1448291984) (.leaf 1411846884))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1376354857) (.branch 47 (.leaf 1341789061) (.leaf 1308123521))) (.branch 50 (.branch 49 (.leaf 1275333095) (.leaf 1243393439)) (.branch 51 (.leaf 1212280976) (.leaf 1181972868)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1152446986) (.leaf 1123681884)) (.branch 55 (.leaf 1095656775) (.leaf 1068351504))) (.branch 58 (.branch 57 (.leaf 1041746525) (.leaf 1015822883)) (.branch 59 (.leaf 990562187) (.leaf 965946595))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 941958792) (.branch 62 (.leaf 918581974) (.leaf 895799827))) (.branch 65 (.branch 64 (.leaf 873596512) (.leaf 851956652)) (.branch 66 (.leaf 830865311) (.leaf 810307983)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 790270576) (.leaf 770739400)) (.branch 70 (.leaf 751701154) (.leaf 733142912))) (.branch 73 (.branch 72 (.leaf 715052110) (.leaf 697416539)) (.branch 74 (.leaf 680224328) (.leaf 663463939))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 647124153) (.branch 77 (.leaf 631194060) (.leaf 615663051))) (.branch 80 (.branch 79 (.leaf 600520809) (.leaf 585757300)) (.branch 81 (.leaf 571362762) (.leaf 557327699)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 543642874) (.leaf 530299299)) (.branch 85 (.leaf 517288229) (.leaf 504601154))) (.branch 88 (.branch 87 (.leaf 492229793) (.leaf 480166087)) (.branch 89 (.leaf 468402190) (.leaf 456930470)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 445743492) (.branch 92 (.leaf 434834024) (.leaf 424195022))) (.branch 95 (.branch 94 (.leaf 413819630) (.leaf 403701171)) (.branch 96 (.leaf 393833145) (.leaf 384209223)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 374823241) (.leaf 365669198)) (.branch 100 (.leaf 356741248) (.leaf 348033699))) (.branch 103 (.branch 102 (.leaf 339541006) (.leaf 331257770)) (.branch 104 (.leaf 323178728) (.leaf 315298759))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 307612871) (.leaf 300116202)) (.branch 108 (.leaf 292804015) (.leaf 285671695))) (.branch 111 (.branch 110 (.leaf 278714747) (.leaf 271928790)) (.branch 112 (.leaf 265309556) (.leaf 258852886)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 252554730) (.leaf 246411137)) (.branch 116 (.leaf 240418260) (.leaf 234572350))) (.branch 119 (.branch 118 (.leaf 228869754) (.leaf 223306909)) (.branch 120 (.leaf 217880345) (.leaf 212586680)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 1259).prefactor = (255844154932599/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 1259).cutoff/(generalMeanRows 1259).c)).2 =
    (68583946722501/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 1259).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 1259).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 1259).q*(generalMeanRows 1259).c/2-2 = (1547/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable423.value]
    have hcontinuation : (generalMeanRows 1259).q*(generalMeanRows 1259).cutoff/2-2 = (3424/497:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable424.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 1259).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 1259

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 1259).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 1259).criticalRate j.val*(generalMeanRows 1259).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 1259).c*(generalMeanRows 1259).criticalPoint j.val)).2-
      (generalMeanRows 1259).J/2-(generalMeanRows 1259).error (generalMeanGrid j.val)+
      (generalMeanRows 1259).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 1259).c)).2-
      (generalMeanRows 1259).J/2-(generalMeanRows 1259).error 4 := by
  have he : (generalMeanRows 1259).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 1259) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 1259)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow1259

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock17 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 17 i) := by
  fin_cases i
  · exact EntropyRow1190.numerical
  · exact EntropyRow1191.numerical
  · exact EntropyRow1192.numerical
  · exact EntropyRow1193.numerical
  · exact EntropyRow1194.numerical
  · exact EntropyRow1195.numerical
  · exact EntropyRow1196.numerical
  · exact EntropyRow1197.numerical
  · exact EntropyRow1198.numerical
  · exact EntropyRow1199.numerical
  · exact EntropyRow1200.numerical
  · exact EntropyRow1201.numerical
  · exact EntropyRow1202.numerical
  · exact EntropyRow1203.numerical
  · exact EntropyRow1204.numerical
  · exact EntropyRow1205.numerical
  · exact EntropyRow1206.numerical
  · exact EntropyRow1207.numerical
  · exact EntropyRow1208.numerical
  · exact EntropyRow1209.numerical
  · exact EntropyRow1210.numerical
  · exact EntropyRow1211.numerical
  · exact EntropyRow1212.numerical
  · exact EntropyRow1213.numerical
  · exact EntropyRow1214.numerical
  · exact EntropyRow1215.numerical
  · exact EntropyRow1216.numerical
  · exact EntropyRow1217.numerical
  · exact EntropyRow1218.numerical
  · exact EntropyRow1219.numerical
  · exact EntropyRow1220.numerical
  · exact EntropyRow1221.numerical
  · exact EntropyRow1222.numerical
  · exact EntropyRow1223.numerical
  · exact EntropyRow1224.numerical
  · exact EntropyRow1225.numerical
  · exact EntropyRow1226.numerical
  · exact EntropyRow1227.numerical
  · exact EntropyRow1228.numerical
  · exact EntropyRow1229.numerical
  · exact EntropyRow1230.numerical
  · exact EntropyRow1231.numerical
  · exact EntropyRow1232.numerical
  · exact EntropyRow1233.numerical
  · exact EntropyRow1234.numerical
  · exact EntropyRow1235.numerical
  · exact EntropyRow1236.numerical
  · exact EntropyRow1237.numerical
  · exact EntropyRow1238.numerical
  · exact EntropyRow1239.numerical
  · exact EntropyRow1240.numerical
  · exact EntropyRow1241.numerical
  · exact EntropyRow1242.numerical
  · exact EntropyRow1243.numerical
  · exact EntropyRow1244.numerical
  · exact EntropyRow1245.numerical
  · exact EntropyRow1246.numerical
  · exact EntropyRow1247.numerical
  · exact EntropyRow1248.numerical
  · exact EntropyRow1249.numerical
  · exact EntropyRow1250.numerical
  · exact EntropyRow1251.numerical
  · exact EntropyRow1252.numerical
  · exact EntropyRow1253.numerical
  · exact EntropyRow1254.numerical
  · exact EntropyRow1255.numerical
  · exact EntropyRow1256.numerical
  · exact EntropyRow1257.numerical
  · exact EntropyRow1258.numerical
  · exact EntropyRow1259.numerical
end SingularValueBounds.KL.Certificates
