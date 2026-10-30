import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block08
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block09
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 350. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0350
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4807644923) (.branch 2 (.leaf 4633077062) (.leaf 4466534594))) (.branch 5 (.branch 4 (.leaf 4307557160) (.leaf 4155716888)) (.branch 6 (.leaf 4010615564) (.leaf 3871882107)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3739170302) (.leaf 3612156780)) (.branch 10 (.leaf 3490539182) (.leaf 3374034514))) (.branch 13 (.branch 12 (.leaf 3262377655) (.leaf 3155320007)) (.branch 14 (.leaf 3052628259) (.leaf 2954083276))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2859479073) (.branch 17 (.leaf 2768621883) (.leaf 2681329304))) (.branch 20 (.branch 19 (.leaf 2597429512) (.leaf 2516760547)) (.branch 21 (.leaf 2439169644) (.leaf 2364512629)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2292653354) (.leaf 2223463176)) (.branch 25 (.leaf 2156820481) (.leaf 2092610234))) (.branch 28 (.branch 27 (.leaf 2030723570) (.leaf 1971057413)) (.branch 29 (.leaf 1913514116) (.leaf 1858001136)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1804430723) (.branch 32 (.leaf 1752719637) (.leaf 1702788879))) (.branch 35 (.branch 34 (.leaf 1654563445) (.leaf 1607972091)) (.branch 36 (.leaf 1562947120) (.leaf 1519424176)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1477342055) (.leaf 1436642529)) (.branch 40 (.leaf 1397270180) (.leaf 1359172242))) (.branch 43 (.branch 42 (.leaf 1322298459) (.leaf 1286600943)) (.branch 44 (.leaf 1252034050) (.leaf 1218554256))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1186120045) (.branch 47 (.leaf 1154691803) (.leaf 1124231717))) (.branch 50 (.branch 49 (.leaf 1094703680) (.leaf 1066073202)) (.branch 51 (.leaf 1038307329) (.leaf 1011374559)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 985244774) (.leaf 959889166)) (.branch 55 (.leaf 935280169) (.leaf 911391404))) (.branch 58 (.branch 57 (.leaf 888197610) (.leaf 865674599)) (.branch 59 (.leaf 843799194) (.leaf 822549187))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 801903286) (.branch 62 (.leaf 781841076) (.leaf 762342971))) (.branch 65 (.branch 64 (.leaf 743390182) (.leaf 724964671)) (.branch 66 (.leaf 707049122) (.leaf 689626905)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 672682042) (.leaf 656199180)) (.branch 70 (.leaf 640163562) (.leaf 624560998))) (.branch 73 (.branch 72 (.leaf 609377838) (.leaf 594600952)) (.branch 74 (.leaf 580217704) (.leaf 566215931))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 552583919) (.branch 77 (.leaf 539310389) (.leaf 526384470))) (.branch 80 (.branch 79 (.leaf 513795691) (.leaf 501533956)) (.branch 81 (.leaf 489589529) (.leaf 477953024)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 466615382) (.leaf 455567866)) (.branch 85 (.leaf 444802040) (.leaf 434309760))) (.branch 88 (.branch 87 (.leaf 424083163) (.leaf 414114653)) (.branch 89 (.leaf 404396890) (.leaf 394922783)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 385685477) (.branch 92 (.leaf 376678344) (.leaf 367894974))) (.branch 95 (.branch 94 (.leaf 359329167) (.leaf 350974926)) (.branch 96 (.leaf 342826445) (.leaf 334878107)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 327124472) (.leaf 319560272)) (.branch 100 (.leaf 312180407) (.leaf 304979935))) (.branch 103 (.branch 102 (.leaf 297954067) (.leaf 291098162)) (.branch 104 (.leaf 284407723) (.leaf 277878389))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 271505930) (.leaf 265286245)) (.branch 108 (.leaf 259215357) (.leaf 253289404))) (.branch 111 (.branch 110 (.leaf 247504640) (.leaf 241857431)) (.branch 112 (.leaf 236344247) (.leaf 230961662)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 225706348) (.leaf 220575074)) (.branch 116 (.leaf 215564700) (.leaf 210672179))) (.branch 119 (.branch 118 (.leaf 205894545) (.leaf 201228920)) (.branch 120 (.leaf 196672505) (.leaf 192222579)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 350).prefactor = (2430848165329479/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 350).cutoff/(generalMeanRows 350).c)).2 =
    (43973685107257/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 350).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 350).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 350).q*(generalMeanRows 350).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 350).q*(generalMeanRows 350).cutoff/2-2 = (4234/2019:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable149.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 350).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 350

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 350).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 350).criticalRate j.val*(generalMeanRows 350).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 350).c*(generalMeanRows 350).criticalPoint j.val)).2-
      (generalMeanRows 350).J/2-(generalMeanRows 350).error (generalMeanGrid j.val)+
      (generalMeanRows 350).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 350).c)).2-
      (generalMeanRows 350).J/2-(generalMeanRows 350).error 4 := by
  have he : (generalMeanRows 350).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 350) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 350)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0350

/-! Kernel-checked entropy margins for general spectral rectangle 351. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0351
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4817883009) (.branch 2 (.leaf 4642989171) (.leaf 4476127612))) (.branch 5 (.branch 4 (.leaf 4316838118) (.leaf 4164692933)) (.branch 6 (.leaf 4019293925) (.leaf 3880270069)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3747275184) (.leaf 3619985906)) (.branch 10 (.leaf 3498099867) (.leaf 3381334045))) (.branch 13 (.branch 12 (.leaf 3269423271) (.leaf 3162118886)) (.branch 14 (.leaf 3059187509) (.leaf 2960409917))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2865580032) (.branch 17 (.leaf 2774503982) (.leaf 2686999254))) (.branch 20 (.branch 19 (.leaf 2602893907) (.leaf 2522025856)) (.branch 21 (.leaf 2444242209) (.leaf 2369398660)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2297358924) (.leaf 2227994223)) (.branch 25 (.leaf 2161182800) (.leaf 2096809483))) (.branch 28 (.branch 27 (.leaf 2034765263) (.leaf 1974946922)) (.branch 29 (.leaf 1917256673) (.leaf 1861601829)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1807894502) (.branch 32 (.leaf 1756051311) (.leaf 1705993120))) (.branch 35 (.branch 34 (.leaf 1657644787) (.leaf 1610934935)) (.branch 36 (.leaf 1565795732) (.leaf 1522162693)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1479974485) (.leaf 1439172755)) (.branch 40 (.leaf 1399701960) (.leaf 1361509215))) (.branch 43 (.branch 42 (.leaf 1324544142) (.leaf 1288758741)) (.branch 44 (.leaf 1254107252) (.leaf 1220546042))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1188033488) (.branch 47 (.leaf 1156529870) (.leaf 1125997274))) (.branch 50 (.branch 49 (.leaf 1096399492) (.leaf 1067701940)) (.branch 51 (.leaf 1039871566) (.leaf 1012876782)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 986687377) (.leaf 961274459)) (.branch 55 (.leaf 936610379) (.leaf 912668675))) (.branch 58 (.branch 57 (.leaf 889424012) (.leaf 866852121)) (.branch 59 (.leaf 844929755) (.leaf 823634633))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 802945396) (.branch 62 (.leaf 782841561) (.leaf 763303479))) (.branch 65 (.branch 64 (.leaf 744312297) (.leaf 725849919)) (.branch 66 (.leaf 707898970) (.leaf 690442763)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 673465268) (.leaf 656951079)) (.branch 70 (.leaf 640885389) (.leaf 625253957))) (.branch 73 (.branch 72 (.leaf 610043089) (.leaf 595239610)) (.branch 74 (.leaf 580830839) (.leaf 566804571))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 553149052) (.branch 77 (.leaf 539852964) (.leaf 526905400))) (.branch 80 (.branch 79 (.leaf 514295851) (.leaf 502014186)) (.branch 81 (.leaf 490050638) (.leaf 478395786)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 467040543) (.leaf 455976140)) (.branch 85 (.leaf 445194112) (.leaf 434686289))) (.branch 88 (.branch 87 (.leaf 424444781) (.leaf 414461966)) (.branch 89 (.leaf 404730480) (.leaf 395243209)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 385993274) (.branch 92 (.leaf 376974026) (.leaf 368179035))) (.branch 95 (.branch 94 (.leaf 359602080) (.leaf 351237144)) (.branch 96 (.leaf 343078404) (.leaf 335120224)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 327357147) (.leaf 319783890)) (.branch 100 (.leaf 312395336) (.leaf 305186528))) (.branch 103 (.branch 102 (.leaf 298152663) (.leaf 291289087)) (.branch 104 (.leaf 284591287) (.leaf 278054891))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 271675656) (.leaf 265449471)) (.branch 108 (.leaf 259372345) (.leaf 253440406))) (.branch 111 (.branch 110 (.leaf 247649899) (.leaf 241997179)) (.branch 112 (.leaf 236478706) (.leaf 231091045)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 225830860) (.leaf 220694910)) (.branch 116 (.leaf 215680050) (.leaf 210783220))) (.branch 119 (.branch 118 (.leaf 206001452) (.leaf 201331858)) (.branch 120 (.leaf 196771633) (.leaf 192318048)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 351).prefactor = (4862615398537063/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 351).cutoff/(generalMeanRows 351).c)).2 =
    (175152349795239/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 351).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 351).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 351).q*(generalMeanRows 351).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 351).q*(generalMeanRows 351).cutoff/2-2 = (2114/1011:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable147.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 351).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 351

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 351).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 351).criticalRate j.val*(generalMeanRows 351).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 351).c*(generalMeanRows 351).criticalPoint j.val)).2-
      (generalMeanRows 351).J/2-(generalMeanRows 351).error (generalMeanGrid j.val)+
      (generalMeanRows 351).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 351).c)).2-
      (generalMeanRows 351).J/2-(generalMeanRows 351).error 4 := by
  have he : (generalMeanRows 351).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 351) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 351)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0351

/-! Kernel-checked entropy margins for general spectral rectangle 352. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0352
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4826439320) (.branch 2 (.leaf 4651234879) (.leaf 4484076983))) (.branch 5 (.branch 4 (.leaf 4324504600) (.leaf 4172089212)) (.branch 6 (.leaf 4026431983) (.leaf 3887161228)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3753930150) (.leaf 3626414814)) (.branch 10 (.leaf 3504312312) (.leaf 3387339119))) (.branch 13 (.branch 12 (.leaf 3275229598) (.leaf 3167734646)) (.branch 14 (.leaf 3064620467) (.leaf 2965667452))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2870669153) (.branch 17 (.leaf 2779431357) (.leaf 2691771226))) (.branch 20 (.branch 19 (.leaf 2607516512) (.leaf 2526504843)) (.branch 21 (.leaf 2448583057) (.leaf 2373606589)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2301438915) (.leaf 2231951025)) (.branch 25 (.leaf 2165020949) (.leaf 2100533308))) (.branch 28 (.branch 27 (.leaf 2038378901) (.leaf 1978454326)) (.branch 29 (.leaf 1920661622) (.leaf 1864907938)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1811105229) (.branch 32 (.leaf 1759169967) (.leaf 1709022875))) (.branch 35 (.branch 34 (.leaf 1660588678) (.leaf 1613795872)) (.branch 36 (.leaf 1568576505) (.leaf 1524865975)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1482602843) (.leaf 1441728651)) (.branch 40 (.leaf 1402187759) (.leaf 1363927185))) (.branch 43 (.branch 42 (.leaf 1326896464) (.leaf 1291047510)) (.branch 44 (.leaf 1256334481) (.leaf 1222713669))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1190143374) (.branch 47 (.leaf 1158583808) (.leaf 1127996987))) (.branch 50 (.branch 49 (.leaf 1098346641) (.leaf 1069598123)) (.branch 51 (.leaf 1041718325) (.leaf 1014675598)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 988439683) (.leaf 962981633)) (.branch 55 (.leaf 938273751) (.leaf 914289528))) (.branch 58 (.branch 57 (.leaf 891003583) (.leaf 868391605)) (.branch 59 (.leaf 846430307) (.leaf 825097366))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 804371386) (.branch 62 (.leaf 784231847) (.leaf 764659066))) (.branch 65 (.branch 64 (.leaf 745634157) (.leaf 727138991)) (.branch 66 (.leaf 709156162) (.leaf 691668954)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 674661308) (.leaf 658117791)) (.branch 70 (.leaf 642023568) (.leaf 626364376))) (.branch 73 (.branch 72 (.leaf 611126494) (.leaf 596296724)) (.branch 74 (.leaf 581862364) (.leaf 567811186))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 554131416) (.branch 77 (.leaf 540811715) (.leaf 527841157))) (.branch 80 (.branch 79 (.leaf 515209214) (.leaf 502905737)) (.branch 81 (.leaf 490920943) (.leaf 479245393)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 467869983) (.leaf 456785930)) (.branch 85 (.leaf 445984754) (.leaf 435458270))) (.branch 88 (.branch 87 (.leaf 425198573) (.leaf 415198029)) (.branch 89 (.leaf 405449261) (.leaf 395945140)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 386678778) (.branch 92 (.leaf 377643512) (.leaf 368832901))) (.branch 95 (.branch 94 (.leaf 360240714) (.leaf 351860923)) (.branch 96 (.leaf 343687693) (.leaf 335715380)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 327938516) (.leaf 320351810)) (.branch 100 (.leaf 312950134) (.leaf 305728524))) (.branch 103 (.branch 102 (.leaf 298682167) (.leaf 291806401)) (.branch 104 (.leaf 285096707) (.leaf 278548702))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 272158138) (.leaf 265920896)) (.branch 108 (.leaf 259832976) (.leaf 253890503))) (.branch 111 (.branch 110 (.leaf 248089713) (.leaf 242426953)) (.branch 112 (.leaf 236898680) (.leaf 231501451)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 226231924) (.leaf 221086853)) (.branch 116 (.leaf 216063086) (.leaf 211157561))) (.branch 119 (.branch 118 (.leaf 206367300) (.leaf 201689413)) (.branch 120 (.leaf 197121089) (.leaf 192659595)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 352).prefactor = (4871251151885627/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 352).cutoff/(generalMeanRows 352).c)).2 =
    (175152349795239/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 352).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 352).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 352).q*(generalMeanRows 352).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 352).q*(generalMeanRows 352).cutoff/2-2 = (2114/1011:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable147.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 352).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 352

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 352).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 352).criticalRate j.val*(generalMeanRows 352).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 352).c*(generalMeanRows 352).criticalPoint j.val)).2-
      (generalMeanRows 352).J/2-(generalMeanRows 352).error (generalMeanGrid j.val)+
      (generalMeanRows 352).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 352).c)).2-
      (generalMeanRows 352).J/2-(generalMeanRows 352).error 4 := by
  have he : (generalMeanRows 352).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 352) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 352)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0352

/-! Kernel-checked entropy margins for general spectral rectangle 353. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0353
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5304869243) (.branch 2 (.leaf 5138548384) (.leaf 4979634677))) (.branch 5 (.branch 4 (.leaf 4827696192) (.leaf 4682331937)) (.branch 6 (.leaf 4543169156) (.leaf 4409860918)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4282083953) (.leaf 4159536711)) (.branch 10 (.leaf 4041937617) (.leaf 3929023494))) (.branch 13 (.branch 12 (.leaf 3820548129) (.leaf 3716280986)) (.branch 14 (.leaf 3616006023) (.leaf 3519520625))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3426634620) (.branch 17 (.leaf 3337169394) (.leaf 3250957062))) (.branch 20 (.branch 19 (.leaf 3167839727) (.leaf 3087668785)) (.branch 21 (.leaf 3010304294) (.leaf 2935614390)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2863474746) (.leaf 2793768079)) (.branch 25 (.leaf 2726383688) (.leaf 2661217030))) (.branch 28 (.branch 27 (.leaf 2598169326) (.leaf 2537147197)) (.branch 29 (.leaf 2478062325) (.leaf 2420831134)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2365374506) (.branch 32 (.leaf 2311617500) (.leaf 2259489105))) (.branch 35 (.branch 34 (.leaf 2208922001) (.leaf 2159852337)) (.branch 36 (.leaf 2112219529) (.leaf 2065966066)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2021037332) (.leaf 1977381436)) (.branch 40 (.leaf 1934949057) (.leaf 1893693297))) (.branch 43 (.branch 42 (.leaf 1853569542) (.leaf 1814535336)) (.branch 44 (.leaf 1776550256) (.leaf 1739575805))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1703575298) (.branch 47 (.leaf 1668513768) (.leaf 1634357871))) (.branch 50 (.branch 49 (.leaf 1601075796) (.leaf 1568637183)) (.branch 51 (.leaf 1537013049) (.leaf 1506175707)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1476098706) (.leaf 1446756760)) (.branch 55 (.leaf 1418125687) (.leaf 1390182356))) (.branch 58 (.branch 57 (.leaf 1362904629) (.leaf 1336271311)) (.branch 59 (.leaf 1310262103) (.leaf 1284857552))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1260039016) (.branch 62 (.leaf 1235788617) (.leaf 1212089204))) (.branch 65 (.branch 64 (.leaf 1188924318) (.leaf 1166278161)) (.branch 66 (.leaf 1144135556) (.leaf 1122481925)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1101303254) (.leaf 1080586069)) (.branch 70 (.leaf 1060317410) (.leaf 1040484807))) (.branch 73 (.branch 72 (.leaf 1021076253) (.leaf 1002080190)) (.branch 74 (.leaf 983485479) (.leaf 965281390))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 947457574) (.branch 77 (.leaf 930004054) (.leaf 912911202))) (.branch 80 (.branch 79 (.leaf 896169727) (.leaf 879770660)) (.branch 81 (.leaf 863705335) (.leaf 847965383)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 832542713) (.leaf 817429504)) (.branch 85 (.leaf 802618190) (.leaf 788101452))) (.branch 88 (.branch 87 (.leaf 773872207) (.leaf 759923597)) (.branch 89 (.leaf 746248979) (.leaf 732841919)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 719696181) (.branch 92 (.leaf 706805721) (.leaf 694164677))) (.branch 95 (.branch 94 (.leaf 681767362) (.leaf 669608260)) (.branch 96 (.leaf 657682015) (.leaf 645983429)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 634507452) (.leaf 623249179)) (.branch 100 (.leaf 612203844) (.leaf 601366814))) (.branch 103 (.branch 102 (.leaf 590733586) (.leaf 580299779)) (.branch 104 (.leaf 570061131) (.leaf 560013497))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 550152841) (.leaf 540475235)) (.branch 108 (.leaf 530976854) (.leaf 521653972))) (.branch 111 (.branch 110 (.leaf 512502960) (.leaf 503520281)) (.branch 112 (.leaf 494702488) (.leaf 486046220)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 477548202) (.leaf 469205237)) (.branch 116 (.leaf 461014208) (.leaf 452972075))) (.branch 119 (.branch 118 (.leaf 445075869) (.leaf 437322694)) (.branch 120 (.leaf 429709722) (.leaf 422234191)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 353).prefactor = (1151730536542697/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 353).cutoff/(generalMeanRows 353).c)).2 =
    (440792956175007/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 353).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 353).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 353).q*(generalMeanRows 353).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 353).q*(generalMeanRows 353).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable148.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 353).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 353

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 353).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 353).criticalRate j.val*(generalMeanRows 353).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 353).c*(generalMeanRows 353).criticalPoint j.val)).2-
      (generalMeanRows 353).J/2-(generalMeanRows 353).error (generalMeanGrid j.val)+
      (generalMeanRows 353).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 353).c)).2-
      (generalMeanRows 353).J/2-(generalMeanRows 353).error 4 := by
  have he : (generalMeanRows 353).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 353) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 353)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0353

/-! Kernel-checked entropy margins for general spectral rectangle 354. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0354
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5322669148) (.branch 2 (.leaf 5155790218) (.leaf 4996343293))) (.branch 5 (.branch 4 (.leaf 4843894995) (.leaf 4698042986)) (.branch 6 (.leaf 4558413260) (.leaf 4424657721)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4296452014) (.leaf 4173493579)) (.branch 10 (.leaf 4055499894) (.leaf 3942206900))) (.branch 13 (.branch 12 (.leaf 3833367558) (.leaf 3728750558)) (.branch 14 (.leaf 3628139134) (.leaf 3531329989))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3438132316) (.branch 17 (.leaf 3348366898) (.leaf 3261865291))) (.branch 20 (.branch 19 (.leaf 3178469064) (.leaf 3098029118)) (.branch 21 (.leaf 3020405039) (.leaf 2945464521)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2873082820) (.leaf 2803142260)) (.branch 25 (.leaf 2735531768) (.leaf 2670146450))) (.branch 28 (.branch 27 (.leaf 2606887197) (.leaf 2545660316)) (.branch 29 (.leaf 2486377190) (.leaf 2428953967)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2373311260) (.branch 32 (.leaf 2319373878) (.leaf 2267070572))) (.branch 35 (.branch 34 (.leaf 2216333795) (.leaf 2167099484)) (.branch 36 (.leaf 2119306849) (.leaf 2072898188)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2027818701) (.leaf 1984016322)) (.branch 40 (.leaf 1941441566) (.leaf 1900047376))) (.branch 43 (.branch 42 (.leaf 1859788991) (.leaf 1820623809)) (.branch 44 (.leaf 1782511275) (.leaf 1745412760))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1709291458) (.branch 47 (.leaf 1674112283) (.leaf 1639841779))) (.branch 50 (.branch 49 (.leaf 1606448029) (.leaf 1573900573)) (.branch 51 (.leaf 1542170327) (.leaf 1511229514)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1481051593) (.leaf 1451611193)) (.branch 55 (.leaf 1422884051) (.leaf 1394846960))) (.branch 58 (.branch 57 (.leaf 1367477705) (.leaf 1340755023)) (.branch 59 (.leaf 1314658543) (.leaf 1289168751))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1264266939) (.branch 62 (.leaf 1239935170) (.leaf 1216156236))) (.branch 65 (.branch 64 (.leaf 1192913623) (.leaf 1170191479)) (.branch 66 (.leaf 1147974577) (.leaf 1126248289)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1104998556) (.leaf 1084211857)) (.branch 70 (.leaf 1063875189) (.leaf 1043976039))) (.branch 73 (.branch 72 (.leaf 1024502362) (.leaf 1005442560)) (.branch 74 (.leaf 986785457) (.leaf 968520285))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 950636664) (.branch 77 (.leaf 933124580) (.leaf 915974375))) (.branch 80 (.branch 79 (.leaf 899176726) (.leaf 882722633)) (.branch 81 (.leaf 866603403) (.leaf 850810637)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 835336218) (.leaf 820172298)) (.branch 85 (.leaf 805311287) (.leaf 790745840))) (.branch 88 (.branch 87 (.leaf 776468850) (.leaf 762473437)) (.branch 89 (.leaf 748752935) (.leaf 735300889)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 722111043) (.branch 92 (.leaf 709177330) (.leaf 696493870))) (.branch 95 (.branch 94 (.leaf 684054958) (.leaf 671855057)) (.branch 96 (.leaf 659888795) (.leaf 648150955)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 636636471) (.leaf 625340423)) (.branch 100 (.leaf 614258027) (.leaf 603384635))) (.branch 103 (.branch 102 (.leaf 592715728) (.leaf 582246911)) (.branch 104 (.leaf 571973908) (.leaf 561892560))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 551998818) (.leaf 542288740)) (.branch 108 (.leaf 532758488) (.leaf 523404325))) (.branch 111 (.branch 110 (.leaf 514222607) (.leaf 505209788)) (.branch 112 (.leaf 496362407) (.leaf 487677095)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 479150562) (.leaf 470779603)) (.branch 116 (.leaf 462561091) (.leaf 454491973))) (.branch 119 (.branch 118 (.leaf 446569272) (.leaf 438790082)) (.branch 120 (.leaf 431151565) (.leaf 423650951)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 354).prefactor = (577797520812859/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 354).cutoff/(generalMeanRows 354).c)).2 =
    (440792956175007/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 354).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 354).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 354).q*(generalMeanRows 354).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 354).q*(generalMeanRows 354).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable148.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 354).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 354

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 354).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 354).criticalRate j.val*(generalMeanRows 354).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 354).c*(generalMeanRows 354).criticalPoint j.val)).2-
      (generalMeanRows 354).J/2-(generalMeanRows 354).error (generalMeanGrid j.val)+
      (generalMeanRows 354).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 354).c)).2-
      (generalMeanRows 354).J/2-(generalMeanRows 354).error 4 := by
  have he : (generalMeanRows 354).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 354) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 354)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0354

/-! Kernel-checked entropy margins for general spectral rectangle 355. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0355
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5267451566) (.branch 2 (.leaf 5099616211) (.leaf 4939248970))) (.branch 5 (.branch 4 (.leaf 4785917092) (.leaf 4639218698)) (.branch 6 (.leaf 4498780093) (.leaf 4364253356)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4235314181) (.leaf 4111659948)) (.branch 10 (.leaf 3993007979) (.leaf 3879093961))) (.branch 13 (.branch 12 (.leaf 3769670530) (.leaf 3664505974)) (.branch 14 (.leaf 3563383063) (.leaf 3466097983))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3372459357) (.branch 17 (.leaf 3282287360) (.leaf 3195412899))) (.branch 20 (.branch 19 (.leaf 3111676867) (.leaf 3030929456)) (.branch 21 (.leaf 2953029528) (.leaf 2877844030)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2805247457) (.leaf 2735121362)) (.branch 25 (.leaf 2667353891) (.leaf 2601839368))) (.branch 28 (.branch 27 (.leaf 2538477892) (.leaf 2477174982)) (.branch 29 (.leaf 2417841235) (.leaf 2360392012)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2304747148) (.branch 32 (.leaf 2250830679) (.leaf 2198570587))) (.branch 35 (.branch 34 (.leaf 2147898570) (.leaf 2098749815)) (.branch 36 (.leaf 2051062798) (.leaf 2004779089)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1959843174) (.leaf 1916202288)) (.branch 40 (.leaf 1873806256) (.leaf 1832607348))) (.branch 43 (.branch 42 (.leaf 1792560140) (.leaf 1753621387)) (.branch 44 (.leaf 1715749899) (.leaf 1678906430))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1643053572) (.branch 47 (.leaf 1608155651) (.leaf 1574178636))) (.branch 50 (.branch 49 (.leaf 1541090053) (.leaf 1508858896)) (.branch 51 (.leaf 1477455552) (.leaf 1446851729)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1417020386) (.leaf 1387935663)) (.branch 55 (.leaf 1359572827) (.leaf 1331908210))) (.branch 58 (.branch 57 (.leaf 1304919154) (.leaf 1278583961)) (.branch 59 (.leaf 1252881845) (.leaf 1227792885))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1203297979) (.branch 62 (.leaf 1179378811) (.leaf 1156017805))) (.branch 65 (.branch 64 (.leaf 1133198090) (.leaf 1110903468)) (.branch 66 (.leaf 1089118382) (.leaf 1067827880)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1047017592) (.leaf 1026673698)) (.branch 70 (.leaf 1006782905) (.leaf 987332419))) (.branch 73 (.branch 72 (.leaf 968309926) (.leaf 949703567)) (.branch 74 (.leaf 931501916) (.leaf 913693963))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 896269094) (.branch 77 (.leaf 879217072) (.leaf 862528023))) (.branch 80 (.branch 79 (.leaf 846192416) (.leaf 830201051)) (.branch 81 (.leaf 814545043) (.leaf 799215809)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 784205053) (.leaf 769504758)) (.branch 85 (.leaf 755107169) (.leaf 741004785))) (.branch 88 (.branch 87 (.leaf 727190349) (.leaf 713656835)) (.branch 89 (.leaf 700397440) (.leaf 687405577)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 674674860) (.branch 92 (.leaf 662199105) (.leaf 649972312))) (.branch 95 (.branch 94 (.leaf 637988666) (.leaf 626242526)) (.branch 96 (.leaf 614728417) (.leaf 603441026)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 592375195) (.leaf 581525915)) (.branch 100 (.leaf 570888319) (.leaf 560457681))) (.branch 103 (.branch 102 (.leaf 550229404) (.leaf 540199024)) (.branch 104 (.leaf 530362195) (.leaf 520714694))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 511252410) (.leaf 501971344)) (.branch 108 (.leaf 492867604) (.leaf 483937399))) (.branch 111 (.branch 110 (.leaf 475177039) (.leaf 466582931)) (.branch 112 (.leaf 458151572) (.leaf 449879551)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 441763541) (.leaf 433800303)) (.branch 116 (.leaf 425986675) (.leaf 418319576))) (.branch 119 (.branch 118 (.leaf 410795999) (.leaf 403413011)) (.branch 120 (.leaf 396167752) (.leaf 389057428)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 355).prefactor = (2312424337449059/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 355).cutoff/(generalMeanRows 355).c)).2 =
    (213446595690371/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 355).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 355).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 355).q*(generalMeanRows 355).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 355).q*(generalMeanRows 355).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 355).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 355

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 355).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 355).criticalRate j.val*(generalMeanRows 355).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 355).c*(generalMeanRows 355).criticalPoint j.val)).2-
      (generalMeanRows 355).J/2-(generalMeanRows 355).error (generalMeanGrid j.val)+
      (generalMeanRows 355).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 355).c)).2-
      (generalMeanRows 355).J/2-(generalMeanRows 355).error 4 := by
  have he : (generalMeanRows 355).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 355) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 355)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0355

/-! Kernel-checked entropy margins for general spectral rectangle 356. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0356
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5341388516) (.branch 2 (.leaf 5173901739) (.leaf 5013860061))) (.branch 5 (.branch 4 (.leaf 4860830406) (.leaf 4714410668)) (.branch 6 (.leaf 4574227012) (.leaf 4439931456)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4311199708) (.leaf 4187729227)) (.branch 10 (.leaf 4069237469) (.leaf 3955460312))) (.branch 13 (.branch 12 (.leaf 3846150625) (.leaf 3741076976)) (.branch 14 (.leaf 3640022451) (.leaf 3542783582))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3449169371) (.branch 17 (.leaf 3359000393) (.leaf 3272107981))) (.branch 20 (.branch 19 (.leaf 3188333470) (.leaf 3107527511)) (.branch 21 (.leaf 3029549439) (.leaf 2954266683)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2881554231) (.leaf 2811294135)) (.branch 25 (.leaf 2743375046) (.leaf 2677691792))) (.branch 28 (.branch 27 (.leaf 2614144985) (.leaf 2552640653)) (.branch 29 (.leaf 2493089902) (.leaf 2435408601)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2379517089) (.branch 32 (.leaf 2325339903) (.leaf 2272805523))) (.branch 35 (.branch 34 (.leaf 2221846138) (.leaf 2172397421)) (.branch 36 (.leaf 2124398327) (.leaf 2077790899)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2032520089) (.leaf 1988533588)) (.branch 40 (.leaf 1945781672) (.leaf 1904217052))) (.branch 43 (.branch 42 (.leaf 1863794737) (.leaf 1824471906)) (.branch 44 (.leaf 1786207786) (.leaf 1748963536))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1712702145) (.branch 47 (.leaf 1677388327) (.leaf 1642988433))) (.branch 50 (.branch 49 (.leaf 1609470356) (.leaf 1576803451)) (.branch 51 (.leaf 1544958459) (.leaf 1513907428)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1483623651) (.leaf 1454081594)) (.branch 55 (.leaf 1425256838) (.leaf 1397126023))) (.branch 58 (.branch 57 (.leaf 1369666788) (.leaf 1342857726)) (.branch 59 (.leaf 1316678330) (.leaf 1291108953))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1266130759) (.branch 62 (.leaf 1241725686) (.leaf 1217876408))) (.branch 65 (.branch 64 (.leaf 1194566294) (.leaf 1171779381)) (.branch 66 (.leaf 1149500335) (.leaf 1127714425)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1106407489) (.leaf 1085565914)) (.branch 70 (.leaf 1065176603) (.leaf 1045226953))) (.branch 73 (.branch 72 (.leaf 1025704834) (.leaf 1006598563)) (.branch 74 (.leaf 987896888) (.leaf 969588963))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 951664332) (.branch 77 (.leaf 934112914) (.leaf 916924981))) (.branch 80 (.branch 79 (.leaf 900091144) (.leaf 883602341)) (.branch 81 (.leaf 867449818) (.leaf 851625118)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 836120068) (.leaf 820926766)) (.branch 85 (.leaf 806037571) (.leaf 791445089))) (.branch 88 (.branch 87 (.leaf 777142165) (.leaf 763121873)) (.branch 89 (.leaf 749377505) (.leaf 735902561)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 722690747) (.branch 92 (.leaf 709735957) (.leaf 697032273))) (.branch 95 (.branch 94 (.leaf 684573954) (.leaf 672355431)) (.branch 96 (.leaf 660371298) (.leaf 648616306)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 637085361) (.leaf 625773511)) (.branch 100 (.leaf 614675946) (.leaf 603787992))) (.branch 103 (.branch 102 (.leaf 593105105) (.leaf 582622864)) (.branch 104 (.leaf 572336971) (.leaf 562243243))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 552337611) (.leaf 542616112)) (.branch 108 (.leaf 533074888) (.leaf 523710184))) (.branch 111 (.branch 110 (.leaf 514518338) (.leaf 505495785)) (.branch 112 (.leaf 496639050) (.leaf 487944745)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 479409568) (.leaf 471030298)) (.branch 116 (.leaf 462803793) (.leaf 454726989))) (.branch 119 (.branch 118 (.leaf 446796895) (.leaf 439010592)) (.branch 120 (.leaf 431365232) (.leaf 423858032)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 356).prefactor = (462362690426743/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 356).cutoff/(generalMeanRows 356).c)).2 =
    (17513549771103/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 356).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 356).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 356).q*(generalMeanRows 356).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 356).q*(generalMeanRows 356).cutoff/2-2 = (16742/7797:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable150.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 356).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 356

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 356).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 356).criticalRate j.val*(generalMeanRows 356).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 356).c*(generalMeanRows 356).criticalPoint j.val)).2-
      (generalMeanRows 356).J/2-(generalMeanRows 356).error (generalMeanGrid j.val)+
      (generalMeanRows 356).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 356).c)).2-
      (generalMeanRows 356).J/2-(generalMeanRows 356).error 4 := by
  have he : (generalMeanRows 356).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 356) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 356)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0356

/-! Kernel-checked entropy margins for general spectral rectangle 357. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0357
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5266516154) (.branch 2 (.leaf 5098718162) (.leaf 4938400717))) (.branch 5 (.branch 4 (.leaf 4785129287) (.leaf 4638500395)) (.branch 6 (.leaf 4498138899) (.leaf 4363695575)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4234844947) (.leaf 4111283343)) (.branch 10 (.leaf 3992727140) (.leaf 3878911183))) (.branch 13 (.branch 12 (.leaf 3769587352) (.leaf 3664523264)) (.branch 14 (.leaf 3563501094) (.leaf 3466316498))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3372777635) (.branch 17 (.leaf 3282704270) (.leaf 3195926952))) (.branch 20 (.branch 19 (.leaf 3112286264) (.leaf 3031632130)) (.branch 21 (.leaf 2953823181) (.leaf 2878726169)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2806215428) (.leaf 2736172374)) (.branch 25 (.leaf 2668485047) (.leaf 2603047681))) (.branch 28 (.branch 27 (.leaf 2539760314) (.leaf 2478528417)) (.branch 29 (.leaf 2419262559) (.leaf 2361878086)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2306294833) (.branch 32 (.leaf 2252436847) (.leaf 2200232132))) (.branch 35 (.branch 34 (.leaf 2149612416) (.leaf 2100512926)) (.branch 36 (.leaf 2052872183) (.leaf 2006631811)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1961736354) (.leaf 1918133107)) (.branch 40 (.leaf 1875771963) (.leaf 1834605260))) (.branch 43 (.branch 42 (.leaf 1794587647) (.leaf 1755675953)) (.branch 44 (.leaf 1717829062) (.leaf 1681007807))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1645174855) (.branch 47 (.leaf 1610294611) (.leaf 1576333124))) (.branch 50 (.branch 49 (.leaf 1543257994) (.leaf 1511038294)) (.branch 51 (.leaf 1479644490) (.leaf 1449048365)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1419222951) (.leaf 1390142465)) (.branch 55 (.leaf 1361782246) (.leaf 1334118696))) (.branch 58 (.branch 57 (.leaf 1307129229) (.leaf 1280792214)) (.branch 59 (.leaf 1255086933) (.leaf 1229993529))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1205492966) (.branch 62 (.leaf 1181566987) (.leaf 1158198077))) (.branch 65 (.branch 64 (.leaf 1135369425) (.leaf 1113064889)) (.branch 66 (.leaf 1091268965) (.leaf 1069966756)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1049143943) (.leaf 1028786755)) (.branch 70 (.leaf 1008881947) (.leaf 989416772))) (.branch 73 (.branch 72 (.leaf 970378961) (.leaf 951756695)) (.branch 74 (.leaf 933538592) (.leaf 915713681))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 898271385) (.branch 77 (.leaf 881201506) (.leaf 864494202))) (.branch 80 (.branch 79 (.leaf 848139978) (.leaf 832129665)) (.branch 81 (.leaf 816454408) (.leaf 801105655)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 786075139) (.leaf 771354867)) (.branch 85 (.leaf 756937112) (.leaf 742814397))) (.branch 88 (.branch 87 (.leaf 728979488) (.leaf 715425382)) (.branch 89 (.leaf 702145296) (.leaf 689132663)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 676381118) (.branch 92 (.leaf 663884493) (.leaf 651636807))) (.branch 95 (.branch 94 (.leaf 639632260) (.leaf 627865226)) (.branch 96 (.leaf 616330246) (.leaf 605022020)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 593935403) (.leaf 583065398)) (.branch 100 (.leaf 572407151) (.leaf 561955945))) (.branch 103 (.branch 102 (.leaf 551707195) (.leaf 541656444)) (.branch 104 (.leaf 531799358) (.leaf 522131719))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 512649427) (.leaf 503348490)) (.branch 108 (.leaf 494225020) (.leaf 485275235))) (.branch 111 (.branch 110 (.leaf 476495450) (.leaf 467882077)) (.branch 112 (.leaf 459431619) (.leaf 451140668)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 443005903) (.leaf 435024087)) (.branch 116 (.leaf 427192063) (.leaf 419506752))) (.branch 119 (.branch 118 (.leaf 411965150) (.leaf 404564328)) (.branch 120 (.leaf 397301426) (.leaf 390173653)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 357).prefactor = (2319632712579889/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 357).cutoff/(generalMeanRows 357).c)).2 =
    (214919350805249/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 357).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 357).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 357).q*(generalMeanRows 357).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 357).q*(generalMeanRows 357).cutoff/2-2 = (16742/7797:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable150.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 357).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 357

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 357).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 357).criticalRate j.val*(generalMeanRows 357).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 357).c*(generalMeanRows 357).criticalPoint j.val)).2-
      (generalMeanRows 357).J/2-(generalMeanRows 357).error (generalMeanGrid j.val)+
      (generalMeanRows 357).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 357).c)).2-
      (generalMeanRows 357).J/2-(generalMeanRows 357).error 4 := by
  have he : (generalMeanRows 357).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 357) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 357)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0357

/-! Kernel-checked entropy margins for general spectral rectangle 358. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0358
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5285411381) (.branch 2 (.leaf 5117003777) (.leaf 4956089751))) (.branch 5 (.branch 4 (.leaf 4802235075) (.leaf 4655036501)) (.branch 6 (.leaf 4514119059) (.leaf 4379133641)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4249754837) (.leaf 4125678995)) (.branch 10 (.leaf 4006622472) (.leaf 3892320056))) (.branch 13 (.branch 12 (.leaf 3782523536) (.leaf 3677000412)) (.branch 14 (.leaf 3575532715) (.leaf 3477915933))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3383958039) (.branch 17 (.leaf 3293478593) (.leaf 3206307926))) (.branch 20 (.branch 19 (.leaf 3122286388) (.leaf 3041263663)) (.branch 21 (.leaf 2963098129) (.leaf 2887656279)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2814812182) (.leaf 2744446986)) (.branch 25 (.leaf 2676448457) (.leaf 2610710556))) (.branch 28 (.branch 27 (.leaf 2547133044) (.leaf 2485621117)) (.branch 29 (.leaf 2426085066) (.leaf 2368439966)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2312605376) (.branch 32 (.leaf 2258505074) (.leaf 2206066797))) (.branch 35 (.branch 34 (.leaf 2155222009) (.leaf 2105905678)) (.branch 36 (.leaf 2058056068) (.leaf 2011614550)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1966525423) (.leaf 1922735739)) (.branch 40 (.leaf 1880195154) (.leaf 1838855775))) (.branch 43 (.branch 42 (.leaf 1798672023) (.leaf 1759600505)) (.branch 44 (.leaf 1721599891) (.leaf 1684630802))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1648655700) (.branch 47 (.leaf 1613638791) (.leaf 1579545930))) (.branch 50 (.branch 49 (.leaf 1546344528) (.leaf 1514003476)) (.branch 51 (.leaf 1482493060) (.leaf 1451784891)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1421851835) (.leaf 1392667945)) (.branch 55 (.leaf 1364208404) (.leaf 1336449462))) (.branch 58 (.branch 57 (.leaf 1309368385) (.leaf 1282943400)) (.branch 59 (.leaf 1257153650) (.leaf 1231979147))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1207400724) (.branch 62 (.leaf 1183400002) (.leaf 1159959344))) (.branch 65 (.branch 64 (.leaf 1137061823) (.leaf 1114691186)) (.branch 66 (.leaf 1092831822) (.leaf 1071468728)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1050587486) (.leaf 1030174228)) (.branch 70 (.leaf 1010215615) (.leaf 990698811))) (.branch 73 (.branch 72 (.leaf 971611459) (.leaf 952941660)) (.branch 74 (.leaf 934677949) (.leaf 916809278))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 899324998) (.branch 77 (.leaf 882214836) (.leaf 865468884))) (.branch 80 (.branch 79 (.leaf 849077580) (.leaf 833031691)) (.branch 81 (.leaf 817322303) (.leaf 801940802)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 786878866) (.leaf 772128448)) (.branch 85 (.leaf 757681769) (.leaf 743531303))) (.branch 88 (.branch 87 (.leaf 729669765) (.leaf 716090107)) (.branch 89 (.leaf 702785504) (.leaf 689749343)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 676975220) (.branch 92 (.leaf 664456928) (.leaf 652188447))) (.branch 95 (.branch 94 (.leaf 640163942) (.leaf 628377752)) (.branch 96 (.leaf 616824385) (.leaf 605498509)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 594394948) (.leaf 583508676)) (.branch 100 (.leaf 572834810) (.leaf 562368608))) (.branch 103 (.branch 102 (.leaf 552105458) (.leaf 542040877)) (.branch 104 (.leaf 532170509) (.leaf 522490114))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 512995568) (.leaf 503682857)) (.branch 108 (.leaf 494548077) (.leaf 485587424))) (.branch 111 (.branch 110 (.leaf 476797195) (.leaf 468173784)) (.branch 112 (.leaf 459713678) (.leaf 451413452)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 443269771) (.leaf 435279381)) (.branch 116 (.leaf 427439112) (.leaf 419745871))) (.branch 119 (.branch 118 (.leaf 412196642) (.leaf 404788481)) (.branch 120 (.leaf 397518519) (.leaf 390383952)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 358).prefactor = (2320308740967619/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 358).cutoff/(generalMeanRows 358).c)).2 =
    (213446595690371/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 358).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 358).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 358).q*(generalMeanRows 358).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 358).q*(generalMeanRows 358).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 358).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 358

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 358).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 358).criticalRate j.val*(generalMeanRows 358).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 358).c*(generalMeanRows 358).criticalPoint j.val)).2-
      (generalMeanRows 358).J/2-(generalMeanRows 358).error (generalMeanGrid j.val)+
      (generalMeanRows 358).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 358).c)).2-
      (generalMeanRows 358).J/2-(generalMeanRows 358).error 4 := by
  have he : (generalMeanRows 358).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 358) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 358)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0358

/-! Kernel-checked entropy margins for general spectral rectangle 359. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0359
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5303432432) (.branch 2 (.leaf 5134450628) (.leaf 4972987953))) (.branch 5 (.branch 4 (.leaf 4818608696) (.leaf 4670908236)) (.branch 6 (.leaf 4529510324) (.leaf 4394064662)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4264244731) (.leaf 4139745842)) (.branch 10 (.leaf 4020283386) (.leaf 3905591245))) (.branch 13 (.branch 12 (.leaf 3795420365) (.leaf 3689537452)) (.branch 14 (.leaf 3587723791) (.leaf 3489774177))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3395495926) (.branch 17 (.leaf 3304707983) (.leaf 3217240100))) (.branch 20 (.branch 19 (.leaf 3132932084) (.leaf 3051633105)) (.branch 21 (.leaf 2973201059) (.leaf 2897501983)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2824409519) (.leaf 2753804407)) (.branch 25 (.leaf 2685574031) (.leaf 2619611991))) (.branch 28 (.branch 27 (.leaf 2555817706) (.leaf 2494096049)) (.branch 29 (.leaf 2434357005) (.leaf 2376515359)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2320490397) (.branch 32 (.leaf 2266205635) (.leaf 2213588566))) (.branch 35 (.branch 34 (.leaf 2162570418) (.leaf 2113085938)) (.branch 36 (.leaf 2065073181) (.leaf 2018473318)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1973230455) (.leaf 1929291467)) (.branch 40 (.leaf 1886605837) (.leaf 1845125507))) (.branch 43 (.branch 42 (.leaf 1804804745) (.leaf 1765600009)) (.branch 44 (.leaf 1727469829) (.leaf 1690374691))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1654276929) (.branch 47 (.leaf 1619140627) (.leaf 1584931523))) (.branch 50 (.branch 49 (.leaf 1551616919) (.leaf 1519165597)) (.branch 51 (.leaf 1487547743) (.leaf 1456734873)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1426699757) (.leaf 1397416363)) (.branch 55 (.leaf 1368859786) (.leaf 1341006198))) (.branch 58 (.branch 57 (.leaf 1313832785) (.leaf 1287317702)) (.branch 59 (.leaf 1261440021) (.leaf 1236179682))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1211517458) (.branch 62 (.leaf 1187434903) (.leaf 1163914322))) (.branch 65 (.branch 64 (.leaf 1140938730) (.leaf 1118491819)) (.branch 66 (.leaf 1096557923) (.leaf 1075121990)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1054169551) (.leaf 1033686693)) (.branch 70 (.leaf 1013660029) (.leaf 994076681))) (.branch 73 (.branch 72 (.leaf 974924250) (.leaf 956190794)) (.branch 74 (.leaf 937864811) (.leaf 919935216))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 902391321) (.branch 77 (.leaf 885222821) (.leaf 868419773))) (.branch 80 (.branch 79 (.leaf 851972581) (.leaf 835871982)) (.branch 81 (.leaf 820109031) (.leaf 804675086)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 789561795) (.leaf 774761085)) (.branch 85 (.leaf 760265149) (.leaf 746066435))) (.branch 88 (.branch 87 (.leaf 732157635) (.leaf 718531676)) (.branch 89 (.leaf 705181710) (.leaf 692101101)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 679283424) (.branch 92 (.leaf 666722449) (.leaf 654412138))) (.branch 95 (.branch 94 (.leaf 642346634) (.leaf 630520259)) (.branch 96 (.leaf 618927499) (.leaf 607563006)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 596421587) (.leaf 585498197)) (.branch 100 (.leaf 574787938) (.leaf 564286050))) (.branch 103 (.branch 102 (.leaf 553987907) (.leaf 543889011)) (.branch 104 (.leaf 533984989) (.leaf 524271588))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 514744669) (.leaf 505400206)) (.branch 108 (.leaf 496234280) (.leaf 487243075))) (.branch 111 (.branch 110 (.leaf 478422875) (.leaf 469770062)) (.branch 112 (.leaf 461281110) (.leaf 452952584)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 444781136) (.leaf 436763503)) (.branch 116 (.leaf 428896502) (.leaf 421177030))) (.branch 119 (.branch 118 (.leaf 413602061) (.leaf 406168641)) (.branch 120 (.leaf 398873891) (.leaf 391714998)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 359).prefactor = (186257602161371/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 359).cutoff/(generalMeanRows 359).c)).2 =
    (213446595690371/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 359).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 359).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 359).q*(generalMeanRows 359).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 359).q*(generalMeanRows 359).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 359).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 359

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 359).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 359).criticalRate j.val*(generalMeanRows 359).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 359).c*(generalMeanRows 359).criticalPoint j.val)).2-
      (generalMeanRows 359).J/2-(generalMeanRows 359).error (generalMeanGrid j.val)+
      (generalMeanRows 359).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 359).c)).2-
      (generalMeanRows 359).J/2-(generalMeanRows 359).error 4 := by
  have he : (generalMeanRows 359).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 359) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 359)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0359

/-! Kernel-checked entropy margins for general spectral rectangle 360. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0360
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5360749381) (.branch 2 (.leaf 5192622056) (.leaf 5031925774))) (.branch 5 (.branch 4 (.leaf 4878231419) (.leaf 4731140432)) (.branch 6 (.leaf 4590282140) (.leaf 4455311381)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4325906363) (.leaf 4201766760)) (.branch 10 (.leaf 4082611978) (.leaf 3968179608))) (.branch 13 (.branch 12 (.leaf 3858224018) (.leaf 3752515072)) (.branch 14 (.leaf 3650836976) (.leaf 3552987219))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3458775611) (.branch 17 (.leaf 3368023406) (.leaf 3280562487))) (.branch 20 (.branch 19 (.leaf 3196234638) (.leaf 3114890857)) (.branch 21 (.leaf 3036390736) (.leaf 2960601882)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2887399394) (.leaf 2816665363)) (.branch 25 (.leaf 2748288428) (.leaf 2682163354))) (.branch 28 (.branch 27 (.leaf 2618190641) (.leaf 2556276168)) (.branch 29 (.leaf 2496330856) (.leaf 2438270361)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2382014779) (.branch 32 (.leaf 2327488383) (.leaf 2274619369))) (.branch 35 (.branch 34 (.leaf 2223339624) (.leaf 2173584506)) (.branch 36 (.leaf 2125292644) (.leaf 2078405746)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2032868419) (.leaf 1988628008)) (.branch 40 (.leaf 1945634437) (.leaf 1903840061))) (.branch 43 (.branch 42 (.leaf 1863199536) (.leaf 1823669684)) (.branch 44 (.leaf 1785209380) (.leaf 1747779430))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1711342477) (.branch 47 (.leaf 1675862890) (.leaf 1641306678))) (.branch 50 (.branch 49 (.leaf 1607641401) (.leaf 1574836085)) (.branch 51 (.leaf 1542861147) (.leaf 1511688318)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1481290580) (.leaf 1451642096)) (.branch 55 (.leaf 1422718151) (.leaf 1394495094))) (.branch 58 (.branch 57 (.leaf 1366950284) (.leaf 1340062038)) (.branch 59 (.leaf 1313809583) (.leaf 1288173011))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1263133235) (.branch 62 (.leaf 1238671949) (.leaf 1214771587))) (.branch 65 (.branch 64 (.leaf 1191415292) (.leaf 1168586877)) (.branch 66 (.leaf 1146270793) (.leaf 1124452099)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1103116436) (.leaf 1082249994)) (.branch 70 (.leaf 1061839489) (.leaf 1041872138))) (.branch 73 (.branch 72 (.leaf 1022335637) (.leaf 1003218135)) (.branch 74 (.leaf 984508217) (.leaf 966194883))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 948267528) (.branch 77 (.leaf 930715926) (.leaf 913530210))) (.branch 80 (.branch 79 (.leaf 896700860) (.leaf 880218685)) (.branch 81 (.leaf 864074809) (.leaf 848260659)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 832767947) (.leaf 817588666)) (.branch 85 (.leaf 802715069) (.leaf 788139665))) (.branch 88 (.branch 87 (.leaf 773855203) (.leaf 759854666)) (.branch 89 (.leaf 746131260) (.leaf 732678404)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 719489721) (.branch 92 (.leaf 706559033) (.leaf 693880348))) (.branch 95 (.branch 94 (.leaf 681447857) (.leaf 669255924)) (.branch 96 (.leaf 657299081) (.leaf 645572021)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 634069591) (.leaf 622786786)) (.branch 100 (.leaf 611718745) (.leaf 600860745))) (.branch 103 (.branch 102 (.leaf 590208193) (.leaf 579756627)) (.branch 104 (.leaf 569501706) (.leaf 559439208))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 549565025) (.leaf 539875158)) (.branch 108 (.leaf 530365718) (.leaf 521032913))) (.branch 111 (.branch 110 (.leaf 511873056) (.leaf 502882550)) (.branch 112 (.leaf 494057895) (.leaf 485395676)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 476892568) (.leaf 468545326)) (.branch 116 (.leaf 460350789) (.leaf 452305870))) (.branch 119 (.branch 118 (.leaf 444407562) (.leaf 436652927)) (.branch 120 (.leaf 429039100) (.leaf 421563284)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 360).prefactor = (919063031589207/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 360).cutoff/(generalMeanRows 360).c)).2 =
    (21451405729771/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 360).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 360).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 360).q*(generalMeanRows 360).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 360).q*(generalMeanRows 360).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable151.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 360).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 360

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 360).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 360).criticalRate j.val*(generalMeanRows 360).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 360).c*(generalMeanRows 360).criticalPoint j.val)).2-
      (generalMeanRows 360).J/2-(generalMeanRows 360).error (generalMeanGrid j.val)+
      (generalMeanRows 360).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 360).c)).2-
      (generalMeanRows 360).J/2-(generalMeanRows 360).error 4 := by
  have he : (generalMeanRows 360).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 360) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 360)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0360

/-! Kernel-checked entropy margins for general spectral rectangle 361. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0361
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5305037338) (.branch 2 (.leaf 5136003924) (.leaf 4974463327))) (.branch 5 (.branch 4 (.leaf 4819983454) (.leaf 4672162953)) (.branch 6 (.leaf 4530628529) (.leaf 4395032547)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4265050891) (.leaf 4140381033)) (.branch 10 (.leaf 4020740306) (.leaf 3905864335))) (.branch 13 (.branch 12 (.leaf 3795505622) (.leaf 3689432267)) (.branch 14 (.leaf 3587426798) (.leaf 3489285108))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3394815491) (.branch 17 (.leaf 3303837752) (.leaf 3216182400))) (.branch 20 (.branch 19 (.leaf 3131689900) (.leaf 3050209997)) (.branch 21 (.leaf 2971601082) (.leaf 2895729617)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2822469599) (.leaf 2751702071)) (.branch 25 (.leaf 2683314665) (.leaf 2617201178))) (.branch 28 (.branch 27 (.leaf 2553261186) (.leaf 2491399678)) (.branch 29 (.leaf 2431526722) (.leaf 2373557154)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2317410282) (.branch 32 (.leaf 2263009621) (.leaf 2210282640))) (.branch 35 (.branch 34 (.leaf 2159160522) (.leaf 2109577954)) (.branch 36 (.leaf 2061472913) (.leaf 2014786480)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1969462663) (.leaf 1925448223)) (.branch 40 (.leaf 1882692523) (.leaf 1841147382))) (.branch 43 (.branch 42 (.leaf 1800766932) (.leaf 1761507494)) (.branch 44 (.leaf 1723327457) (.leaf 1686187162))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1650048798) (.branch 47 (.leaf 1614876300) (.leaf 1580635258))) (.branch 50 (.branch 49 (.leaf 1547292823) (.leaf 1514817630)) (.branch 51 (.leaf 1483179717) (.leaf 1452350451)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1422302460) (.leaf 1393009565)) (.branch 55 (.leaf 1364446723) (.leaf 1336589964))) (.branch 58 (.branch 57 (.leaf 1309416340) (.leaf 1282903870)) (.branch 59 (.leaf 1257031495) (.leaf 1231779030))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1207127120) (.branch 62 (.leaf 1183057199) (.leaf 1159551453))) (.branch 65 (.branch 64 (.leaf 1136592783) (.leaf 1114164768)) (.branch 66 (.leaf 1092251634) (.leaf 1070838225)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1049909968) (.leaf 1029452853)) (.branch 70 (.leaf 1009453399) (.leaf 989898635))) (.branch 73 (.branch 72 (.leaf 970776073) (.leaf 952073688)) (.branch 74 (.leaf 933779893) (.leaf 915883525))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 898373821) (.branch 77 (.leaf 881240401) (.leaf 864473253))) (.branch 80 (.branch 79 (.leaf 848062714) (.leaf 831999456)) (.branch 81 (.leaf 816274471) (.leaf 800879059)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 785804811) (.leaf 771043601)) (.branch 85 (.leaf 756587568) (.leaf 742429112))) (.branch 88 (.branch 87 (.leaf 728560879) (.leaf 714975749)) (.branch 89 (.leaf 701666831) (.leaf 688627450)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 675851141) (.branch 92 (.leaf 663331639) (.leaf 651062868))) (.branch 95 (.branch 94 (.leaf 639038942) (.leaf 627254147)) (.branch 96 (.leaf 615702943) (.leaf 604379952)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 593279954) (.leaf 582397881)) (.branch 100 (.leaf 571728810) (.leaf 561267958))) (.branch 103 (.branch 102 (.leaf 551010679) (.leaf 540952455)) (.branch 104 (.leaf 531088895) (.leaf 521415728))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 511928800) (.leaf 502624069)) (.branch 108 (.leaf 493497601) (.leaf 484545569))) (.branch 111 (.branch 110 (.leaf 475764243) (.leaf 467149995)) (.branch 112 (.leaf 458699287) (.leaf 450408676)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 442274805) (.leaf 434294401)) (.branch 116 (.leaf 426464276) (.leaf 418781319))) (.branch 119 (.branch 118 (.leaf 411242498) (.leaf 403844856)) (.branch 120 (.leaf 396585505) (.leaf 389461630)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 361).prefactor = (4627218232346357/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 361).cutoff/(generalMeanRows 361).c)).2 =
    (52628508991043/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 361).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 361).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 361).q*(generalMeanRows 361).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 361).q*(generalMeanRows 361).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable151.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 361).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 361

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 361).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 361).criticalRate j.val*(generalMeanRows 361).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 361).c*(generalMeanRows 361).criticalPoint j.val)).2-
      (generalMeanRows 361).J/2-(generalMeanRows 361).error (generalMeanGrid j.val)+
      (generalMeanRows 361).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 361).c)).2-
      (generalMeanRows 361).J/2-(generalMeanRows 361).error 4 := by
  have he : (generalMeanRows 361).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 361) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 361)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0361

/-! Kernel-checked entropy margins for general spectral rectangle 362. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0362
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5251842974) (.branch 2 (.leaf 5081928969) (.leaf 4919541138))) (.branch 5 (.branch 4 (.leaf 4764248060) (.leaf 4615648895)) (.branch 6 (.leaf 4473370712) (.leaf 4337066109)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4206411081) (.leaf 4081103105)) (.branch 10 (.leaf 3960859416) (.leaf 3845415454))) (.branch 13 (.branch 12 (.leaf 3734523460) (.leaf 3627951197)) (.branch 14 (.leaf 3525480795) (.leaf 3426907693))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3332039681) (.branch 17 (.leaf 3240696017) (.leaf 3152706623))) (.branch 20 (.branch 19 (.leaf 3067911349) (.leaf 2986159293)) (.branch 21 (.leaf 2907308176) (.leaf 2831223770)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2757779369) (.leaf 2686855296)) (.branch 25 (.leaf 2618338455) (.leaf 2552121908))) (.branch 28 (.branch 27 (.leaf 2488104490) (.leaf 2426190450)) (.branch 29 (.leaf 2366289113) (.leaf 2308314573)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2252185400) (.branch 32 (.leaf 2197824376) (.leaf 2145158242))) (.branch 35 (.branch 34 (.leaf 2094117463) (.leaf 2044636012)) (.branch 36 (.leaf 1996651164) (.leaf 1950103308)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1904935768) (.leaf 1861094635)) (.branch 40 (.leaf 1818528615) (.leaf 1777188877))) (.branch 43 (.branch 42 (.leaf 1737028922) (.leaf 1698004449)) (.branch 44 (.leaf 1660073240) (.leaf 1623195041))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1587331460) (.branch 47 (.leaf 1552445867) (.leaf 1518503298))) (.branch 50 (.branch 49 (.leaf 1485470365) (.leaf 1453315178)) (.branch 51 (.leaf 1422007263) (.leaf 1391517490)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1361818001) (.leaf 1332882150)) (.branch 55 (.leaf 1304684432) (.leaf 1277200437))) (.branch 58 (.branch 57 (.leaf 1250406783) (.leaf 1224281072)) (.branch 59 (.leaf 1198801841) (.leaf 1173948509))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1149701341) (.branch 62 (.leaf 1126041405) (.leaf 1102950527))) (.branch 65 (.branch 64 (.leaf 1080411264) (.leaf 1058406860)) (.branch 66 (.leaf 1036921220) (.leaf 1015938874)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 995444949) (.leaf 975425142)) (.branch 70 (.leaf 955865693) (.leaf 936753359))) (.branch 73 (.branch 72 (.leaf 918075391) (.leaf 899819510)) (.branch 74 (.leaf 881973890) (.leaf 864527131))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 847468245) (.branch 77 (.leaf 830786637) (.leaf 814472084))) (.branch 80 (.branch 79 (.leaf 798514723) (.leaf 782905034)) (.branch 81 (.leaf 767633823) (.leaf 752692213)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 738071622) (.leaf 723763761)) (.branch 85 (.leaf 709760614) (.leaf 696054427))) (.branch 88 (.branch 87 (.leaf 682637702) (.leaf 669503181)) (.branch 89 (.leaf 656643842) (.leaf 644052882)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 631723715) (.branch 92 (.leaf 619649959) (.leaf 607825431))) (.branch 95 (.branch 94 (.leaf 596244135) (.leaf 584900259)) (.branch 96 (.leaf 573788167) (.leaf 562902390)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 552237620) (.leaf 541788707)) (.branch 100 (.leaf 531550649) (.leaf 521518591))) (.branch 103 (.branch 102 (.leaf 511687813) (.leaf 502053732)) (.branch 104 (.leaf 492611893) (.leaf 483357967))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 474287741) (.leaf 465397121)) (.branch 108 (.leaf 456682125) (.leaf 448138875))) (.branch 111 (.branch 110 (.leaf 439763601) (.leaf 431552630)) (.branch 112 (.leaf 423502390) (.leaf 415609398)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 407870265) (.leaf 400281687)) (.branch 116 (.leaf 392840448) (.leaf 385543411))) (.branch 119 (.branch 118 (.leaf 378387519) (.leaf 371369792)) (.branch 120 (.leaf 364487324) (.leaf 357737282)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 362).prefactor = (2314745428412053/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 362).cutoff/(generalMeanRows 362).c)).2 =
    (81452120404363/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 362).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 362).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 362).q*(generalMeanRows 362).c/2-2 = (2879/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable152.value]
    have hcontinuation : (generalMeanRows 362).q*(generalMeanRows 362).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 362).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 362

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 362).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 362).criticalRate j.val*(generalMeanRows 362).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 362).c*(generalMeanRows 362).criticalPoint j.val)).2-
      (generalMeanRows 362).J/2-(generalMeanRows 362).error (generalMeanGrid j.val)+
      (generalMeanRows 362).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 362).c)).2-
      (generalMeanRows 362).J/2-(generalMeanRows 362).error 4 := by
  have he : (generalMeanRows 362).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 362) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 362)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0362

/-! Kernel-checked entropy margins for general spectral rectangle 363. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0363
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5111576141) (.branch 2 (.leaf 4941197001) (.leaf 4778415681))) (.branch 5 (.branch 4 (.leaf 4622797547) (.leaf 4473938716)) (.branch 6 (.leaf 4331463375) (.leaf 4195021384)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4064286133) (.leaf 3938952617)) (.branch 10 (.leaf 3818735708) (.leaf 3703368589))) (.branch 13 (.branch 12 (.leaf 3592601341) (.leaf 3486199663)) (.branch 14 (.leaf 3383943708) (.leaf 3285627021))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3191055573) (.branch 17 (.leaf 3100046876) (.leaf 3012429178))) (.branch 20 (.branch 19 (.leaf 2928040717) (.leaf 2846729038)) (.branch 21 (.leaf 2768350372) (.leaf 2692769056)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2619856997) (.leaf 2549493186)) (.branch 25 (.leaf 2481563239) (.leaf 2415958981))) (.branch 28 (.branch 27 (.leaf 2352578048) (.leaf 2291323535)) (.branch 29 (.leaf 2232103651) (.leaf 2174831415)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2119424357) (.branch 32 (.leaf 2065804256) (.leaf 2013896881))) (.branch 35 (.branch 34 (.leaf 1963631761) (.leaf 1914941963)) (.branch 36 (.leaf 1867763888) (.leaf 1822037077)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1777704039) (.leaf 1734710073)) (.branch 40 (.leaf 1693003122) (.leaf 1652533617))) (.branch 43 (.branch 42 (.leaf 1613254344) (.leaf 1575120314)) (.branch 44 (.leaf 1538088641) (.leaf 1502118428))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1467170661) (.branch 47 (.leaf 1433208107) (.leaf 1400195219))) (.branch 50 (.branch 49 (.leaf 1368098051) (.leaf 1336884169)) (.branch 51 (.leaf 1306522575) (.leaf 1276983632)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1248238996) (.leaf 1220261545)) (.branch 55 (.leaf 1193025323) (.leaf 1166505477))) (.branch 58 (.branch 57 (.leaf 1140678203) (.leaf 1115520695)) (.branch 59 (.leaf 1091011092) (.leaf 1067128435))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1043852623) (.branch 62 (.leaf 1021164368) (.leaf 999045159))) (.branch 65 (.branch 64 (.leaf 977477221) (.leaf 956443486)) (.branch 66 (.leaf 935927553) (.leaf 915913660)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 896386654) (.leaf 877331960)) (.branch 70 (.leaf 858735559) (.leaf 840583957))) (.branch 73 (.branch 72 (.leaf 822864167) (.leaf 805563680)) (.branch 74 (.leaf 788670448) (.leaf 772172860))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 756059725) (.branch 77 (.leaf 740320253) (.leaf 724944037))) (.branch 80 (.branch 79 (.leaf 709921035) (.leaf 695241556)) (.branch 81 (.leaf 680896246) (.leaf 666876069)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 653172300) (.leaf 639776505)) (.branch 85 (.leaf 626680534) (.leaf 613876508))) (.branch 88 (.branch 87 (.leaf 601356806) (.leaf 589114056)) (.branch 89 (.leaf 577141124) (.leaf 565431106)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 553977317) (.branch 92 (.leaf 542773283) (.leaf 531812734))) (.branch 95 (.branch 94 (.leaf 521089591) (.leaf 510597967)) (.branch 96 (.leaf 500332151) (.leaf 490286608)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 480455967) (.leaf 470835017)) (.branch 100 (.leaf 461418705) (.leaf 452202121))) (.branch 103 (.branch 102 (.leaf 443180502) (.leaf 434349221)) (.branch 104 (.leaf 425703785) (.leaf 417239827))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 408953104) (.leaf 400839493)) (.branch 108 (.leaf 392894985) (.leaf 385115682))) (.branch 111 (.branch 110 (.leaf 377497792) (.leaf 370037629)) (.branch 112 (.leaf 362731604) (.leaf 355576226)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 348568095) (.leaf 341703904)) (.branch 116 (.leaf 334980431) (.leaf 328394539))) (.branch 119 (.branch 118 (.leaf 321943173) (.leaf 315623356)) (.branch 120 (.leaf 309432187) (.leaf 303366841)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 363).prefactor = (1165540724440251/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 363).cutoff/(generalMeanRows 363).c)).2 =
    (195787002927057/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 363).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 363).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 363).q*(generalMeanRows 363).c/2-2 = (3051/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable153.value]
    have hcontinuation : (generalMeanRows 363).q*(generalMeanRows 363).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 363).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 363

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 363).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 363).criticalRate j.val*(generalMeanRows 363).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 363).c*(generalMeanRows 363).criticalPoint j.val)).2-
      (generalMeanRows 363).J/2-(generalMeanRows 363).error (generalMeanGrid j.val)+
      (generalMeanRows 363).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 363).c)).2-
      (generalMeanRows 363).J/2-(generalMeanRows 363).error 4 := by
  have he : (generalMeanRows 363).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 363) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 363)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0363

/-! Kernel-checked entropy margins for general spectral rectangle 364. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0364
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5160930418) (.branch 2 (.leaf 4991371590) (.leaf 4829376997))) (.branch 5 (.branch 4 (.leaf 4674511455) (.leaf 4526370685)) (.branch 6 (.leaf 4384578613) (.leaf 4248784964)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4118663109) (.leaf 3993908127)) (.branch 10 (.leaf 3874235063) (.leaf 3759377359))) (.branch 13 (.branch 12 (.leaf 3649085429) (.leaf 3543125371)) (.branch 14 (.leaf 3441277794) (.leaf 3343336752))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3249108771) (.branch 17 (.leaf 3158411958) (.leaf 3071075186))) (.branch 20 (.branch 19 (.leaf 2986937351) (.leaf 2905846681)) (.branch 21 (.leaf 2827660110) (.leaf 2752242691)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2679467066) (.leaf 2609212967)) (.branch 25 (.leaf 2541366763) (.leaf 2475821030))) (.branch 28 (.branch 27 (.leaf 2412474165) (.leaf 2351230016)) (.branch 29 (.leaf 2291997551) (.leaf 2234690540)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2179227261) (.branch 32 (.leaf 2125530232) (.leaf 2073525959))) (.branch 35 (.branch 34 (.leaf 2023144692) (.leaf 1974320216)) (.branch 36 (.leaf 1926989633) (.leaf 1881093182)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1836574048) (.leaf 1793378204)) (.branch 40 (.leaf 1751454245) (.leaf 1710753246))) (.branch 43 (.branch 42 (.leaf 1671228623) (.leaf 1632836001)) (.branch 44 (.leaf 1595533095) (.leaf 1559279594))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1524037057) (.branch 47 (.leaf 1489768808) (.leaf 1456439845))) (.branch 50 (.branch 49 (.leaf 1424016749) (.leaf 1392467602)) (.branch 51 (.leaf 1361761905) (.leaf 1331870508)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1302765537) (.leaf 1274420331)) (.branch 55 (.leaf 1246809375) (.leaf 1219908249))) (.branch 58 (.branch 57 (.leaf 1193693566) (.leaf 1168142922)) (.branch 59 (.leaf 1143234849) (.leaf 1118948766))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1095264938) (.branch 62 (.leaf 1072164430) (.leaf 1049629073))) (.branch 65 (.branch 64 (.leaf 1027641422) (.leaf 1006184728)) (.branch 66 (.leaf 985242895) (.leaf 964800460)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 944842553) (.leaf 925354876)) (.branch 70 (.leaf 906323674) (.leaf 887735709))) (.branch 73 (.branch 72 (.leaf 869578238) (.leaf 851838988)) (.branch 74 (.leaf 834506138) (.leaf 817568295))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 801014477) (.branch 77 (.leaf 784834095) (.leaf 769016934))) (.branch 80 (.branch 79 (.leaf 753553136) (.leaf 738433189)) (.branch 81 (.leaf 723647907) (.leaf 709188417)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 695046148) (.leaf 681212816)) (.branch 85 (.leaf 667680411) (.leaf 654441191))) (.branch 88 (.branch 87 (.leaf 641487662) (.leaf 628812577)) (.branch 89 (.leaf 616408919) (.leaf 604269895)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 592388928) (.branch 92 (.leaf 580759643) (.leaf 569375867))) (.branch 95 (.branch 94 (.leaf 558231612) (.leaf 547321077)) (.branch 96 (.leaf 536638634) (.leaf 526178824)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 515936349) (.leaf 505906068)) (.branch 100 (.leaf 496082992) (.leaf 486462273))) (.branch 103 (.branch 102 (.leaf 477039205) (.leaf 467809214)) (.branch 104 (.leaf 458767858) (.leaf 449910818))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 441233894) (.leaf 432733004)) (.branch 108 (.leaf 424404177) (.leaf 416243550))) (.branch 111 (.branch 110 (.leaf 408247365) (.leaf 400411962)) (.branch 112 (.leaf 392733781) (.leaf 385209355)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 377835308) (.leaf 370608352)) (.branch 116 (.leaf 363525282) (.leaf 356582979))) (.branch 119 (.branch 118 (.leaf 349778399) (.leaf 343108579)) (.branch 120 (.leaf 336570628) (.leaf 330161727)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 364).prefactor = (582417849315929/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 364).cutoff/(generalMeanRows 364).c)).2 =
    (405217465901701/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 364).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 364).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 364).q*(generalMeanRows 364).c/2-2 = (593/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable154.value]
    have hcontinuation : (generalMeanRows 364).q*(generalMeanRows 364).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable151.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 364).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 364

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 364).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 364).criticalRate j.val*(generalMeanRows 364).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 364).c*(generalMeanRows 364).criticalPoint j.val)).2-
      (generalMeanRows 364).J/2-(generalMeanRows 364).error (generalMeanGrid j.val)+
      (generalMeanRows 364).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 364).c)).2-
      (generalMeanRows 364).J/2-(generalMeanRows 364).error 4 := by
  have he : (generalMeanRows 364).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 364) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 364)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0364

/-! Kernel-checked entropy margins for general spectral rectangle 365. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0365
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5022571339) (.branch 2 (.leaf 4852639222) (.leaf 4690341671))) (.branch 5 (.branch 4 (.leaf 4535240270) (.leaf 4386927678)) (.branch 6 (.leaf 4245024920) (.leaf 4109178968)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3979060572) (.leaf 3854362315)) (.branch 10 (.leaf 3734796865) (.leaf 3620095392))) (.branch 13 (.branch 12 (.leaf 3510006141) (.leaf 3404293135)) (.branch 14 (.leaf 3302734996) (.leaf 3205123876))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3111264474) (.branch 17 (.leaf 3020973145) (.leaf 2934077083))) (.branch 20 (.branch 19 (.leaf 2850413567) (.leaf 2769829270)) (.branch 21 (.leaf 2692179632) (.leaf 2617328270)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2545146440) (.leaf 2475512543)) (.branch 25 (.leaf 2408311660) (.leaf 2343435130))) (.branch 28 (.branch 27 (.leaf 2280780158) (.leaf 2220249440)) (.branch 29 (.leaf 2161750835) (.leaf 2105197040)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2050505302) (.branch 32 (.leaf 1997597141) (.leaf 1946398100))) (.branch 35 (.branch 34 (.leaf 1896837502) (.leaf 1848848233)) (.branch 36 (.leaf 1802366532) (.leaf 1757331800)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1713686417) (.leaf 1671375575)) (.branch 40 (.leaf 1630347118) (.leaf 1590551396))) (.branch 43 (.branch 42 (.leaf 1551941122) (.leaf 1514471246)) (.branch 44 (.leaf 1478098829) (.leaf 1442782931))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1408484501) (.branch 47 (.leaf 1375166277) (.leaf 1342792690))) (.branch 50 (.branch 49 (.leaf 1311329775) (.leaf 1280745086)) (.branch 51 (.leaf 1251007617) (.leaf 1222087727)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1193957070) (.leaf 1166588529)) (.branch 55 (.leaf 1139956152) (.leaf 1114035093))) (.branch 58 (.branch 57 (.leaf 1088801560) (.leaf 1064232757)) (.branch 59 (.leaf 1040306838) (.leaf 1017002859))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 994300735) (.branch 62 (.leaf 972181196) (.leaf 950625749))) (.branch 65 (.branch 64 (.leaf 929616641) (.leaf 909136820)) (.branch 66 (.leaf 889169909) (.leaf 869700166)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 850712460) (.leaf 832192239)) (.branch 70 (.leaf 814125506) (.leaf 796498790))) (.branch 73 (.branch 72 (.leaf 779299126) (.leaf 762514029)) (.branch 74 (.leaf 746131474) (.leaf 730139874))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 714528060) (.branch 77 (.leaf 699285268) (.leaf 684401111))) (.branch 80 (.branch 79 (.leaf 669865574) (.leaf 655668989)) (.branch 81 (.leaf 641802024) (.leaf 628255669)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 615021220) (.leaf 602090269)) (.branch 85 (.leaf 589454689) (.leaf 577106624))) (.branch 88 (.branch 87 (.leaf 565038477) (.leaf 553242900)) (.branch 89 (.leaf 541712782) (.leaf 530441244)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 519421624) (.branch 92 (.leaf 508647471) (.leaf 498112539))) (.branch 95 (.branch 94 (.leaf 487810775) (.leaf 477736313)) (.branch 96 (.leaf 467883468) (.leaf 458246726)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 448820743) (.leaf 439600332)) (.branch 100 (.leaf 430580461) (.leaf 421756248))) (.branch 103 (.branch 102 (.leaf 413122952) (.leaf 404675971)) (.branch 104 (.leaf 396410835) (.leaf 388323202))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 380408855) (.leaf 372663695)) (.branch 108 (.leaf 365083737) (.leaf 357665108))) (.branch 111 (.branch 110 (.leaf 350404042) (.leaf 343296876)) (.branch 112 (.leaf 336340047) (.leaf 329530088)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 322863627) (.leaf 316337379)) (.branch 116 (.leaf 309948150) (.leaf 303692827))) (.branch 119 (.branch 118 (.leaf 297568380) (.leaf 291571859)) (.branch 120 (.leaf 285700388) (.leaf 279951167)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 365).prefactor = (293230648885809/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 365).cutoff/(generalMeanRows 365).c)).2 =
    (389652949360589/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 365).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 365).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 365).q*(generalMeanRows 365).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 365).q*(generalMeanRows 365).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable151.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 365).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 365

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 365).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 365).criticalRate j.val*(generalMeanRows 365).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 365).c*(generalMeanRows 365).criticalPoint j.val)).2-
      (generalMeanRows 365).J/2-(generalMeanRows 365).error (generalMeanGrid j.val)+
      (generalMeanRows 365).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 365).c)).2-
      (generalMeanRows 365).J/2-(generalMeanRows 365).error 4 := by
  have he : (generalMeanRows 365).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 365) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 365)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0365

/-! Kernel-checked entropy margins for general spectral rectangle 366. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0366
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4976888532) (.branch 2 (.leaf 4806190069) (.leaf 4643159866))) (.branch 5 (.branch 4 (.leaf 4487359940) (.leaf 4338383239)) (.branch 6 (.leaf 4195850948) (.leaf 4059410078)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3928731311) (.leaf 3803507069)) (.branch 10 (.leaf 3683449768) (.leaf 3568290253))) (.branch 13 (.branch 12 (.leaf 3457776371) (.leaf 3351671689)) (.branch 14 (.leaf 3249754318) (.leaf 3151815849))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3057660384) (.branch 17 (.leaf 2967103642) (.leaf 2879972150))) (.branch 20 (.branch 19 (.leaf 2796102496) (.leaf 2715340641)) (.branch 21 (.leaf 2637541294) (.leaf 2562567327)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2490289242) (.leaf 2420584677)) (.branch 25 (.leaf 2353337945) (.leaf 2288439617))) (.branch 28 (.branch 27 (.leaf 2225786125) (.leaf 2165279401)) (.branch 29 (.leaf 2106826536) (.leaf 2050339469)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1995734693) (.branch 32 (.leaf 1942932987) (.leaf 1891859154))) (.branch 35 (.branch 34 (.leaf 1842441794) (.leaf 1794613078)) (.branch 36 (.leaf 1748308543) (.leaf 1703466899)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1660029849) (.leaf 1617941923)) (.branch 40 (.leaf 1577150314) (.leaf 1537604735))) (.branch 43 (.branch 42 (.leaf 1499257282) (.leaf 1462062295)) (.branch 44 (.leaf 1425976247) (.leaf 1390957619))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1356966800) (.branch 47 (.leaf 1323965983) (.leaf 1291919066))) (.branch 50 (.branch 49 (.leaf 1260791569) (.leaf 1230550543)) (.branch 51 (.leaf 1201164498) (.leaf 1172603320)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1144838205) (.leaf 1117841593)) (.branch 55 (.leaf 1091587103) (.leaf 1066049475))) (.branch 58 (.branch 57 (.leaf 1041204514) (.leaf 1017029035)) (.branch 59 (.leaf 993500819) (.leaf 970598559))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 948301819) (.branch 62 (.leaf 926590995) (.leaf 905447266))) (.branch 65 (.branch 64 (.leaf 884852567) (.leaf 864789545)) (.branch 66 (.leaf 845241531) (.leaf 826192506)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 807627068) (.leaf 789530408)) (.branch 70 (.leaf 771888281) (.leaf 754686977))) (.branch 73 (.branch 72 (.leaf 737913304) (.leaf 721554558)) (.branch 74 (.leaf 705598501) (.leaf 690033348))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 674847737) (.branch 77 (.leaf 660030718) (.leaf 645571730))) (.branch 80 (.branch 79 (.leaf 631460588) (.leaf 617687464)) (.branch 81 (.leaf 604242872) (.leaf 591117656)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 578302973) (.leaf 565790282)) (.branch 85 (.leaf 553571329) (.leaf 541638139))) (.branch 88 (.branch 87 (.leaf 529983000) (.leaf 518598457)) (.branch 89 (.leaf 507477297) (.leaf 496612541)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 485997438) (.branch 92 (.leaf 475625449) (.leaf 465490247))) (.branch 95 (.branch 94 (.leaf 455585701) (.leaf 445905872)) (.branch 96 (.leaf 436445008) (.leaf 427197531)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 418158037) (.leaf 409321282)) (.branch 100 (.leaf 400682184) (.leaf 392235810))) (.branch 103 (.branch 102 (.leaf 383977375) (.leaf 375902236)) (.branch 104 (.leaf 368005885) (.leaf 360283944))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 352732163) (.leaf 345346414)) (.branch 108 (.leaf 338122687) (.leaf 331057082))) (.branch 111 (.branch 110 (.leaf 324145815) (.leaf 317385201)) (.branch 112 (.leaf 310771662) (.leaf 304301717)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 297971980) (.leaf 291779158)) (.branch 116 (.leaf 285720048) (.leaf 279791530))) (.branch 119 (.branch 118 (.leaf 273990570) (.leaf 268314216)) (.branch 120 (.leaf 262759590) (.leaf 257323894)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 366).prefactor = (4695065517457429/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 366).cutoff/(generalMeanRows 366).c)).2 =
    (188064841713321/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 366).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 366).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 366).q*(generalMeanRows 366).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 366).q*(generalMeanRows 366).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 366).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 366

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 366).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 366).criticalRate j.val*(generalMeanRows 366).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 366).c*(generalMeanRows 366).criticalPoint j.val)).2-
      (generalMeanRows 366).J/2-(generalMeanRows 366).error (generalMeanGrid j.val)+
      (generalMeanRows 366).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 366).c)).2-
      (generalMeanRows 366).J/2-(generalMeanRows 366).error 4 := by
  have he : (generalMeanRows 366).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 366) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 366)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0366

/-! Kernel-checked entropy margins for general spectral rectangle 367. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0367
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5128129027) (.branch 2 (.leaf 4957161054) (.leaf 4793831882))) (.branch 5 (.branch 4 (.leaf 4637703506) (.leaf 4488368952)) (.branch 6 (.leaf 4345449575) (.leaf 4208592633)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4077469132) (.leaf 3951771878)) (.branch 10 (.leaf 3831213735) (.leaf 3715526040))) (.branch 13 (.branch 12 (.leaf 3604457182) (.leaf 3497771306)) (.branch 14 (.leaf 3395247138) (.leaf 3296676912))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3201865399) (.branch 17 (.leaf 3110629007) (.leaf 3022794972))) (.branch 20 (.branch 19 (.leaf 2938200602) (.leaf 2856692592)) (.branch 21 (.leaf 2778126392) (.leaf 2702365622)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2629281534) (.leaf 2558752518)) (.branch 25 (.leaf 2490663642) (.leaf 2424906224))) (.branch 28 (.branch 27 (.leaf 2361377443) (.leaf 2299979970)) (.branch 29 (.leaf 2240621632) (.leaf 2183215095)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2127677570) (.branch 32 (.leaf 2073930543) (.leaf 2021899516))) (.branch 35 (.branch 34 (.leaf 1971513777) (.leaf 1922706170)) (.branch 36 (.leaf 1875412896) (.leaf 1829573316)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1785129770) (.leaf 1742027410)) (.branch 40 (.leaf 1700214041) (.leaf 1659639972))) (.branch 43 (.branch 42 (.leaf 1620257878) (.leaf 1582022670)) (.branch 44 (.leaf 1544891370) (.leaf 1508823002))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1473778477) (.branch 47 (.leaf 1439720497) (.leaf 1406613457))) (.branch 50 (.branch 49 (.leaf 1374423356) (.leaf 1343117716)) (.branch 51 (.leaf 1312665495) (.leaf 1283037019)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1254203911) (.leaf 1226139020)) (.branch 55 (.leaf 1198816363) (.leaf 1172211065))) (.branch 58 (.branch 57 (.leaf 1146299302) (.leaf 1121058247)) (.branch 59 (.leaf 1096466028) (.leaf 1072501669))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1049145059) (.branch 62 (.leaf 1026376897) (.leaf 1004178665))) (.branch 65 (.branch 64 (.leaf 982532580) (.leaf 961421565)) (.branch 66 (.leaf 940829215) (.leaf 920739761)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 901138046) (.leaf 882009492)) (.branch 70 (.leaf 863340075) (.leaf 845116298))) (.branch 73 (.branch 72 (.leaf 827325171) (.leaf 809954182)) (.branch 74 (.leaf 792991280) (.leaf 776424852))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 760243704) (.branch 77 (.leaf 744437045) (.leaf 728994463))) (.branch 80 (.branch 79 (.leaf 713905915) (.leaf 699161709)) (.branch 81 (.leaf 684752486) (.leaf 670669208)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 656903147) (.leaf 643445867)) (.branch 85 (.leaf 630289214) (.leaf 617425306))) (.branch 88 (.branch 87 (.leaf 604846517) (.leaf 592545473)) (.branch 89 (.leaf 580515036) (.leaf 568748298)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 557238569) (.branch 92 (.leaf 545979371) (.leaf 534964428))) (.branch 95 (.branch 94 (.leaf 524187660) (.leaf 513643172)) (.branch 96 (.leaf 503325248) (.leaf 493228349)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 483347097) (.leaf 473676278)) (.branch 100 (.leaf 464210830) (.leaf 454945840))) (.branch 103 (.branch 102 (.leaf 445876537) (.leaf 436998289)) (.branch 104 (.leaf 428306595) (.leaf 419797083))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 411465504) (.leaf 403307727)) (.branch 108 (.leaf 395319737) (.leaf 387497630))) (.branch 111 (.branch 110 (.leaf 379837606) (.leaf 372335972)) (.branch 112 (.leaf 364989132) (.leaf 357793587)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 350745932) (.leaf 343842852)) (.branch 116 (.leaf 337081117) (.leaf 330457584))) (.branch 119 (.branch 118 (.leaf 323969188) (.leaf 317612948)) (.branch 120 (.leaf 311385954) (.leaf 305285372)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 367).prefactor = (4693386224904391/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 367).cutoff/(generalMeanRows 367).c)).2 =
    (197242608030787/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 367).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 367).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 367).q*(generalMeanRows 367).c/2-2 = (3051/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable153.value]
    have hcontinuation : (generalMeanRows 367).q*(generalMeanRows 367).cutoff/2-2 = (16558/7889:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable155.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 367).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 367

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 367).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 367).criticalRate j.val*(generalMeanRows 367).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 367).c*(generalMeanRows 367).criticalPoint j.val)).2-
      (generalMeanRows 367).J/2-(generalMeanRows 367).error (generalMeanGrid j.val)+
      (generalMeanRows 367).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 367).c)).2-
      (generalMeanRows 367).J/2-(generalMeanRows 367).error 4 := by
  have he : (generalMeanRows 367).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 367) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 367)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0367

/-! Kernel-checked entropy margins for general spectral rectangle 368. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0368
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5059517353) (.branch 2 (.leaf 4888375743) (.leaf 4724908317))) (.branch 5 (.branch 4 (.leaf 4568675415) (.leaf 4419268500)) (.branch 6 (.leaf 4276307439) (.leaf 4139438085)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4008330103) (.leaf 3882675026)) (.branch 10 (.leaf 3762184501) (.leaf 3646588708))) (.branch 13 (.branch 12 (.leaf 3535634929) (.leaf 3429086251)) (.branch 14 (.leaf 3326720387) (.leaf 3228328603))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3133714739) (.branch 17 (.leaf 3042694314) (.leaf 2955093706))) (.branch 20 (.branch 19 (.leaf 2870749404) (.leaf 2789507314)) (.branch 21 (.leaf 2711222128) (.leaf 2635756735)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2562981686) (.leaf 2492774697)) (.branch 25 (.leaf 2425020184) (.leaf 2359608839))) (.branch 28 (.branch 27 (.leaf 2296437238) (.leaf 2235407470)) (.branch 29 (.leaf 2176426803) (.leaf 2119407362)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2064265837) (.branch 32 (.leaf 2010923210) (.leaf 1959304502))) (.branch 35 (.branch 34 (.leaf 1909338531) (.leaf 1860957692)) (.branch 36 (.leaf 1814097750) (.leaf 1768697646)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1724699317) (.leaf 1682047525)) (.branch 40 (.leaf 1640689696) (.leaf 1600575777))) (.branch 43 (.branch 42 (.leaf 1561658093) (.leaf 1523891216)) (.branch 44 (.leaf 1487231843) (.leaf 1451638683))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1417072344) (.branch 47 (.leaf 1383495236) (.leaf 1350871471))) (.branch 50 (.branch 49 (.leaf 1319166779) (.leaf 1288348418)) (.branch 51 (.leaf 1258385094) (.leaf 1229246891)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1200905197) (.leaf 1173332637)) (.branch 55 (.leaf 1146503010) (.leaf 1120391232))) (.branch 58 (.branch 57 (.leaf 1094973279) (.leaf 1070226132)) (.branch 59 (.leaf 1046127730) (.leaf 1022656922))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 999793422) (.branch 62 (.leaf 977517768) (.leaf 955811280))) (.branch 65 (.branch 64 (.leaf 934656026) (.leaf 914034782)) (.branch 66 (.leaf 893931003) (.leaf 874328787)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 855212847) (.leaf 836568484)) (.branch 70 (.leaf 818381555) (.leaf 800638452))) (.branch 73 (.branch 72 (.leaf 783326075) (.leaf 766431812)) (.branch 74 (.leaf 749943512) (.leaf 733849469))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 718138401) (.branch 77 (.leaf 702799430) (.leaf 687822065))) (.branch 80 (.branch 79 (.leaf 673196186) (.leaf 658912026)) (.branch 81 (.leaf 644960158) (.leaf 631331480)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 618017200) (.leaf 605008823)) (.branch 85 (.leaf 592298141) (.leaf 579877219))) (.branch 88 (.branch 87 (.leaf 567738382) (.leaf 555874209)) (.branch 89 (.leaf 544277519) (.leaf 532941364)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 521859016) (.branch 92 (.leaf 511023962) (.leaf 500429894))) (.branch 95 (.branch 94 (.leaf 490070699) (.leaf 479940456)) (.branch 96 (.leaf 470033424) (.leaf 460344039)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 450866903) (.leaf 441596782)) (.branch 100 (.leaf 432528597) (.leaf 423657420))) (.branch 103 (.branch 102 (.leaf 414978465) (.leaf 406487090)) (.branch 104 (.leaf 398178784) (.leaf 390049165))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 382093978) (.leaf 374309088)) (.branch 108 (.leaf 366690475) (.leaf 359234232))) (.branch 111 (.branch 110 (.leaf 351936560) (.leaf 344793765)) (.branch 112 (.leaf 337802253) (.leaf 330958529)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324259190) (.leaf 317700926)) (.branch 116 (.leaf 311280516) (.leaf 304994822))) (.branch 119 (.branch 118 (.leaf 298840789) (.leaf 292815443)) (.branch 120 (.leaf 286915885) (.leaf 281139295)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 368).prefactor = (941956674263761/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 368).cutoff/(generalMeanRows 368).c)).2 =
    (48341654907157/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 368).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 368).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 368).q*(generalMeanRows 368).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 368).q*(generalMeanRows 368).cutoff/2-2 = (16558/7889:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable155.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 368).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 368

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 368).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 368).criticalRate j.val*(generalMeanRows 368).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 368).c*(generalMeanRows 368).criticalPoint j.val)).2-
      (generalMeanRows 368).J/2-(generalMeanRows 368).error (generalMeanGrid j.val)+
      (generalMeanRows 368).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 368).c)).2-
      (generalMeanRows 368).J/2-(generalMeanRows 368).error 4 := by
  have he : (generalMeanRows 368).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 368) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 368)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0368

/-! Kernel-checked entropy margins for general spectral rectangle 369. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0369
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5079144126) (.branch 2 (.leaf 4907384114) (.leaf 4743311180))) (.branch 5 (.branch 4 (.leaf 4586485952) (.leaf 4436500117)) (.branch 6 (.leaf 4292973712) (.leaf 4155552705)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4023906829) (.leaf 3897727643)) (.branch 10 (.leaf 3776726781) (.leaf 3660634374))) (.branch 13 (.branch 12 (.leaf 3549197624) (.leaf 3442179511)) (.branch 14 (.leaf 3339357615) (.leaf 3240523047))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3145479474) (.branch 17 (.leaf 3054042223) (.leaf 2966037467))) (.branch 20 (.branch 19 (.leaf 2881301475) (.leaf 2799679925)) (.branch 21 (.leaf 2721027269) (.leaf 2645206150)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2572086868) (.leaf 2501546879)) (.branch 25 (.leaf 2433470338) (.leaf 2367747676))) (.branch 28 (.branch 27 (.leaf 2304275201) (.leaf 2242954738)) (.branch 29 (.leaf 2183693287) (.leaf 2126402706)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2070999424) (.branch 32 (.leaf 2017404161) (.leaf 1965541675))) (.branch 35 (.branch 34 (.leaf 1915340528) (.leaf 1866732863)) (.branch 36 (.leaf 1819654194) (.leaf 1774043215)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1729841622) (.leaf 1686993937)) (.branch 40 (.leaf 1645447355) (.leaf 1605151595))) (.branch 43 (.branch 42 (.leaf 1566058757) (.leaf 1528123195)) (.branch 44 (.leaf 1491301393) (.leaf 1455551850))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1420834972) (.branch 47 (.leaf 1387112969) (.leaf 1354349763))) (.branch 50 (.branch 49 (.leaf 1322510894) (.leaf 1291563436)) (.branch 51 (.leaf 1261475920) (.leaf 1232218256)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1203761665) (.leaf 1176078608)) (.branch 55 (.leaf 1149142727) (.leaf 1122928786))) (.branch 58 (.branch 57 (.leaf 1097412610) (.leaf 1072571039)) (.branch 59 (.leaf 1048381871) (.leaf 1024823821))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1001876472) (.branch 62 (.leaf 979520236) (.leaf 957736312))) (.branch 65 (.branch 64 (.leaf 936506649) (.leaf 915813910)) (.branch 66 (.leaf 895641439) (.leaf 875973229)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 856793889) (.leaf 838088621)) (.branch 70 (.leaf 819843188) (.leaf 802043888))) (.branch 73 (.branch 72 (.leaf 784677533) (.leaf 767731424)) (.branch 74 (.leaf 751193329) (.leaf 735051462))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 719294463) (.branch 77 (.leaf 703911381) (.leaf 688891654))) (.branch 80 (.branch 79 (.leaf 674225092) (.leaf 659901863)) (.branch 81 (.leaf 645912478) (.leaf 632247770)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 618898891) (.leaf 605857288)) (.branch 85 (.leaf 593114699) (.leaf 580663135))) (.branch 88 (.branch 87 (.leaf 568494873) (.leaf 556602443)) (.branch 89 (.leaf 544978616) (.leaf 533616400)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 522509024) (.branch 92 (.leaf 511649933) (.leaf 501032779))) (.branch 95 (.branch 94 (.leaf 490651412) (.leaf 480499873)) (.branch 96 (.leaf 470572387) (.leaf 460863354)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 451367345) (.leaf 442079094)) (.branch 100 (.leaf 432993493) (.leaf 424105583))) (.branch 103 (.branch 102 (.leaf 415410554) (.leaf 406903734)) (.branch 104 (.leaf 398580587) (.leaf 390436708))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 382467818) (.leaf 374669758)) (.branch 108 (.leaf 367038487) (.leaf 359570079))) (.branch 111 (.branch 110 (.leaf 352260713) (.leaf 345106676)) (.branch 112 (.leaf 338104356) (.leaf 331250241)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324540911) (.leaf 317973040)) (.branch 116 (.leaf 311543389) (.leaf 305248808))) (.branch 119 (.branch 118 (.leaf 299086227) (.leaf 293052658)) (.branch 120 (.leaf 287145190) (.leaf 281360987)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 369).prefactor = (942320760483571/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 369).cutoff/(generalMeanRows 369).c)).2 =
    (191911014524899/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 369).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 369).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 369).q*(generalMeanRows 369).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 369).q*(generalMeanRows 369).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 369).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 369

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 369).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 369).criticalRate j.val*(generalMeanRows 369).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 369).c*(generalMeanRows 369).criticalPoint j.val)).2-
      (generalMeanRows 369).J/2-(generalMeanRows 369).error (generalMeanGrid j.val)+
      (generalMeanRows 369).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 369).c)).2-
      (generalMeanRows 369).J/2-(generalMeanRows 369).error 4 := by
  have he : (generalMeanRows 369).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 369) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 369)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0369

/-! Kernel-checked entropy margins for general spectral rectangle 370. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0370
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5012012287) (.branch 2 (.leaf 4840109142) (.leaf 4675928374))) (.branch 5 (.branch 4 (.leaf 4519028910) (.leaf 4369000825)) (.branch 6 (.leaf 4225462631) (.leaf 4088058846)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3956457831) (.leaf 3830349834)) (.branch 10 (.leaf 3709445245) (.leaf 3593473006))) (.branch 13 (.branch 12 (.leaf 3482179187) (.leaf 3375325684)) (.branch 14 (.leaf 3272689044) (.leaf 3174059387))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3079239432) (.branch 17 (.leaf 2988043597) (.leaf 2900297186))) (.branch 20 (.branch 19 (.leaf 2815835633) (.leaf 2734503812)) (.branch 21 (.leaf 2656155405) (.leaf 2580652319)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2507864141) (.leaf 2437667644)) (.branch 25 (.leaf 2369946327) (.leaf 2304589988))) (.branch 28 (.branch 27 (.leaf 2241494327) (.leaf 2180560584)) (.branch 29 (.leaf 2121695195) (.leaf 2064809478)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2009819336) (.branch 32 (.leaf 1956644988) (.leaf 1905210709))) (.branch 35 (.branch 34 (.leaf 1855444592) (.leaf 1807278331)) (.branch 36 (.leaf 1760647008) (.leaf 1715488899)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1671745298) (.leaf 1629360341)) (.branch 40 (.leaf 1588280851) (.leaf 1548456185))) (.branch 43 (.branch 42 (.leaf 1509838099) (.leaf 1472380613)) (.branch 44 (.leaf 1436039892) (.leaf 1400774125))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1366543420) (.branch 47 (.leaf 1333309704) (.leaf 1301036620))) (.branch 50 (.branch 49 (.leaf 1269689444) (.leaf 1239234997)) (.branch 51 (.leaf 1209641563) (.leaf 1180878818)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1152917755) (.leaf 1125730618)) (.branch 55 (.leaf 1099290840) (.leaf 1073572983))) (.branch 58 (.branch 57 (.leaf 1048552681) (.leaf 1024206588)) (.branch 59 (.leaf 1000512324) (.leaf 977448434))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 954994339) (.branch 62 (.leaf 933130292) (.leaf 911837344))) (.branch 65 (.branch 64 (.leaf 891097301) (.leaf 870892687)) (.branch 66 (.leaf 851206716) (.leaf 832023254)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 813326793) (.leaf 795102418)) (.branch 70 (.leaf 777335784) (.leaf 760013085))) (.branch 73 (.branch 72 (.leaf 743121033) (.leaf 726646837)) (.branch 74 (.leaf 710578173) (.leaf 694903170))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 679610389) (.branch 77 (.leaf 664688801) (.leaf 650127770))) (.branch 80 (.branch 79 (.leaf 635917041) (.leaf 622046714)) (.branch 81 (.leaf 608507239) (.leaf 595289393)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 582384272) (.leaf 569783274)) (.branch 85 (.leaf 557478088) (.leaf 545460681))) (.branch 88 (.branch 87 (.leaf 533723288) (.leaf 522258400)) (.branch 89 (.leaf 511058753) (.leaf 500117321)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 489427303) (.branch 92 (.leaf 478982115) (.leaf 468775385))) (.branch 95 (.branch 94 (.leaf 458800938) (.leaf 449052796)) (.branch 96 (.leaf 439525163) (.leaf 430212423)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 421109134) (.leaf 412210015)) (.branch 100 (.leaf 403509947) (.leaf 395003964))) (.branch 103 (.branch 102 (.leaf 386687247) (.leaf 378555118)) (.branch 104 (.leaf 370603039) (.leaf 362826602))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 355221525) (.leaf 347783653)) (.branch 108 (.leaf 340508944) (.leaf 333393476))) (.branch 111 (.branch 110 (.leaf 326433432) (.leaf 319625107)) (.branch 112 (.leaf 312964893) (.leaf 306449288)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300074879) (.leaf 293838353)) (.branch 116 (.leaf 287736480) (.leaf 281766123))) (.branch 119 (.branch 118 (.leaf 275924224) (.leaf 270207809)) (.branch 120 (.leaf 264613982) (.leaf 259139924)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 370).prefactor = (591025042899193/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 370).cutoff/(generalMeanRows 370).c)).2 =
    (188064841713321/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 370).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 370).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 370).q*(generalMeanRows 370).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 370).q*(generalMeanRows 370).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 370).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 370

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 370).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 370).criticalRate j.val*(generalMeanRows 370).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 370).c*(generalMeanRows 370).criticalPoint j.val)).2-
      (generalMeanRows 370).J/2-(generalMeanRows 370).error (generalMeanGrid j.val)+
      (generalMeanRows 370).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 370).c)).2-
      (generalMeanRows 370).J/2-(generalMeanRows 370).error 4 := by
  have he : (generalMeanRows 370).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 370) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 370)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0370

/-! Kernel-checked entropy margins for general spectral rectangle 371. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0371
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4816148248) (.branch 2 (.leaf 4641271628) (.leaf 4474434595))) (.branch 5 (.branch 4 (.leaf 4315175976) (.leaf 4163067143)) (.branch 6 (.leaf 4017709177) (.leaf 3878730340)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3745783807) (.leaf 3618545635)) (.branch 10 (.leaf 3496712931) (.leaf 3380002200))) (.branch 13 (.branch 12 (.leaf 3268147853) (.leaf 3160900850)) (.branch 14 (.leaf 3058027471) (.leaf 2959308190))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2864536660) (.branch 17 (.leaf 2773518770) (.leaf 2686071796))) (.branch 20 (.branch 19 (.leaf 2602023610) (.leaf 2521211964)) (.branch 21 (.leaf 2443483826) (.leaf 2368694764)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2296708391) (.leaf 2227395836)) (.branch 25 (.leaf 2160635269) (.leaf 2096311452))) (.branch 28 (.branch 27 (.leaf 2034315330) (.leaf 1974543640)) (.branch 29 (.leaf 1916898566) (.leaf 1861287400)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1807622236) (.branch 32 (.leaf 1755819688) (.leaf 1705800617))) (.branch 35 (.branch 34 (.leaf 1657489886) (.leaf 1610816126)) (.branch 36 (.leaf 1565711519) (.leaf 1522111595)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1479955043) (.leaf 1439183532)) (.branch 40 (.leaf 1399741544) (.leaf 1361576223))) (.branch 43 (.branch 42 (.leaf 1324637221) (.leaf 1288876566)) (.branch 44 (.leaf 1254248534) (.leaf 1220709524))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1188217947) (.branch 47 (.leaf 1156734117) (.leaf 1126220156))) (.branch 50 (.branch 49 (.leaf 1096639893) (.leaf 1067958776)) (.branch 51 (.leaf 1040143792) (.leaf 1013163387)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 986987386) (.leaf 961586930)) (.branch 55 (.leaf 936934408) (.leaf 913003390))) (.branch 58 (.branch 57 (.leaf 889768574) (.leaf 867205726)) (.branch 59 (.leaf 845291630) (.leaf 824004037))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 803321620) (.branch 62 (.leaf 783223925) (.leaf 763691334))) (.branch 65 (.branch 64 (.leaf 744705023) (.leaf 726246922)) (.branch 66 (.leaf 708299686) (.leaf 690846654)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 673871821) (.leaf 657359806)) (.branch 70 (.leaf 641295826) (.leaf 625665664))) (.branch 73 (.branch 72 (.leaf 610455650) (.leaf 595652628)) (.branch 74 (.leaf 581243941) (.leaf 567217402))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 553561280) (.branch 77 (.leaf 540264272) (.leaf 527315491))) (.branch 80 (.branch 79 (.leaf 514704446) (.leaf 502421023)) (.branch 81 (.leaf 490455471) (.leaf 478798384)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 467440689) (.leaf 456373633)) (.branch 85 (.leaf 445588766) (.leaf 435077928))) (.branch 88 (.branch 87 (.leaf 424833243) (.leaf 414847101)) (.branch 89 (.leaf 405112151) (.leaf 395621287)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 386367643) (.branch 92 (.leaf 377344578) (.leaf 368545673))) (.branch 95 (.branch 94 (.leaf 359964716) (.leaf 351595698)) (.branch 96 (.leaf 343432806) (.leaf 335470409)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 327703060) (.leaf 320125481)) (.branch 100 (.leaf 312732563) (.leaf 305519356))) (.branch 103 (.branch 102 (.leaf 298481061) (.leaf 291613030)) (.branch 104 (.leaf 284910758) (.leaf 278369875))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 271986145) (.leaf 265755460)) (.branch 108 (.leaf 259673833) (.leaf 253737399))) (.branch 111 (.branch 110 (.leaf 247942404) (.leaf 242285207)) (.branch 112 (.leaf 236762271) (.leaf 231370166)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 226105557) (.leaf 220965207)) (.branch 116 (.leaf 215945972) (.leaf 211044796))) (.branch 119 (.branch 118 (.leaf 206258713) (.leaf 201584836)) (.branch 120 (.leaf 197020361) (.leaf 192562565)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 371).prefactor = (4870295257636871/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 371).cutoff/(generalMeanRows 371).c)).2 =
    (43973685107257/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 371).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 371).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 371).q*(generalMeanRows 371).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 371).q*(generalMeanRows 371).cutoff/2-2 = (4234/2019:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable149.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 371).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 371

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 371).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 371).criticalRate j.val*(generalMeanRows 371).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 371).c*(generalMeanRows 371).criticalPoint j.val)).2-
      (generalMeanRows 371).J/2-(generalMeanRows 371).error (generalMeanGrid j.val)+
      (generalMeanRows 371).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 371).c)).2-
      (generalMeanRows 371).J/2-(generalMeanRows 371).error 4 := by
  have he : (generalMeanRows 371).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 371) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 371)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0371

/-! Kernel-checked entropy margins for general spectral rectangle 372. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0372
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4745165804) (.branch 2 (.leaf 4570609535) (.leaf 4404112217))) (.branch 5 (.branch 4 (.leaf 4245211636) (.leaf 4093478170)) (.branch 6 (.leaf 3948511952) (.leaf 3809940335)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3677415624) (.leaf 3550613041)) (.branch 10 (.leaf 3429228895) (.leaf 3312978924))) (.branch 13 (.branch 12 (.leaf 3201596803) (.leaf 3094832783)) (.branch 14 (.leaf 2992452465) (.leaf 2894235670))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2799975421) (.branch 17 (.leaf 2709477003) (.leaf 2622557111))) (.branch 20 (.branch 19 (.leaf 2539043057) (.leaf 2458772056)) (.branch 21 (.leaf 2381590556) (.leaf 2307353627)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2235924402) (.leaf 2167173549)) (.branch 25 (.leaf 2100978793) (.leaf 2037224469))) (.branch 28 (.branch 27 (.leaf 1975801110) (.leaf 1916605059)) (.branch 29 (.leaf 1859538118) (.leaf 1804507214)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1751424090) (.branch 32 (.leaf 1700205021) (.leaf 1650770544))) (.branch 35 (.branch 34 (.leaf 1603045212) (.leaf 1556957354)) (.branch 36 (.leaf 1512438867) (.leaf 1469425005)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1427854193) (.leaf 1387667846)) (.branch 40 (.leaf 1348810205) (.leaf 1311228180))) (.branch 43 (.branch 42 (.leaf 1274871202) (.leaf 1239691088)) (.branch 44 (.leaf 1205641907) (.leaf 1172679866))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1140763190) (.branch 47 (.leaf 1109852019) (.leaf 1079908302))) (.branch 50 (.branch 49 (.leaf 1050895710) (.leaf 1022779538)) (.branch 51 (.leaf 995526628) (.leaf 969105286)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 943485209) (.leaf 918637412)) (.branch 55 (.leaf 894534165) (.leaf 871148929))) (.branch 58 (.branch 57 (.leaf 848456296) (.leaf 826431933)) (.branch 59 (.leaf 805052531) (.leaf 784295754))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 764140189) (.branch 62 (.leaf 744565309) (.leaf 725551421))) (.branch 65 (.branch 64 (.leaf 707079634) (.leaf 689131818)) (.branch 66 (.leaf 671690567) (.leaf 654739167)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 638261564) (.leaf 622242331)) (.branch 70 (.leaf 606666644) (.leaf 591520250))) (.branch 73 (.branch 72 (.leaf 576789441) (.leaf 562461033)) (.branch 74 (.leaf 548522341) (.leaf 534961156))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 521765723) (.branch 77 (.leaf 508924724) (.leaf 496427257))) (.branch 80 (.branch 79 (.leaf 484262817) (.leaf 472421282)) (.branch 81 (.leaf 460892893) (.leaf 449668241)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 438738252) (.leaf 428094172)) (.branch 85 (.leaf 417727552) (.leaf 407630239))) (.branch 88 (.branch 87 (.leaf 397794363) (.leaf 388212322)) (.branch 89 (.leaf 378876775) (.leaf 369780629)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 360917031) (.branch 92 (.leaf 352279358) (.leaf 343861204))) (.branch 95 (.branch 94 (.leaf 335656377) (.leaf 327658889)) (.branch 96 (.leaf 319862945) (.leaf 312262939)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 304853447) (.leaf 297629216)) (.branch 100 (.leaf 290585161) (.leaf 283716359))) (.branch 103 (.branch 102 (.leaf 277018040) (.leaf 270485585)) (.branch 104 (.leaf 264114516) (.leaf 257900495))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 251839317) (.leaf 245926905)) (.branch 108 (.leaf 240159306) (.leaf 234532685))) (.branch 111 (.branch 110 (.leaf 229043323) (.leaf 223687614)) (.branch 112 (.leaf 218462056) (.leaf 213363251)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 208387902) (.leaf 203532809)) (.branch 116 (.leaf 198794861) (.leaf 194171042))) (.branch 119 (.branch 118 (.leaf 189658420) (.leaf 185254146)) (.branch 120 (.leaf 180955456) (.leaf 176759660)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 372).prefactor = (2439454696807973/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 372).cutoff/(generalMeanRows 372).c)).2 =
    (344184881472839/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 372).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 372).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 372).q*(generalMeanRows 372).c/2-2 = (113/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable124.value]
    have hcontinuation : (generalMeanRows 372).q*(generalMeanRows 372).cutoff/2-2 = (4234/2019:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable149.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 372).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 372

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 372).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 372).criticalRate j.val*(generalMeanRows 372).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 372).c*(generalMeanRows 372).criticalPoint j.val)).2-
      (generalMeanRows 372).J/2-(generalMeanRows 372).error (generalMeanGrid j.val)+
      (generalMeanRows 372).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 372).c)).2-
      (generalMeanRows 372).J/2-(generalMeanRows 372).error 4 := by
  have he : (generalMeanRows 372).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 372) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 372)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0372

/-! Kernel-checked entropy margins for general spectral rectangle 373. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0373
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5295214303) (.branch 2 (.leaf 5129221835) (.leaf 4970635666))) (.branch 5 (.branch 4 (.leaf 4819022852) (.leaf 4673981504)) (.branch 6 (.leaf 4535138080) (.leaf 4402144962)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4274678281) (.leaf 4152435976)) (.branch 10 (.leaf 4035136031) (.leaf 3922514895))) (.branch 13 (.branch 12 (.leaf 3814326046) (.leaf 3710338690)) (.branch 14 (.leaf 3610336581) (.leaf 3514116941))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3421489480) (.branch 17 (.leaf 3332275496) (.leaf 3246307056))) (.branch 20 (.branch 19 (.leaf 3163426238) (.leaf 3083484444)) (.branch 21 (.leaf 3006341756) (.leaf 2931866358)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2859933989) (.leaf 2790427446)) (.branch 25 (.leaf 2723236124) (.leaf 2658255587))) (.branch 28 (.branch 27 (.leaf 2595387174) (.leaf 2534537631)) (.branch 29 (.leaf 2475618774) (.leaf 2418547169)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2363243843) (.branch 32 (.leaf 2309634004) (.leaf 2257646796))) (.branch 35 (.branch 34 (.leaf 2207215051) (.leaf 2158275079)) (.branch 36 (.leaf 2110766452) (.leaf 2064631819)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2019816722) (.leaf 1976269428)) (.branch 40 (.leaf 1933940772) (.leaf 1892784014))) (.branch 43 (.branch 42 (.leaf 1852754692) (.leaf 1813810502)) (.branch 44 (.leaf 1775911174) (.leaf 1739018353))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1703095503) (.branch 47 (.leaf 1668107797) (.leaf 1634022030))) (.branch 50 (.branch 49 (.leaf 1600806526) (.leaf 1568431060)) (.branch 51 (.leaf 1536866777) (.leaf 1506086117)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1476062751) (.leaf 1446771513)) (.branch 55 (.leaf 1418188338) (.leaf 1390290207))) (.branch 58 (.branch 57 (.leaf 1363055093) (.leaf 1336461906)) (.branch 59 (.leaf 1310490450) (.leaf 1285121374))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1260336130) (.branch 62 (.leaf 1236116935) (.leaf 1212446727))) (.branch 65 (.branch 64 (.leaf 1189309137) (.leaf 1166688448)) (.branch 66 (.leaf 1144569567) (.leaf 1122937993)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1101779789) (.leaf 1081081553)) (.branch 70 (.leaf 1060830395) (.leaf 1041013913))) (.branch 73 (.branch 72 (.leaf 1021620166) (.leaf 1002637658)) (.branch 74 (.leaf 984055310) (.leaf 965862449))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 948048784) (.branch 77 (.leaf 930604390) (.leaf 913519691))) (.branch 80 (.branch 79 (.leaf 896785444) (.leaf 880392728)) (.branch 81 (.leaf 864332923) (.leaf 848597702)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 833179018) (.leaf 818069087)) (.branch 85 (.leaf 803260383) (.leaf 788745624))) (.branch 88 (.branch 87 (.leaf 774517761) (.leaf 760569969)) (.branch 89 (.leaf 746895639) (.leaf 733488366)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 720341944) (.branch 92 (.leaf 707450356) (.leaf 694807768))) (.branch 95 (.branch 94 (.leaf 682408518) (.leaf 670247114)) (.branch 96 (.leaf 658318224) (.leaf 646616671)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 635137427) (.leaf 623875608)) (.branch 100 (.leaf 612826466) (.leaf 601985387))) (.branch 103 (.branch 102 (.leaf 591347884) (.leaf 580909593)) (.branch 104 (.leaf 570666270) (.leaf 560613782))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 550748110) (.leaf 541065337)) (.branch 108 (.leaf 531561652) (.leaf 522233342))) (.branch 111 (.branch 110 (.leaf 513076788) (.leaf 504088465)) (.branch 112 (.leaf 495264936) (.leaf 486602851)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 478098943) (.leaf 469750024)) (.branch 116 (.leaf 461552987) (.leaf 453504798))) (.branch 119 (.branch 118 (.leaf 445602496) (.leaf 437843192)) (.branch 120 (.leaf 430224065) (.leaf 422742360)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 373).prefactor = (2306717983856169/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 373).cutoff/(generalMeanRows 373).c)).2 =
    (88751184261133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 373).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 373).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 373).q*(generalMeanRows 373).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 373).q*(generalMeanRows 373).cutoff/2-2 = (16834/7751:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable156.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 373).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 373

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 373).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 373).criticalRate j.val*(generalMeanRows 373).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 373).c*(generalMeanRows 373).criticalPoint j.val)).2-
      (generalMeanRows 373).J/2-(generalMeanRows 373).error (generalMeanGrid j.val)+
      (generalMeanRows 373).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 373).c)).2-
      (generalMeanRows 373).J/2-(generalMeanRows 373).error 4 := by
  have he : (generalMeanRows 373).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 373) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 373)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0373

/-! Kernel-checked entropy margins for general spectral rectangle 374. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0374
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5304020407) (.branch 2 (.leaf 5137751888) (.leaf 4978901986))) (.branch 5 (.branch 4 (.leaf 4827037035) (.leaf 4681754478)) (.branch 6 (.leaf 4542680154) (.leaf 4409465864)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4281787202) (.leaf 4159341604)) (.branch 10 (.leaf 4041846586) (.leaf 3929038158))) (.branch 13 (.branch 12 (.leaf 3820669387) (.leaf 3716509097)) (.branch 14 (.leaf 3616340682) (.leaf 3519961026))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3427179522) (.branch 17 (.leaf 3337817173) (.leaf 3251705764))) (.branch 20 (.branch 19 (.leaf 3168687113) (.leaf 3088612373)) (.branch 21 (.leaf 3011341395) (.leaf 2936742142)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2864690147) (.leaf 2795068013)) (.branch 25 (.leaf 2727764949) (.leaf 2662676348))) (.branch 28 (.branch 27 (.leaf 2599703382) (.leaf 2538752645)) (.branch 29 (.leaf 2479735804) (.leaf 2422569287)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2367173990) (.branch 32 (.leaf 2313474997) (.leaf 2261401332))) (.branch 35 (.branch 34 (.leaf 2210885718) (.leaf 2161864357)) (.branch 36 (.leaf 2114276722) (.leaf 2068065366)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2023175739) (.leaf 1979556024)) (.branch 40 (.leaf 1937156975) (.leaf 1895931771))) (.branch 43 (.branch 42 (.leaf 1855835880) (.leaf 1816826925)) (.branch 44 (.leaf 1778864568) (.leaf 1741910394))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1705927803) (.branch 47 (.leaf 1670881911) (.leaf 1636739458))) (.branch 50 (.branch 49 (.leaf 1603468717) (.leaf 1571039409)) (.branch 51 (.leaf 1539422634) (.leaf 1508590785)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1478517489) (.leaf 1449177538)) (.branch 55 (.leaf 1420546828) (.leaf 1392602302))) (.branch 58 (.branch 57 (.leaf 1365321895) (.leaf 1338684483)) (.branch 59 (.leaf 1312669836) (.leaf 1287258570))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1262432108) (.branch 62 (.leaf 1238172635) (.leaf 1214463063))) (.branch 65 (.branch 64 (.leaf 1191286995) (.leaf 1168628687)) (.branch 66 (.leaf 1146473022) (.leaf 1124805474)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1103612082) (.leaf 1082879425)) (.branch 70 (.leaf 1062594589) (.leaf 1042745151))) (.branch 73 (.branch 72 (.leaf 1023319152) (.leaf 1004305075)) (.branch 74 (.leaf 985691824) (.leaf 967468708))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 949625418) (.branch 77 (.leaf 932152013) (.leaf 915038902))) (.branch 80 (.branch 79 (.leaf 898276826) (.leaf 881856848)) (.branch 81 (.leaf 865770335) (.leaf 850008946)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 834564620) (.leaf 819429561)) (.branch 85 (.leaf 804596230) (.leaf 790057333))) (.branch 88 (.branch 87 (.leaf 775805808) (.leaf 761834820)) (.branch 89 (.leaf 748137749) (.leaf 734708179)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 721539895) (.branch 92 (.leaf 708626868) (.leaf 695963254))) (.branch 95 (.branch 94 (.leaf 683543384) (.leaf 671361755)) (.branch 96 (.leaf 659413027) (.leaf 647692014)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 636193680) (.leaf 624913132)) (.branch 100 (.leaf 613845615) (.leaf 602986507))) (.branch 103 (.branch 102 (.leaf 592331314) (.leaf 581875664)) (.branch 104 (.leaf 571615305) (.leaf 561546100))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 551664021) (.leaf 541965145)) (.branch 108 (.leaf 532445656) (.leaf 523101832))) (.branch 111 (.branch 110 (.leaf 513930051) (.leaf 504926780)) (.branch 112 (.leaf 496088577) (.leaf 487412087)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 478894036) (.leaf 470531233)) (.branch 116 (.leaf 462320564) (.leaf 454258990))) (.branch 119 (.branch 118 (.leaf 446343547) (.leaf 438571339)) (.branch 120 (.leaf 430939541) (.leaf 423445394)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 374).prefactor = (4621108253272507/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 374).cutoff/(generalMeanRows 374).c)).2 =
    (88751184261133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 374).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 374).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 374).q*(generalMeanRows 374).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 374).q*(generalMeanRows 374).cutoff/2-2 = (16834/7751:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable156.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 374).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 374

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 374).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 374).criticalRate j.val*(generalMeanRows 374).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 374).c*(generalMeanRows 374).criticalPoint j.val)).2-
      (generalMeanRows 374).J/2-(generalMeanRows 374).error (generalMeanGrid j.val)+
      (generalMeanRows 374).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 374).c)).2-
      (generalMeanRows 374).J/2-(generalMeanRows 374).error 4 := by
  have he : (generalMeanRows 374).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 374) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 374)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0374

/-! Kernel-checked entropy margins for general spectral rectangle 375. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0375
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5294722650) (.branch 2 (.leaf 5128760285) (.leaf 4970209732))) (.branch 5 (.branch 4 (.leaf 4818637188) (.leaf 4673639991)) (.branch 6 (.leaf 4534843905) (.leaf 4401900688)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4274485913) (.leaf 4152297018)) (.branch 10 (.leaf 4035051541) (.leaf 3922485534))) (.branch 13 (.branch 12 (.leaf 3814352121) (.leaf 3710420197)) (.branch 14 (.leaf 3610473239) (.leaf 3514308227))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3421734658) (.branch 17 (.leaf 3332573647) (.leaf 3246657101))) (.branch 20 (.branch 19 (.leaf 3163826961) (.leaf 3083934511)) (.branch 21 (.leaf 3006839739) (.leaf 2932410745)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2860523202) (.leaf 2791059857)) (.branch 25 (.leaf 2723910062) (.leaf 2658969353))) (.branch 28 (.branch 27 (.leaf 2596139050) (.leaf 2535325889)) (.branch 29 (.leaf 2476441681) (.leaf 2419402999)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2364130877) (.branch 32 (.leaf 2310550542) (.leaf 2258591156))) (.branch 35 (.branch 34 (.leaf 2208185578) (.leaf 2159270143)) (.branch 36 (.leaf 2111784458) (.leaf 2065671203)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2020875957) (.leaf 1977347025)) (.branch 40 (.leaf 1935035283) (.leaf 1893894029))) (.branch 43 (.branch 42 (.leaf 1853878845) (.leaf 1814947469)) (.branch 44 (.leaf 1777059672) (.leaf 1740177145))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1704263393) (.branch 47 (.leaf 1669283634) (.leaf 1635204704))) (.branch 50 (.branch 49 (.leaf 1601994972) (.leaf 1569624254)) (.branch 51 (.leaf 1538063735) (.leaf 1507285899)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1477264456) (.leaf 1447974279)) (.branch 55 (.leaf 1419391343) (.leaf 1391492668))) (.branch 58 (.branch 57 (.leaf 1364256261) (.leaf 1337661071)) (.branch 59 (.leaf 1311686936) (.leaf 1286314540))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1261525367) (.branch 62 (.leaf 1237301667) (.leaf 1213626411))) (.branch 65 (.branch 64 (.leaf 1190483258) (.leaf 1167856522)) (.branch 66 (.leaf 1145731137) (.leaf 1124092630)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1102927091) (.leaf 1082221144)) (.branch 70 (.leaf 1061961923) (.leaf 1042137049))) (.branch 73 (.branch 72 (.leaf 1022734605) (.leaf 1003743115)) (.branch 74 (.leaf 985151523) (.leaf 966949176))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 949125802) (.branch 77 (.leaf 931671493) (.leaf 914576693))) (.branch 80 (.branch 79 (.leaf 897832176) (.leaf 881429035)) (.branch 81 (.leaf 865358668) (.leaf 849612762)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 834183283) (.leaf 819062463)) (.branch 85 (.leaf 804242786) (.leaf 789716984))) (.branch 88 (.branch 87 (.leaf 775478019) (.leaf 761519078)) (.branch 89 (.leaf 747833560) (.leaf 734415074)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 721257420) (.branch 92 (.leaf 708354592) (.leaf 695700763))) (.branch 95 (.branch 94 (.leaf 683290280) (.leaf 671117658)) (.branch 96 (.leaf 659177573) (.leaf 647464854)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 635974480) (.leaf 624701572)) (.branch 100 (.leaf 613641389) (.leaf 602789320))) (.branch 103 (.branch 102 (.leaf 592140886) (.leaf 581691726)) (.branch 104 (.leaf 571437599) (.leaf 561374378))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 551498047) (.leaf 541804693)) (.branch 108 (.leaf 532290508) (.leaf 522951781))) (.branch 111 (.branch 110 (.leaf 513784897) (.leaf 504786333)) (.branch 112 (.leaf 495952655) (.leaf 487280514)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 478766645) (.leaf 470407863)) (.branch 116 (.leaf 462201062) (.leaf 454143208))) (.branch 119 (.branch 118 (.leaf 446231344) (.leaf 438462580)) (.branch 120 (.leaf 430834096) (.leaf 423343139)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 375).prefactor = (462046279507837/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 375).cutoff/(generalMeanRows 375).c)).2 =
    (445240702573243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 375).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 375).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 375).q*(generalMeanRows 375).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 375).q*(generalMeanRows 375).cutoff/2-2 = (33714/15479:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable157.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 375).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 375

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 375).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 375).criticalRate j.val*(generalMeanRows 375).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 375).c*(generalMeanRows 375).criticalPoint j.val)).2-
      (generalMeanRows 375).J/2-(generalMeanRows 375).error (generalMeanGrid j.val)+
      (generalMeanRows 375).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 375).c)).2-
      (generalMeanRows 375).J/2-(generalMeanRows 375).error 4 := by
  have he : (generalMeanRows 375).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 375) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 375)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0375

/-! Kernel-checked entropy margins for general spectral rectangle 376. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0376
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5303493177) (.branch 2 (.leaf 5137255901) (.leaf 4978442714))) (.branch 5 (.branch 4 (.leaf 4826619095) (.leaf 4681381716)) (.branch 6 (.leaf 4542355719) (.leaf 4409192286)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4281566453) (.leaf 4159175156)) (.branch 10 (.leaf 4041735466) (.leaf 3928982997))) (.branch 13 (.branch 12 (.leaf 3820670465) (.leaf 3716566381)) (.branch 14 (.leaf 3616453865) (.leaf 3520129558))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3427402645) (.branch 17 (.leaf 3338093942) (.leaf 3252035077))) (.branch 20 (.branch 19 (.leaf 3169067732) (.leaf 3089042943)) (.branch 21 (.leaf 3011820466) (.leaf 2937268183)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2865261561) (.leaf 2795683152)) (.branch 25 (.leaf 2728422126) (.leaf 2663373845))) (.branch 28 (.branch 27 (.leaf 2600439466) (.leaf 2539525569)) (.branch 29 (.leaf 2480543822) (.leaf 2423410657)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2368046979) (.branch 32 (.leaf 2314377890) (.leaf 2262332435))) (.branch 35 (.branch 34 (.leaf 2211843362) (.leaf 2162846901)) (.branch 36 (.leaf 2115282557) (.leaf 2069092917)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2024223469) (.leaf 1980622433)) (.branch 40 (.leaf 1938240603) (.leaf 1897031199))) (.branch 43 (.branch 42 (.leaf 1856949732) (.leaf 1817953867)) (.branch 44 (.leaf 1780003310) (.leaf 1743059689))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1707086447) (.branch 47 (.leaf 1672048745) (.leaf 1637913365))) (.branch 50 (.branch 49 (.leaf 1604648622) (.leaf 1572224283)) (.branch 51 (.leaf 1540611485) (.leaf 1509782667)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1479711494) (.leaf 1450372799)) (.branch 55 (.leaf 1421742517) (.leaf 1393797628))) (.branch 58 (.branch 57 (.leaf 1366516105) (.leaf 1339876861)) (.branch 59 (.leaf 1313859701) (.leaf 1288445276))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1263615041) (.branch 62 (.leaf 1239351215) (.leaf 1215636741))) (.branch 65 (.branch 64 (.leaf 1192455253) (.leaf 1169791036)) (.branch 66 (.leaf 1147629001) (.leaf 1125954651)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1104754052) (.leaf 1084013806)) (.branch 70 (.leaf 1063721027) (.leaf 1043863313))) (.branch 73 (.branch 72 (.leaf 1024428730) (.leaf 1005405781)) (.branch 74 (.leaf 986783393) (.leaf 968550894))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 950697996) (.branch 77 (.leaf 933214775) (.leaf 916091658))) (.branch 80 (.branch 79 (.leaf 899319404) (.leaf 882889092)) (.branch 81 (.leaf 866792105) (.leaf 851020117)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 835565079) (.leaf 820419212)) (.branch 85 (.leaf 805574987) (.leaf 791025123))) (.branch 88 (.branch 87 (.leaf 776762572) (.leaf 762780508)) (.branch 89 (.leaf 749072321) (.leaf 735631607)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 722452158) (.branch 92 (.leaf 709527957) (.leaf 696853167))) (.branch 95 (.branch 94 (.leaf 684422127) (.leaf 672229342)) (.branch 96 (.leaf 660269478) (.leaf 648537358)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 637027950) (.leaf 625736369)) (.branch 100 (.leaf 614657865) (.leaf 603787820))) (.branch 103 (.branch 102 (.leaf 593121747) (.leaf 582655278)) (.branch 104 (.leaf 572384166) (.leaf 562304276))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 552411584) (.leaf 542702174)) (.branch 108 (.leaf 533172229) (.leaf 523818033))) (.branch 111 (.branch 110 (.leaf 514635964) (.leaf 505622494)) (.branch 112 (.leaf 496774183) (.leaf 488087677)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 479559706) (.leaf 471187078)) (.branch 116 (.leaf 462966682) (.leaf 454895481))) (.branch 119 (.branch 118 (.leaf 446970511) (.leaf 439188878)) (.branch 120 (.leaf 431547758) (.leaf 424044393)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 376).prefactor = (4628116433623489/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 376).cutoff/(generalMeanRows 376).c)).2 =
    (445240702573243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 376).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 376).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 376).q*(generalMeanRows 376).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 376).q*(generalMeanRows 376).cutoff/2-2 = (33714/15479:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable157.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 376).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 376

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 376).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 376).criticalRate j.val*(generalMeanRows 376).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 376).c*(generalMeanRows 376).criticalPoint j.val)).2-
      (generalMeanRows 376).J/2-(generalMeanRows 376).error (generalMeanGrid j.val)+
      (generalMeanRows 376).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 376).c)).2-
      (generalMeanRows 376).J/2-(generalMeanRows 376).error 4 := by
  have he : (generalMeanRows 376).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 376) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 376)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0376

/-! Kernel-checked entropy margins for general spectral rectangle 377. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0377
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5312841156) (.branch 2 (.leaf 5146296127) (.leaf 4987182053))) (.branch 5 (.branch 4 (.leaf 4835064545) (.leaf 4689540380)) (.branch 6 (.leaf 4550234770) (.leaf 4416798941)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4288907946) (.leaf 4166258717)) (.branch 10 (.leaf 4048568301) (.leaf 3935572269))) (.branch 13 (.branch 12 (.leaf 3827023277) (.leaf 3722689766)) (.branch 14 (.leaf 3622354767) (.leaf 3525814829))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3432879027) (.branch 17 (.leaf 3343368065) (.leaf 3257113451))) (.branch 20 (.branch 19 (.leaf 3173956737) (.leaf 3093748830)) (.branch 21 (.leaf 3016349348) (.leaf 2941626034)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2869454215) (.leaf 2799716297)) (.branch 25 (.leaf 2732301306) (.leaf 2667104460))) (.branch 28 (.branch 27 (.leaf 2604026769) (.leaf 2542974668)) (.branch 29 (.leaf 2483859681) (.leaf 2426598095)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2371110673) (.branch 32 (.leaf 2317322377) (.leaf 2265162111))) (.branch 35 (.branch 34 (.leaf 2214562488) (.leaf 2165459603)) (.branch 36 (.leaf 2117792829) (.leaf 2071504622)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2026540343) (.leaf 1982848087)) (.branch 40 (.leaf 1940378527) (.leaf 1899084764))) (.branch 43 (.branch 42 (.leaf 1858922192) (.leaf 1819848364)) (.branch 44 (.leaf 1781822875) (.leaf 1744807245))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1708764813) (.branch 47 (.leaf 1673660639) (.leaf 1639461406))) (.branch 50 (.branch 49 (.leaf 1606135334) (.leaf 1573652096)) (.branch 51 (.leaf 1541982741) (.leaf 1511099617)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1480976309) (.leaf 1451587565)) (.branch 55 (.leaf 1422909241) (.leaf 1394918243))) (.branch 58 (.branch 57 (.leaf 1367592467) (.leaf 1340910757)) (.branch 59 (.leaf 1314852846) (.leaf 1289399321))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1264531571) (.branch 62 (.leaf 1240231754) (.leaf 1216482753))) (.branch 65 (.branch 64 (.leaf 1193268141) (.leaf 1170572152)) (.branch 66 (.leaf 1148379642) (.leaf 1126676060)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1105447423) (.leaf 1084680286)) (.branch 70 (.leaf 1064361716) (.leaf 1044479268))) (.branch 73 (.branch 72 (.leaf 1025020963) (.leaf 1005975265)) (.branch 74 (.leaf 987331060) (.leaf 969077638))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 951204675) (.branch 77 (.leaf 933702211) (.leaf 916560640))) (.branch 80 (.branch 79 (.leaf 899770688) (.leaf 883323403)) (.branch 81 (.leaf 867210138) (.leaf 851422537)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 835952527) (.leaf 820792298)) (.branch 85 (.leaf 805934298) (.leaf 791371222))) (.branch 88 (.branch 87 (.leaf 777095997) (.leaf 763101775)) (.branch 89 (.leaf 749381925) (.leaf 735930022)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 722739838) (.branch 92 (.leaf 709805336) (.leaf 697120663))) (.branch 95 (.branch 94 (.leaf 684680138) (.leaf 672478250)) (.branch 96 (.leaf 660509651) (.leaf 648769146)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 637251690) (.leaf 625952382)) (.branch 100 (.leaf 614866459) (.leaf 603989292))) (.branch 103 (.branch 102 (.leaf 593316379) (.leaf 582843341)) (.branch 104 (.leaf 572565919) (.leaf 562479968))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 552581455) (.leaf 542866450)) (.branch 108 (.leaf 533331129) (.leaf 523971766))) (.branch 111 (.branch 110 (.leaf 514784732) (.leaf 505766488)) (.branch 112 (.leaf 496913588) (.leaf 488222668)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 479690452) (.leaf 471313741)) (.branch 116 (.leaf 463089417) (.leaf 455014437))) (.branch 119 (.branch 118 (.leaf 447085830) (.leaf 439300697)) (.branch 120 (.leaf 431656207) (.leaf 424149597)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 377).prefactor = (57859916225987/12500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 377).cutoff/(generalMeanRows 377).c)).2 =
    (88751184261133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 377).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 377).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 377).q*(generalMeanRows 377).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 377).q*(generalMeanRows 377).cutoff/2-2 = (16834/7751:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable156.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 377).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 377

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 377).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 377).criticalRate j.val*(generalMeanRows 377).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 377).c*(generalMeanRows 377).criticalPoint j.val)).2-
      (generalMeanRows 377).J/2-(generalMeanRows 377).error (generalMeanGrid j.val)+
      (generalMeanRows 377).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 377).c)).2-
      (generalMeanRows 377).J/2-(generalMeanRows 377).error 4 := by
  have he : (generalMeanRows 377).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 377) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 377)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0377

/-! Kernel-checked entropy margins for general spectral rectangle 378. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0378
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5321676574) (.branch 2 (.leaf 5154854575) (.leaf 4995475889))) (.branch 5 (.branch 4 (.leaf 4843105406) (.leaf 4697339229)) (.branch 6 (.leaf 4557801950) (.leaf 4424144213)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4296040531) (.leaf 4173187333)) (.branch 10 (.leaf 4055301194) (.leaf 3942117246))) (.branch 13 (.branch 12 (.leaf 3833387735) (.leaf 3728880713)) (.branch 14 (.leaf 3628378854) (.leaf 3531678367))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3438588010) (.branch 17 (.leaf 3348928189) (.leaf 3262530130))) (.branch 20 (.branch 19 (.leaf 3179235125) (.leaf 3098893829)) (.branch 21 (.leaf 3021365629) (.leaf 2946518048)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2874226205) (.leaf 2804372311)) (.branch 25 (.leaf 2736845207) (.leaf 2671539937))) (.branch 28 (.branch 27 (.leaf 2608357345) (.leaf 2547203713)) (.branch 29 (.leaf 2487990415) (.leaf 2430633602)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2375053903) (.branch 32 (.leaf 2321176155) (.leaf 2268929145))) (.branch 35 (.branch 34 (.leaf 2218245374) (.leaf 2169060829)) (.branch 36 (.leaf 2121314783) (.leaf 2074949597)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2029910541) (.leaf 1986145624)) (.branch 40 (.leaf 1943605436) (.leaf 1902243000))) (.branch 43 (.branch 42 (.leaf 1862013636) (.leaf 1822874828)) (.branch 44 (.leaf 1784786101) (.leaf 1747708913))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1711606541) (.branch 47 (.leaf 1676443988) (.leaf 1642187881))) (.branch 50 (.branch 49 (.leaf 1608806387) (.leaf 1576269128)) (.branch 51 (.leaf 1544547105) (.leaf 1513612622)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1483439218) (.leaf 1454001600)) (.branch 55 (.leaf 1425275583) (.leaf 1397238035))) (.branch 58 (.branch 57 (.leaf 1369866816) (.leaf 1343140732)) (.branch 59 (.leaf 1317039487) (.leaf 1291543631))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1266634526) (.branch 62 (.leaf 1242294298) (.leaf 1218505801))) (.branch 65 (.branch 64 (.leaf 1195252583) (.leaf 1172518850)) (.branch 66 (.leaf 1150289432) (.leaf 1128549757)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1107285816) (.leaf 1086484143)) (.branch 70 (.leaf 1066131782) (.leaf 1046216270))) (.branch 73 (.branch 72 (.leaf 1026725605) (.leaf 1007648233)) (.branch 74 (.leaf 988973022) (.leaf 970689244))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 952786557) (.branch 77 (.leaf 935254986) (.leaf 918084908))) (.branch 80 (.branch 79 (.leaf 901267034) (.leaf 884792397)) (.branch 81 (.leaf 868652335) (.leaf 852838479)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 837342741) (.leaf 822157300)) (.branch 85 (.leaf 807274592) (.leaf 792687297))) (.branch 88 (.branch 87 (.leaf 778388331) (.leaf 764370837)) (.branch 89 (.leaf 750628170) (.leaf 737153896)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 723941776) (.branch 92 (.leaf 710985764) (.leaf 698279996))) (.branch 95 (.branch 94 (.leaf 685818782) (.leaf 673596602)) (.branch 96 (.leaf 661608099) (.leaf 649848069)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 638311459) (.leaf 626993360)) (.branch 100 (.leaf 615889001) (.leaf 604993745))) (.branch 103 (.branch 102 (.leaf 594303082) (.leaf 583812627)) (.branch 104 (.leaf 573518114) (.leaf 563415390))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 553500415) (.leaf 543769253)) (.branch 108 (.leaf 534218075) (.leaf 524843148))) (.branch 111 (.branch 110 (.leaf 515640835) (.leaf 506607594)) (.branch 112 (.leaf 497739970) (.leaf 489034597)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 480488191) (.leaf 472097550)) (.branch 116 (.leaf 463859549) (.leaf 455771140))) (.branch 119 (.branch 118 (.leaf 447829347) (.leaf 440031267)) (.branch 120 (.leaf 432374064) (.leaf 424854970)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 378).prefactor = (4636491123350709/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 378).cutoff/(generalMeanRows 378).c)).2 =
    (88751184261133/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 378).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 378).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 378).q*(generalMeanRows 378).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 378).q*(generalMeanRows 378).cutoff/2-2 = (16834/7751:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable156.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 378).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 378

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 378).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 378).criticalRate j.val*(generalMeanRows 378).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 378).c*(generalMeanRows 378).criticalPoint j.val)).2-
      (generalMeanRows 378).J/2-(generalMeanRows 378).error (generalMeanGrid j.val)+
      (generalMeanRows 378).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 378).c)).2-
      (generalMeanRows 378).J/2-(generalMeanRows 378).error 4 := by
  have he : (generalMeanRows 378).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 378) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 378)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0378

/-! Kernel-checked entropy margins for general spectral rectangle 379. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0379
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5247694276) (.branch 2 (.leaf 5080508407) (.leaf 4920789761))) (.branch 5 (.branch 4 (.leaf 4768103523) (.leaf 4622045996)) (.branch 6 (.leaf 4482241879) (.leaf 4348341845)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4220020367) (.leaf 4096973764)) (.branch 10 (.leaf 3978918446) (.leaf 3865589327))) (.branch 13 (.branch 12 (.leaf 3756738387) (.leaf 3652133375)) (.branch 14 (.leaf 3551556619) (.leaf 3454803954))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3361683736) (.branch 17 (.leaf 3272015942) (.leaf 3185631351))) (.branch 20 (.branch 19 (.leaf 3102370786) (.leaf 3022084422)) (.branch 21 (.leaf 2944631150) (.leaf 2869877989)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2797699543) (.leaf 2727977507)) (.branch 25 (.leaf 2660600197) (.leaf 2595462131))) (.branch 28 (.branch 27 (.leaf 2532463628) (.leaf 2471510441)) (.branch 29 (.leaf 2412513418) (.leaf 2355388188)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2300054860) (.branch 32 (.leaf 2246437757) (.leaf 2194465155))) (.branch 35 (.branch 34 (.leaf 2144069048) (.leaf 2095184928)) (.branch 36 (.leaf 2047751577) (.leaf 2001710871)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1957007603) (.leaf 1913589317)) (.branch 40 (.leaf 1871406142) (.leaf 1830410653))) (.branch 43 (.branch 42 (.leaf 1790557726) (.leaf 1751804413)) (.branch 44 (.leaf 1714109818) (.leaf 1677434983))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1641742784) (.branch 47 (.leaf 1606997826) (.leaf 1573166352))) (.branch 50 (.branch 49 (.leaf 1540216154) (.leaf 1508116488)) (.branch 51 (.leaf 1476837999) (.leaf 1446352642)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1416633619) (.leaf 1387655308)) (.branch 55 (.leaf 1359393207) (.leaf 1331823870))) (.branch 58 (.branch 57 (.leaf 1304924858) (.leaf 1278674685)) (.branch 59 (.leaf 1253052767) (.leaf 1228039383))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1203615626) (.branch 62 (.leaf 1179763362) (.leaf 1156465197))) (.branch 65 (.branch 64 (.leaf 1133704435) (.leaf 1111465046)) (.branch 66 (.leaf 1089731634) (.leaf 1068489406)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1047724142) (.leaf 1027422169)) (.branch 70 (.leaf 1007570334) (.leaf 988155980))) (.branch 73 (.branch 72 (.leaf 969166923) (.leaf 950591429)) (.branch 74 (.leaf 932418194) (.leaf 914636324))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 897235317) (.branch 77 (.leaf 880205045) (.leaf 863535735))) (.branch 80 (.branch 79 (.leaf 847217957) (.leaf 831242606)) (.branch 81 (.leaf 815600887) (.leaf 800284307)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 785284653) (.leaf 770593989)) (.branch 85 (.leaf 756204638) (.leaf 742109172))) (.branch 88 (.branch 87 (.leaf 728300406) (.leaf 714771381)) (.branch 89 (.leaf 701515360) (.leaf 688525817)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 675796427) (.branch 92 (.leaf 663321062) (.leaf 651093777))) (.branch 95 (.branch 94 (.leaf 639108809) (.leaf 627360566)) (.branch 96 (.leaf 615843621) (.leaf 604552705)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 593482705) (.leaf 582628653)) (.branch 100 (.leaf 571985721) (.leaf 561549219))) (.branch 103 (.branch 102 (.leaf 551314589) (.leaf 541277397)) (.branch 104 (.leaf 531433333) (.leaf 521778202))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 512307924) (.leaf 503018528)) (.branch 108 (.leaf 493906148) (.leaf 484967018))) (.branch 111 (.branch 110 (.leaf 476197474) (.leaf 467593942)) (.branch 112 (.leaf 459152943) (.leaf 450871086)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 442745065) (.leaf 434771657)) (.branch 116 (.leaf 426947718) (.leaf 419270184))) (.branch 119 (.branch 118 (.leaf 411736064) (.leaf 404342440)) (.branch 120 (.leaf 397086465) (.leaf 389965359)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 379).prefactor = (115947251363031/25000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 379).cutoff/(generalMeanRows 379).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 379).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 379).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 379).q*(generalMeanRows 379).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 379).q*(generalMeanRows 379).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable148.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 379).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 379

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 379).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 379).criticalRate j.val*(generalMeanRows 379).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 379).c*(generalMeanRows 379).criticalPoint j.val)).2-
      (generalMeanRows 379).J/2-(generalMeanRows 379).error (generalMeanGrid j.val)+
      (generalMeanRows 379).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 379).c)).2-
      (generalMeanRows 379).J/2-(generalMeanRows 379).error 4 := by
  have he : (generalMeanRows 379).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 379) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 379)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0379

/-! Kernel-checked entropy margins for general spectral rectangle 380. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0380
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5265302337) (.branch 2 (.leaf 5097555494) (.leaf 4937300929))) (.branch 5 (.branch 4 (.leaf 4784102370) (.leaf 4637554763)) (.branch 6 (.leaf 4497281548) (.leaf 4362932228)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4234180181) (.leaf 4110720709)) (.branch 10 (.leaf 3992269269) (.leaf 3878559886))) (.branch 13 (.branch 12 (.leaf 3769343709) (.leaf 3664387706)) (.branch 14 (.leaf 3563473476) (.leaf 3466396169))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3372963496) (.branch 17 (.leaf 3282994832) (.leaf 3196320387))) (.branch 20 (.branch 19 (.leaf 3112780450) (.leaf 3032224694)) (.branch 21 (.leaf 2954511536) (.leaf 2879507548)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2807086916) (.leaf 2737130935)) (.branch 25 (.leaf 2669527548) (.leaf 2604170919))) (.branch 28 (.branch 27 (.leaf 2540961031) (.leaf 2479803322)) (.branch 29 (.leaf 2420608342) (.leaf 2363291434)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2307772441) (.branch 32 (.leaf 2253975432) (.leaf 2201828441))) (.branch 35 (.branch 34 (.leaf 2151263236) (.leaf 2102215091)) (.branch 36 (.leaf 2054622582) (.leaf 2008427391)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1963574127) (.leaf 1920010155)) (.branch 40 (.leaf 1877685440) (.leaf 1836552395))) (.branch 43 (.branch 42 (.leaf 1796565746) (.leaf 1757682400)) (.branch 44 (.leaf 1719861325) (.leaf 1683063432))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1647251471) (.branch 47 (.leaf 1612389930) (.leaf 1578444938))) (.branch 50 (.branch 49 (.leaf 1545384179) (.leaf 1513176807)) (.branch 51 (.leaf 1481793366) (.leaf 1451205719)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1421386977) (.leaf 1392311433)) (.branch 55 (.leaf 1363954501) (.leaf 1336292659))) (.branch 58 (.branch 57 (.leaf 1309303390) (.leaf 1282965137)) (.branch 59 (.leaf 1257257248) (.leaf 1232159934))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1207654226) (.branch 62 (.leaf 1183721928) (.leaf 1160345589))) (.branch 65 (.branch 64 (.leaf 1137508455) (.leaf 1115194444)) (.branch 66 (.leaf 1093388108) (.leaf 1072074604)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1051239665) (.leaf 1030869571)) (.branch 70 (.leaf 1010951126) (.leaf 991471629))) (.branch 73 (.branch 72 (.leaf 972418856) (.leaf 953781034)) (.branch 74 (.leaf 935546820) (.leaf 917705286))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 900245892) (.branch 77 (.leaf 883158476) (.leaf 866433234))) (.branch 80 (.branch 79 (.leaf 850060704) (.leaf 834031749)) (.branch 81 (.leaf 818337546) (.leaf 802969573)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 787919590) (.leaf 773179633)) (.branch 85 (.leaf 758741999) (.leaf 744599238))) (.branch 88 (.branch 87 (.leaf 730744138) (.leaf 717169718)) (.branch 89 (.leaf 703869218) (.leaf 690836090)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 678063988) (.branch 92 (.leaf 665546763) (.leaf 653278451))) (.branch 95 (.branch 94 (.leaf 641253269) (.leaf 629465605)) (.branch 96 (.leaf 617910016) (.leaf 606581215)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 595474071) (.leaf 584583599)) (.branch 100 (.leaf 573904956) (.leaf 563433436))) (.branch 103 (.branch 102 (.leaf 553164464) (.leaf 543093594)) (.branch 104 (.leaf 533216499) (.leaf 523528971))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 514026917) (.leaf 504706352)) (.branch 108 (.leaf 495563396) (.leaf 486594272))) (.branch 111 (.branch 110 (.leaf 477795302) (.leaf 469162902)) (.branch 112 (.leaf 460693580) (.leaf 452383934)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 444230647) (.leaf 436230485)) (.branch 116 (.leaf 428380294) (.leaf 420676999))) (.branch 119 (.branch 118 (.leaf 413117599) (.leaf 405699167)) (.branch 120 (.leaf 398418845) (.leaf 391273845)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 380).prefactor = (4653451984262199/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 380).cutoff/(generalMeanRows 380).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 380).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 380).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 380).q*(generalMeanRows 380).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 380).q*(generalMeanRows 380).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable148.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 380).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 380

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 380).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 380).criticalRate j.val*(generalMeanRows 380).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 380).c*(generalMeanRows 380).criticalPoint j.val)).2-
      (generalMeanRows 380).J/2-(generalMeanRows 380).error (generalMeanGrid j.val)+
      (generalMeanRows 380).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 380).c)).2-
      (generalMeanRows 380).J/2-(generalMeanRows 380).error 4 := by
  have he : (generalMeanRows 380).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 380) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 380)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0380

/-! Kernel-checked entropy margins for general spectral rectangle 381. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0381
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5312278232) (.branch 2 (.leaf 5145765589) (.leaf 4986689335))) (.branch 5 (.branch 4 (.leaf 4834614225) (.leaf 4689136264)) (.branch 6 (.leaf 4549879976) (.leaf 4416495962)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4288658721) (.leaf 4166064687)) (.branch 10 (.leaf 4048430462) (.leaf 3935491223))) (.branch 13 (.branch 12 (.leaf 3826999275) (.leaf 3722722746)) (.branch 14 (.leaf 3622444397) (.leaf 3525960532))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3433080020) (.branch 17 (.leaf 3343623380) (.leaf 3257421962))) (.branch 20 (.branch 19 (.leaf 3174317184) (.leaf 3094159837)) (.branch 21 (.leaf 3016809444) (.leaf 2942133667)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2870007769) (.leaf 2800314105)) (.branch 25 (.leaf 2732941664) (.leaf 2667785633))) (.branch 28 (.branch 27 (.leaf 2604747005) (.leaf 2543732206)) (.branch 29 (.leaf 2484652758) (.leaf 2427424954)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2371969568) (.branch 32 (.leaf 2318211578) (.leaf 2266079911))) (.branch 35 (.branch 34 (.leaf 2215507205) (.leaf 2166429582)) (.branch 36 (.leaf 2118786450) (.leaf 2072520298)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2027576526) (.leaf 1983903266)) (.branch 40 (.leaf 1941451232) (.leaf 1900173567))) (.branch 43 (.branch 42 (.leaf 1860025705) (.leaf 1820965246)) (.branch 44 (.leaf 1782951825) (.leaf 1745947008))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1709914178) (.branch 47 (.leaf 1674818437) (.leaf 1640626512))) (.branch 50 (.branch 49 (.leaf 1607306667) (.leaf 1574828618)) (.branch 51 (.leaf 1543163455) (.leaf 1512283570)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1482162586) (.leaf 1452775292)) (.branch 55 (.leaf 1424097584) (.leaf 1396106406))) (.branch 58 (.branch 57 (.leaf 1368779692) (.leaf 1342096321)) (.branch 59 (.leaf 1316036064) (.leaf 1290579541))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1265708176) (.branch 62 (.leaf 1241404158) (.leaf 1217650402))) (.branch 65 (.branch 64 (.leaf 1194430514) (.leaf 1171728755)) (.branch 66 (.leaf 1149530010) (.leaf 1127819757)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1106584040) (.leaf 1085809438)) (.branch 70 (.leaf 1065483044) (.leaf 1045592437))) (.branch 73 (.branch 72 (.leaf 1026125661) (.leaf 1007071201)) (.branch 74 (.leaf 988417966) (.leaf 970155266))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 952272795) (.branch 77 (.leaf 934760613) (.leaf 917609132))) (.branch 80 (.branch 79 (.leaf 900809096) (.leaf 884351568)) (.branch 81 (.leaf 868227917) (.leaf 852429803)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 836949164) (.leaf 821778208)) (.branch 85 (.leaf 806909394) (.leaf 792335430))) (.branch 88 (.branch 87 (.leaf 778049253) (.leaf 764044028)) (.branch 89 (.leaf 750313134) (.leaf 736850156)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 723648876) (.branch 92 (.leaf 710703266) (.leaf 698007481))) (.branch 95 (.branch 94 (.leaf 685555849) (.leaf 673342867)) (.branch 96 (.leaf 661363192) (.leaf 649611638)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 638083165) (.leaf 626772880)) (.branch 100 (.leaf 615676024) (.leaf 604787974))) (.branch 103 (.branch 102 (.leaf 594104233) (.leaf 583620427)) (.branch 104 (.leaf 573332300) (.leaf 563235713))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 553326635) (.leaf 543601141)) (.branch 108 (.leaf 534055410) (.leaf 524685719))) (.branch 111 (.branch 110 (.leaf 515488441) (.leaf 506460041)) (.branch 112 (.leaf 497597073) (.leaf 488896178)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 480354080) (.leaf 471967583)) (.branch 116 (.leaf 463733570) (.leaf 455649000))) (.branch 119 (.branch 118 (.leaf 447710902) (.leaf 439916380)) (.branch 120 (.leaf 432262602) (.leaf 424746808)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 381).prefactor = (4635782750159009/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 381).cutoff/(generalMeanRows 381).c)).2 =
    (445240702573243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 381).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 381).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 381).q*(generalMeanRows 381).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 381).q*(generalMeanRows 381).cutoff/2-2 = (33714/15479:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable157.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 381).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 381

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 381).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 381).criticalRate j.val*(generalMeanRows 381).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 381).c*(generalMeanRows 381).criticalPoint j.val)).2-
      (generalMeanRows 381).J/2-(generalMeanRows 381).error (generalMeanGrid j.val)+
      (generalMeanRows 381).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 381).c)).2-
      (generalMeanRows 381).J/2-(generalMeanRows 381).error 4 := by
  have he : (generalMeanRows 381).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 381) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 381)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0381

/-! Kernel-checked entropy margins for general spectral rectangle 382. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0382
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5321077839) (.branch 2 (.leaf 5154289374) (.leaf 4994949615))) (.branch 5 (.branch 4 (.leaf 4842622598) (.leaf 4696903658)) (.branch 6 (.leaf 4557416696) (.leaf 4423811736)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4295762738) (.leaf 4172965631)) (.branch 10 (.leaf 4055136549) (.leaf 3942010229))) (.branch 13 (.branch 12 (.leaf 3833338568) (.leaf 3728889309)) (.branch 14 (.leaf 3628444852) (.leaf 3531801165))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3438766799) (.branch 17 (.leaf 3349161978) (.leaf 3262817770))) (.branch 20 (.branch 19 (.leaf 3179575332) (.leaf 3099285207)) (.branch 21 (.leaf 3021806685) (.leaf 2947007211)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2874761839) (.leaf 2804952730)) (.branch 25 (.leaf 2737468688) (.leaf 2672204728))) (.branch 28 (.branch 27 (.leaf 2609061679) (.leaf 2547945812)) (.branch 29 (.leaf 2488768500) (.leaf 2431445900)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2375898654) (.branch 32 (.leaf 2322051616) (.leaf 2269833595))) (.branch 35 (.branch 34 (.leaf 2219177117) (.leaf 2170018199)) (.branch 36 (.leaf 2122296147) (.leaf 2075953357)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2030935137) (.leaf 1987189534)) (.branch 40 (.leaf 1944667179) (.leaf 1903321139))) (.branch 43 (.branch 42 (.leaf 1863106774) (.leaf 1823981612)) (.branch 44 (.leaf 1785905224) (.leaf 1748839109))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1712746592) (.branch 47 (.leaf 1677592716) (.leaf 1643344154))) (.branch 50 (.branch 49 (.leaf 1609969116) (.leaf 1577437268)) (.branch 51 (.leaf 1545719653) (.leaf 1514788616)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1484617737) (.leaf 1455181765)) (.branch 55 (.leaf 1426456553) (.leaf 1398419008))) (.branch 58 (.branch 57 (.leaf 1371047029) (.leaf 1344319458)) (.branch 59 (.leaf 1318216033) (.leaf 1292717342))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1267804778) (.branch 62 (.leaf 1243460501) (.leaf 1219667398))) (.branch 65 (.branch 64 (.leaf 1196409047) (.leaf 1173669683)) (.branch 66 (.leaf 1151434167) (.leaf 1129687952)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1108417058) (.leaf 1087608044)) (.branch 70 (.leaf 1067247980) (.leaf 1047324425))) (.branch 73 (.branch 72 (.leaf 1027825403) (.leaf 1008739380)) (.branch 74 (.leaf 990055246) (.leaf 971762295))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 953850202) (.branch 77 (.leaf 936309012) (.leaf 919129121))) (.branch 80 (.branch 79 (.leaf 902301256) (.leaf 885816466)) (.branch 81 (.leaf 869666107) (.leaf 853841823)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 838335542) (.leaf 823139455)) (.branch 85 (.leaf 808246012) (.leaf 793647906))) (.branch 88 (.branch 87 (.leaf 779338065) (.leaf 765309641)) (.branch 89 (.leaf 751556002) (.leaf 738070723)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 724847575) (.branch 92 (.leaf 711880522) (.leaf 699163706))) (.branch 95 (.branch 94 (.leaf 686691449) (.leaf 674458236)) (.branch 96 (.leaf 662458717) (.leaf 650687697)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 639140128) (.leaf 627811108)) (.branch 100 (.leaf 616695871) (.leaf 605789785))) (.branch 103 (.branch 102 (.leaf 595088346) (.leaf 584587174)) (.branch 104 (.leaf 574282006) (.leaf 564168694))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 554243202) (.leaf 544501598)) (.branch 108 (.leaf 534940055) (.leaf 525554843))) (.branch 111 (.branch 110 (.leaf 516342330) (.leaf 507298974)) (.branch 112 (.leaf 498421325) (.leaf 489706018)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 481149770) (.leaf 472749381)) (.branch 116 (.leaf 464501729) (.leaf 456403767))) (.branch 119 (.branch 118 (.leaf 448452520) (.leaf 440645086)) (.branch 120 (.leaf 432978631) (.leaf 425450386)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 382).prefactor = (1160865441421399/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 382).cutoff/(generalMeanRows 382).c)).2 =
    (445240702573243/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 382).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 382).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 382).q*(generalMeanRows 382).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 382).q*(generalMeanRows 382).cutoff/2-2 = (33714/15479:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable157.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 382).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 382

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 382).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 382).criticalRate j.val*(generalMeanRows 382).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 382).c*(generalMeanRows 382).criticalPoint j.val)).2-
      (generalMeanRows 382).J/2-(generalMeanRows 382).error (generalMeanGrid j.val)+
      (generalMeanRows 382).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 382).c)).2-
      (generalMeanRows 382).J/2-(generalMeanRows 382).error 4 := by
  have he : (generalMeanRows 382).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 382) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 382)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0382

/-! Kernel-checked entropy margins for general spectral rectangle 383. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0383
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5237641978) (.branch 2 (.leaf 5070793689) (.leaf 4911411407))) (.branch 5 (.branch 4 (.leaf 4759059321) (.leaf 4613332855)) (.branch 6 (.leaf 4473855940) (.leaf 4340278579)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4212274663) (.leaf 4089540011)) (.branch 10 (.leaf 3971790606) (.leaf 3858761003))) (.branch 13 (.branch 12 (.leaf 3750202884) (.leaf 3645883750)) (.branch 14 (.leaf 3545585737) (.leaf 3449104527))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3356248365) (.branch 17 (.leaf 3266837152) (.leaf 3180701625))) (.branch 20 (.branch 19 (.leaf 3097682591) (.leaf 3017630237)) (.branch 21 (.leaf 2940403487) (.leaf 2865869413)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2793902693) (.leaf 2724385106)) (.branch 25 (.leaf 2657205071) (.leaf 2592257216))) (.branch 28 (.branch 27 (.leaf 2529441984) (.leaf 2468665260)) (.branch 29 (.leaf 2409838030) (.leaf 2352876066)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2297699629) (.branch 32 (.leaf 2244233194) (.leaf 2192405194))) (.branch 35 (.branch 34 (.leaf 2142147782) (.leaf 2093396612)) (.branch 36 (.leaf 2046090624) (.leaf 2000171858)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1955585269) (.leaf 1912278560)) (.branch 40 (.leaf 1870202020) (.leaf 1829308382))) (.branch 43 (.branch 42 (.leaf 1789552679) (.leaf 1750892116)) (.branch 44 (.leaf 1713285950) (.leaf 1676695372))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1641083403) (.branch 47 (.leaf 1606414793) (.leaf 1572655926))) (.branch 50 (.branch 49 (.leaf 1539774731) (.leaf 1507740598)) (.branch 51 (.leaf 1476524302) (.leaf 1446097927)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1416434800) (.leaf 1387509418)) (.branch 55 (.leaf 1359297397) (.leaf 1331775407))) (.branch 58 (.branch 57 (.leaf 1304921117) (.leaf 1278713149)) (.branch 59 (.leaf 1253131026) (.leaf 1228155124))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1203766635) (.branch 62 (.leaf 1179947520) (.leaf 1156680475))) (.branch 65 (.branch 64 (.leaf 1133948892) (.leaf 1111736828)) (.branch 66 (.leaf 1090028969) (.leaf 1068810599)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1048067575) (.leaf 1027786299)) (.branch 70 (.leaf 1007953687) (.leaf 988557152))) (.branch 73 (.branch 72 (.leaf 969584575) (.leaf 951024285)) (.branch 74 (.leaf 932865039) (.leaf 915096001))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 897706726) (.branch 77 (.leaf 880687139) (.leaf 864027519))) (.branch 80 (.branch 79 (.leaf 847718486) (.leaf 831750982)) (.branch 81 (.leaf 816116259) (.leaf 800805866)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 785811635) (.leaf 771125667)) (.branch 85 (.leaf 756740325) (.leaf 742648218))) (.branch 88 (.branch 87 (.leaf 728842196) (.leaf 715315334)) (.branch 89 (.leaf 702060928) (.leaf 689072482)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 676343701) (.branch 92 (.leaf 663868484) (.leaf 651640915))) (.branch 95 (.branch 94 (.leaf 639655256) (.leaf 627905939)) (.branch 96 (.leaf 616387561) (.leaf 605094876)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 594022792) (.leaf 583166359)) (.branch 100 (.leaf 572520772) (.leaf 562081359))) (.branch 103 (.branch 102 (.leaf 551843578) (.leaf 541803012)) (.branch 104 (.leaf 531955368) (.leaf 522296466))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 512822239) (.leaf 503528732)) (.branch 108 (.leaf 494412089) (.leaf 485468560))) (.branch 111 (.branch 110 (.leaf 476694490) (.leaf 468086317)) (.branch 112 (.leaf 459640574) (.leaf 451353878)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 443222933) (.leaf 435244526)) (.branch 116 (.leaf 427415521) (.leaf 419732862))) (.branch 119 (.branch 118 (.leaf 412193566) (.leaf 404794721)) (.branch 120 (.leaf 397533488) (.leaf 390407093)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 383).prefactor = (4644201750342073/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 383).cutoff/(generalMeanRows 383).c)).2 =
    (217877939319293/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 383).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 383).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 383).q*(generalMeanRows 383).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 383).q*(generalMeanRows 383).cutoff/2-2 = (16834/7751:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable156.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 383).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 383

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 383).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 383).criticalRate j.val*(generalMeanRows 383).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 383).c*(generalMeanRows 383).criticalPoint j.val)).2-
      (generalMeanRows 383).J/2-(generalMeanRows 383).error (generalMeanGrid j.val)+
      (generalMeanRows 383).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 383).c)).2-
      (generalMeanRows 383).J/2-(generalMeanRows 383).error 4 := by
  have he : (generalMeanRows 383).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 383) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 383)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0383

/-! Kernel-checked entropy margins for general spectral rectangle 384. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0384
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5246352338) (.branch 2 (.leaf 5079226574) (.leaf 4919579235))) (.branch 5 (.branch 4 (.leaf 4766973782) (.leaf 4621004969)) (.branch 6 (.leaf 4481296100) (.leaf 4347496596)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4219279805) (.leaf 4096341041)) (.branch 10 (.leaf 3978395816) (.leaf 3865178241))) (.branch 13 (.branch 12 (.leaf 3756439586) (.leaf 3651946967)) (.branch 14 (.leaf 3551482155) (.leaf 3454840494))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3361829909) (.branch 17 (.leaf 3272270003) (.leaf 3185991229))) (.branch 20 (.branch 19 (.leaf 3102834132) (.leaf 3022648649)) (.branch 21 (.leaf 2945293468) (.leaf 2870635442)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2798549039) (.leaf 2728915842)) (.branch 25 (.leaf 2661624084) (.leaf 2596568220))) (.branch 28 (.branch 27 (.leaf 2533648524) (.leaf 2472770726)) (.branch 29 (.leaf 2413845665) (.leaf 2356788971)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2301520774) (.branch 32 (.leaf 2247965422) (.leaf 2196051231))) (.branch 35 (.branch 34 (.leaf 2145710240) (.leaf 2096877994)) (.branch 36 (.leaf 2049493335) (.leaf 2003498205)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1958837467) (.leaf 1915458738)) (.branch 40 (.leaf 1873312224) (.leaf 1832350578))) (.branch 43 (.branch 42 (.leaf 1792528760) (.leaf 1753803904)) (.branch 44 (.leaf 1716135197) (.leaf 1679483767))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1643812575) (.branch 47 (.leaf 1609086310) (.leaf 1575271301))) (.branch 50 (.branch 49 (.leaf 1542335423) (.leaf 1510248016)) (.branch 51 (.leaf 1478979807) (.leaf 1448502833)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1418790374) (.leaf 1389816889)) (.branch 55 (.leaf 1361557951) (.leaf 1333990190))) (.branch 58 (.branch 57 (.leaf 1307091241) (.leaf 1280839688)) (.branch 59 (.leaf 1255215021) (.leaf 1230197584))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1205768535) (.branch 62 (.leaf 1181909809) (.leaf 1158604070))) (.branch 65 (.branch 64 (.leaf 1135834684) (.leaf 1113585681)) (.branch 66 (.leaf 1091841720) (.leaf 1070588063)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1049810544) (.leaf 1029495539)) (.branch 70 (.leaf 1009629945) (.leaf 990201153))) (.branch 73 (.branch 72 (.leaf 971197024) (.leaf 952605867)) (.branch 74 (.leaf 934416422) (.leaf 916617834))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 899199640) (.branch 77 (.leaf 882151748) (.leaf 865464423))) (.branch 80 (.branch 79 (.leaf 849128268) (.leaf 833134209)) (.branch 81 (.leaf 817473486) (.leaf 802137631)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 787118464) (.leaf 772408073)) (.branch 85 (.leaf 757998807) (.leaf 743883265))) (.branch 88 (.branch 87 (.leaf 730054283) (.leaf 716504926)) (.branch 89 (.leaf 703228477) (.leaf 690218430)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 677468481) (.branch 92 (.leaf 664972518) (.leaf 652724614))) (.branch 95 (.branch 94 (.leaf 640719022) (.leaf 628950166)) (.branch 96 (.leaf 617412632) (.leaf 606101168)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 595010670) (.leaf 584136183)) (.branch 100 (.leaf 573472892) (.leaf 563016118))) (.branch 103 (.branch 102 (.leaf 552761311) (.leaf 542704047)) (.branch 104 (.leaf 532840026) (.leaf 523165061))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 513675079) (.leaf 504366115)) (.branch 108 (.leaf 495234312) (.leaf 486275909))) (.branch 111 (.branch 110 (.leaf 477487247) (.leaf 468864759)) (.branch 112 (.leaf 460404970) (.leaf 452104493)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 443960027) (.leaf 435968351)) (.branch 116 (.leaf 428126327) (.leaf 420430891))) (.branch 119 (.branch 118 (.leaf 412879056) (.leaf 405467907)) (.branch 120 (.leaf 398194598) (.leaf 391056352)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 384).prefactor = (1162981300085671/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 384).cutoff/(generalMeanRows 384).c)).2 =
    (217877939319293/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 384).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 384).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 384).q*(generalMeanRows 384).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 384).q*(generalMeanRows 384).cutoff/2-2 = (16834/7751:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable156.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 384).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 384

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 384).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 384).criticalRate j.val*(generalMeanRows 384).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 384).c*(generalMeanRows 384).criticalPoint j.val)).2-
      (generalMeanRows 384).J/2-(generalMeanRows 384).error (generalMeanGrid j.val)+
      (generalMeanRows 384).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 384).c)).2-
      (generalMeanRows 384).J/2-(generalMeanRows 384).error 4 := by
  have he : (generalMeanRows 384).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 384) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 384)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0384

/-! Kernel-checked entropy margins for general spectral rectangle 385. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0385
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5263816537) (.branch 2 (.leaf 5096134441) (.leaf 4935955663))) (.branch 5 (.branch 4 (.leaf 4782842214) (.leaf 4636387495)) (.branch 6 (.leaf 4496213559) (.leaf 4361968660)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4233325058) (.leaf 4109977052)) (.branch 10 (.leaf 3991639207) (.leaf 3878044751))) (.branch 13 (.branch 12 (.leaf 3768944124) (.leaf 3664103667)) (.branch 14 (.leaf 3563304425) (.leaf 3466341060))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3373020859) (.branch 17 (.leaf 3283162824) (.leaf 3196596843))) (.branch 20 (.branch 19 (.leaf 3113162930) (.leaf 3032710523)) (.branch 21 (.leaf 2955097841) (.leaf 2880191291)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2807864924) (.leaf 2737999930)) (.branch 25 (.leaf 2670484170) (.leaf 2605211746))) (.branch 28 (.branch 27 (.leaf 2542082602) (.leaf 2481002152)) (.branch 29 (.leaf 2421880939) (.leaf 2364634314)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2309182139) (.branch 32 (.leaf 2255448510) (.leaf 2203361505))) (.branch 35 (.branch 34 (.leaf 2152852938) (.leaf 2103858139)) (.branch 36 (.leaf 2056315744) (.leaf 2010167504)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1965358099) (.leaf 1921834968)) (.branch 40 (.leaf 1879548156) (.leaf 1838450156))) (.branch 43 (.branch 42 (.leaf 1798495778) (.leaf 1759642013)) (.branch 44 (.leaf 1721847914) (.leaf 1685074478))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1649284543) (.branch 47 (.leaf 1614442680) (.leaf 1580515107))) (.branch 50 (.branch 49 (.leaf 1547469591) (.leaf 1515275371)) (.branch 51 (.leaf 1483903075) (.leaf 1453324648)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1423513282) (.leaf 1394443349)) (.branch 55 (.leaf 1366090342) (.leaf 1338430813))) (.branch 58 (.branch 57 (.leaf 1311442322) (.leaf 1285103382)) (.branch 59 (.leaf 1259393415) (.leaf 1234292699))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1209782330) (.branch 62 (.leaf 1185844182) (.leaf 1162460862))) (.branch 65 (.branch 64 (.leaf 1139615681) (.leaf 1117292615)) (.branch 66 (.leaf 1095476272) (.leaf 1074151866)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1053305181) (.leaf 1032922552)) (.branch 70 (.leaf 1012990829) (.leaf 993497362))) (.branch 73 (.branch 72 (.leaf 974429971) (.leaf 955776927)) (.branch 74 (.leaf 937526932) (.leaf 919669096))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 902192920) (.branch 77 (.leaf 885088279) (.leaf 868345405))) (.branch 80 (.branch 79 (.leaf 851954869) (.leaf 835907569)) (.branch 81 (.leaf 820194714) (.leaf 804807809)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 789738645) (.leaf 774979286)) (.branch 85 (.leaf 760522054) (.leaf 746359524))) (.branch 88 (.branch 87 (.leaf 732484507) (.leaf 718890047)) (.branch 89 (.leaf 705569403) (.leaf 692516048)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 679723656) (.branch 92 (.leaf 667186096) (.leaf 654897421))) (.branch 95 (.branch 94 (.leaf 642851865) (.leaf 631043832)) (.branch 96 (.leaf 619467892) (.leaf 608118774)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 596991357) (.leaf 586080671)) (.branch 100 (.leaf 575381884) (.leaf 564890301))) (.branch 103 (.branch 102 (.leaf 554601357) (.leaf 544510615)) (.branch 104 (.leaf 534613758) (.leaf 524906587))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 515385014) (.leaf 506045063)) (.branch 108 (.leaf 496882861) (.leaf 487894638))) (.branch 111 (.branch 110 (.leaf 479076720) (.leaf 470425529)) (.branch 112 (.leaf 461937579) (.leaf 453609471)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 445437893) (.leaf 437419614)) (.branch 116 (.leaf 429551485) (.leaf 421830433))) (.branch 119 (.branch 118 (.leaf 414253459) (.leaf 406817639)) (.branch 120 (.leaf 399520119) (.leaf 392358111)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 385).prefactor = (2333705327353693/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 385).cutoff/(generalMeanRows 385).c)).2 =
    (217877939319293/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 385).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 385).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 385).q*(generalMeanRows 385).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 385).q*(generalMeanRows 385).cutoff/2-2 = (16834/7751:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable156.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 385).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 385

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 385).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 385).criticalRate j.val*(generalMeanRows 385).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 385).c*(generalMeanRows 385).criticalPoint j.val)).2-
      (generalMeanRows 385).J/2-(generalMeanRows 385).error (generalMeanGrid j.val)+
      (generalMeanRows 385).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 385).c)).2-
      (generalMeanRows 385).J/2-(generalMeanRows 385).error 4 := by
  have he : (generalMeanRows 385).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 385) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 385)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0385

/-! Kernel-checked entropy margins for general spectral rectangle 386. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0386
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5282969480) (.branch 2 (.leaf 5114659780) (.leaf 4953867499))) (.branch 5 (.branch 4 (.leaf 4800154899) (.leaf 4653115567)) (.branch 6 (.leaf 4512371682) (.leaf 4377571567)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4248387507) (.leaf 4124513780)) (.branch 10 (.leaf 4005664889) (.leaf 3891573967))) (.branch 13 (.branch 12 (.leaf 3781991327) (.leaf 3676683156)) (.branch 14 (.leaf 3575430319) (.leaf 3478027280))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3384281104) (.branch 17 (.leaf 3294010560) (.leaf 3207045288))) (.branch 20 (.branch 19 (.leaf 3123225042) (.leaf 3042398990)) (.branch 21 (.leaf 2964425074) (.leaf 2889169419)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2816505787) (.leaf 2746315077)) (.branch 25 (.leaf 2678484854) (.leaf 2612908928))) (.branch 28 (.branch 27 (.leaf 2549486946) (.leaf 2488124029)) (.branch 29 (.leaf 2428730427) (.leaf 2371221198)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2315515918) (.branch 32 (.leaf 2261538398) (.leaf 2209216434))) (.branch 35 (.branch 34 (.leaf 2158481563) (.leaf 2109268842)) (.branch 36 (.leaf 2061516642) (.leaf 2015166448)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1970162684) (.leaf 1926452538)) (.branch 40 (.leaf 1883985807) (.leaf 1842714744))) (.branch 43 (.branch 42 (.leaf 1802593924) (.leaf 1763580110)) (.branch 44 (.leaf 1725632130) (.leaf 1688710766))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1652778642) (.branch 47 (.leaf 1617800127) (.leaf 1583741237))) (.branch 50 (.branch 49 (.leaf 1550569546) (.leaf 1518254105)) (.branch 51 (.leaf 1486765361) (.leaf 1456075080)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1426156285) (.leaf 1396983181)) (.branch 55 (.leaf 1368531101) (.leaf 1340776442))) (.branch 58 (.branch 57 (.leaf 1313696614) (.leaf 1287269985)) (.branch 59 (.leaf 1261475836) (.leaf 1236294311))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1211706376) (.branch 62 (.leaf 1187693777) (.leaf 1164239001))) (.branch 65 (.branch 64 (.leaf 1141325239) (.leaf 1118936357)) (.branch 66 (.leaf 1097056852) (.leaf 1075671833)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1054766984) (.leaf 1034328541)) (.branch 70 (.leaf 1014343261) (.leaf 994798403))) (.branch 73 (.branch 72 (.leaf 975681700) (.leaf 956981341)) (.branch 74 (.leaf 938685945) (.leaf 920784545))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 903266568) (.branch 77 (.leaf 886121817) (.leaf 869340456))) (.branch 80 (.branch 79 (.leaf 852912989) (.leaf 836830251)) (.branch 81 (.leaf 821083388) (.leaf 805663849)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 790563367) (.leaf 775773952)) (.branch 85 (.leaf 761287875) (.leaf 747097659))) (.branch 88 (.branch 87 (.leaf 733196069) (.leaf 719576102)) (.branch 89 (.leaf 706230973) (.leaf 693154114)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 680339157) (.branch 92 (.leaf 667779932) (.leaf 655470455))) (.branch 95 (.branch 94 (.leaf 643404923) (.leaf 631577708)) (.branch 96 (.leaf 619983345) (.leaf 608616532)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 597472119) (.leaf 586545105)) (.branch 100 (.leaf 575830631) (.leaf 565323974))) (.branch 103 (.branch 102 (.leaf 555020547) (.leaf 544915885)) (.branch 104 (.leaf 535005648) (.leaf 525285615))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 515751678) (.leaf 506399838)) (.branch 108 (.leaf 497226204) (.leaf 488226985))) (.branch 111 (.branch 110 (.leaf 479398491) (.leaf 470737126)) (.branch 112 (.leaf 462239387) (.leaf 453901859)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 445721214) (.leaf 437694209)) (.branch 116 (.leaf 429817677) (.leaf 422088535))) (.branch 119 (.branch 118 (.leaf 414503770) (.leaf 407060446)) (.branch 120 (.leaf 399755696) (.leaf 392586721)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 386).prefactor = (186762645213841/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 386).cutoff/(generalMeanRows 386).c)).2 =
    (432792913507929/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 386).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 386).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 386).q*(generalMeanRows 386).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 386).q*(generalMeanRows 386).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable148.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 386).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 386

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 386).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 386).criticalRate j.val*(generalMeanRows 386).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 386).c*(generalMeanRows 386).criticalPoint j.val)).2-
      (generalMeanRows 386).J/2-(generalMeanRows 386).error (generalMeanGrid j.val)+
      (generalMeanRows 386).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 386).c)).2-
      (generalMeanRows 386).J/2-(generalMeanRows 386).error 4 := by
  have he : (generalMeanRows 386).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 386) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 386)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0386

/-! Kernel-checked entropy margins for general spectral rectangle 387. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0387
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5209020101) (.branch 2 (.leaf 5040442899) (.leaf 4879418363))) (.branch 5 (.branch 4 (.leaf 4725507273) (.leaf 4578301810)) (.branch 6 (.leaf 4437422817) (.leaf 4302517348)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4173256476) (.leaf 4049333325)) (.branch 10 (.leaf 3930461295) (.leaf 3816372462))) (.branch 13 (.branch 12 (.leaf 3706816130) (.leaf 3601557515)) (.branch 14 (.leaf 3500376553) (.leaf 3403066812))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3309434501) (.branch 17 (.leaf 3219297560) (.leaf 3132484835))) (.branch 20 (.branch 19 (.leaf 3048835311) (.leaf 2968197416)) (.branch 21 (.leaf 2890428380) (.leaf 2815393638)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2742966288) (.leaf 2673026584)) (.branch 25 (.leaf 2605461473) (.leaf 2540164162))) (.branch 28 (.branch 27 (.leaf 2477033719) (.leaf 2415974703)) (.branch 29 (.leaf 2356896818) (.leaf 2299714598)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2244347108) (.branch 32 (.leaf 2190717666) (.leaf 2138753590))) (.branch 35 (.branch 34 (.leaf 2088385955) (.leaf 2039549369)) (.branch 36 (.leaf 1992181768) (.leaf 1946224216)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1901620730) (.leaf 1858318103)) (.branch 40 (.leaf 1816265747) (.leaf 1775415547))) (.branch 43 (.branch 42 (.leaf 1735721716) (.leaf 1697140669)) (.branch 44 (.leaf 1659630896) (.leaf 1623152853))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1587668846) (.branch 47 (.leaf 1553142938) (.leaf 1519540845))) (.branch 50 (.branch 49 (.leaf 1486829855) (.leaf 1454978740)) (.branch 51 (.leaf 1423957674) (.leaf 1393738164)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1364292978) (.leaf 1335596076)) (.branch 55 (.leaf 1307622553) (.leaf 1280348577))) (.branch 58 (.branch 57 (.leaf 1253751334) (.leaf 1227808979)) (.branch 59 (.leaf 1202500583) (.leaf 1177806088))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1153706267) (.branch 62 (.leaf 1130182677) (.leaf 1107217622))) (.branch 65 (.branch 64 (.leaf 1084794121) (.leaf 1062895865)) (.branch 66 (.leaf 1041507191) (.leaf 1020613048)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1000198968) (.leaf 980251038)) (.branch 70 (.leaf 960755874) (.leaf 941700598))) (.branch 73 (.branch 72 (.leaf 923072811) (.leaf 904860573)) (.branch 74 (.leaf 887052381) (.leaf 869637151))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 852604195) (.branch 77 (.leaf 835943207) (.leaf 819644245))) (.branch 80 (.branch 79 (.leaf 803697713) (.leaf 788094348)) (.branch 81 (.leaf 772825203) (.leaf 757881637)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 743255298) (.leaf 728938112)) (.branch 85 (.leaf 714922273) (.leaf 701200227))) (.branch 88 (.branch 87 (.leaf 687764667) (.leaf 674608521)) (.branch 89 (.leaf 661724938) (.leaf 649107286)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 636749138) (.branch 92 (.leaf 624644266) (.leaf 612786632))) (.branch 95 (.branch 94 (.leaf 601170381) (.leaf 589789835)) (.branch 96 (.leaf 578639482) (.leaf 567713977)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 557008126) (.leaf 546516890)) (.branch 100 (.leaf 536235372) (.leaf 526158815))) (.branch 103 (.branch 102 (.leaf 516282595) (.leaf 506602219)) (.branch 104 (.leaf 497113319) (.leaf 487811643))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 478693060) (.leaf 469753548)) (.branch 108 (.leaf 460989192) (.leaf 452396182))) (.branch 111 (.branch 110 (.leaf 443970810) (.leaf 435709463)) (.branch 112 (.leaf 427608621) (.leaf 419664857)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 411874831) (.leaf 404235287)) (.branch 116 (.leaf 396743051) (.leaf 389395028))) (.branch 119 (.branch 118 (.leaf 382188201) (.leaf 375119627)) (.branch 120 (.leaf 368186435) (.leaf 361385822)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 387).prefactor = (2342366333989457/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 387).cutoff/(generalMeanRows 387).c)).2 =
    (424856363912193/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 387).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 387).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 387).q*(generalMeanRows 387).c/2-2 = (2879/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable152.value]
    have hcontinuation : (generalMeanRows 387).q*(generalMeanRows 387).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable148.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 387).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 387

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 387).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 387).criticalRate j.val*(generalMeanRows 387).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 387).c*(generalMeanRows 387).criticalPoint j.val)).2-
      (generalMeanRows 387).J/2-(generalMeanRows 387).error (generalMeanGrid j.val)+
      (generalMeanRows 387).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 387).c)).2-
      (generalMeanRows 387).J/2-(generalMeanRows 387).error 4 := by
  have he : (generalMeanRows 387).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 387) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 387)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0387

/-! Kernel-checked entropy margins for general spectral rectangle 388. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0388
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5284329123) (.branch 2 (.leaf 5115963587) (.leaf 4955103899))) (.branch 5 (.branch 4 (.leaf 4801314059) (.leaf 4654189223)) (.branch 6 (.leaf 4513352982) (.leaf 4378454929)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4249168489) (.leaf 4125188962)) (.branch 10 (.leaf 4006231765) (.leaf 3892030848))) (.branch 13 (.branch 12 (.leaf 3782337250) (.leaf 3676917803)) (.branch 14 (.leaf 3575553945) (.leaf 3478040641))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3384185401) (.branch 17 (.leaf 3293807380) (.leaf 3206736555))) (.branch 20 (.branch 19 (.leaf 3122812968) (.leaf 3041886038)) (.branch 21 (.leaf 2963813915) (.leaf 2888462902)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2815706908) (.leaf 2745426947)) (.branch 25 (.leaf 2677510680) (.leaf 2611851985))) (.branch 28 (.branch 27 (.leaf 2548350560) (.leaf 2486911558)) (.branch 29 (.leaf 2427445245) (.leaf 2369866681)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2314095428) (.branch 32 (.leaf 2260055277) (.leaf 2207673990))) (.branch 35 (.branch 34 (.leaf 2156883062) (.leaf 2107617503)) (.branch 36 (.leaf 2059815625) (.leaf 2013418854)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1968371546) (.leaf 1924620820)) (.branch 40 (.leaf 1882116397) (.leaf 1840810456))) (.branch 43 (.branch 42 (.leaf 1800657492) (.leaf 1761614186)) (.branch 44 (.leaf 1723639286) (.leaf 1686693490))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1650739340) (.branch 47 (.leaf 1615741120) (.leaf 1581664765))) (.branch 50 (.branch 49 (.leaf 1548477765) (.leaf 1516149088)) (.branch 51 (.leaf 1484649101) (.leaf 1453949490)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1424023197) (.leaf 1394844352)) (.branch 55 (.leaf 1366388210) (.leaf 1338631094))) (.branch 58 (.branch 57 (.leaf 1311550340) (.leaf 1285124246)) (.branch 59 (.leaf 1259332021) (.leaf 1234153743))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1209570312) (.branch 62 (.leaf 1185563408) (.leaf 1162115457))) (.branch 65 (.branch 64 (.leaf 1139209592) (.leaf 1116829615)) (.branch 66 (.leaf 1094959971) (.leaf 1073585711)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1052692469) (.leaf 1032266427)) (.branch 70 (.leaf 1012294295) (.leaf 992763283))) (.branch 73 (.branch 72 (.leaf 973661079) (.leaf 954975827)) (.branch 74 (.leaf 936696105) (.leaf 918810905))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 901309614) (.branch 77 (.leaf 884181999) (.leaf 867418186))) (.branch 80 (.branch 79 (.leaf 851008647) (.leaf 834944182)) (.branch 81 (.leaf 819215907) (.leaf 803815240)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 788733885) (.leaf 773963825)) (.branch 85 (.leaf 759497305) (.leaf 745326823))) (.branch 88 (.branch 87 (.leaf 731445120) (.leaf 717845169)) (.branch 89 (.leaf 704520167) (.leaf 691463521)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 678668846) (.branch 92 (.leaf 666129953) (.leaf 653840842))) (.branch 95 (.branch 94 (.leaf 641795692) (.leaf 629988859)) (.branch 96 (.leaf 618414864) (.leaf 607068390)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 595944274) (.leaf 585037504)) (.branch 100 (.leaf 574343207) (.leaf 563856652))) (.branch 103 (.branch 102 (.leaf 553573237) (.leaf 543488492)) (.branch 104 (.leaf 533598066) (.leaf 523897729))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 514383365) (.leaf 505050968)) (.branch 108 (.leaf 495896640) (.leaf 486916584))) (.branch 111 (.branch 110 (.leaf 478107104) (.leaf 469464597)) (.branch 112 (.leaf 460985557) (.leaf 452666563)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 444504284) (.leaf 436495472)) (.branch 116 (.leaf 428636957) (.leaf 420925652))) (.branch 119 (.branch 118 (.leaf 413358542) (.leaf 405932688)) (.branch 120 (.leaf 398645221) (.leaf 391493340)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 388).prefactor = (2327478420157369/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 388).cutoff/(generalMeanRows 388).c)).2 =
    (214919350805249/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 388).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 388).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 388).q*(generalMeanRows 388).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 388).q*(generalMeanRows 388).cutoff/2-2 = (16742/7797:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable150.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 388).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 388

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 388).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 388).criticalRate j.val*(generalMeanRows 388).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 388).c*(generalMeanRows 388).criticalPoint j.val)).2-
      (generalMeanRows 388).J/2-(generalMeanRows 388).error (generalMeanGrid j.val)+
      (generalMeanRows 388).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 388).c)).2-
      (generalMeanRows 388).J/2-(generalMeanRows 388).error 4 := by
  have he : (generalMeanRows 388).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 388) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 388)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0388

/-! Kernel-checked entropy margins for general spectral rectangle 389. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0389
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5210724672) (.branch 2 (.leaf 5042088220) (.leaf 4880992976))) (.branch 5 (.branch 4 (.leaf 4727001448) (.leaf 4579707379)) (.branch 6 (.leaf 4438733013) (.leaf 4303726667)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4174360548) (.leaf 4050328795)) (.branch 10 (.leaf 3931345718) (.leaf 3817144202))) (.branch 13 (.branch 12 (.leaf 3707474272) (.leaf 3602101788)) (.branch 14 (.leaf 3500807251) (.leaf 3403384731))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3309640874) (.branch 17 (.leaf 3219394005) (.leaf 3132473303))) (.branch 20 (.branch 19 (.leaf 3048718039) (.leaf 2967976891)) (.branch 21 (.leaf 2890107293) (.leaf 2814974858)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2742452827) (.leaf 2672421571)) (.branch 25 (.leaf 2604768128) (.leaf 2539385773))) (.branch 28 (.branch 27 (.leaf 2476173625) (.leaf 2415036271)) (.branch 29 (.leaf 2355883434) (.leaf 2298629646)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2243193960) (.branch 32 (.leaf 2189499672) (.leaf 2137474065))) (.branch 35 (.branch 34 (.leaf 2087048173) (.leaf 2038156555)) (.branch 36 (.leaf 1990737089) (.leaf 1944730779)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1900081575) (.leaf 1856736199)) (.branch 40 (.leaf 1814643990) (.leaf 1773756755))) (.branch 43 (.branch 42 (.leaf 1734028629) (.leaf 1695415945)) (.branch 44 (.leaf 1657877113) (.leaf 1621372505))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1585864346) (.branch 47 (.leaf 1551316612) (.leaf 1517694939))) (.branch 50 (.branch 49 (.leaf 1484966532) (.leaf 1453100080)) (.branch 51 (.leaf 1422065676) (.leaf 1391834748)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1362379984) (.leaf 1333675267)) (.branch 55 (.leaf 1305695616) (.leaf 1278417124))) (.branch 58 (.branch 57 (.leaf 1251816905) (.leaf 1225873041)) (.branch 59 (.leaf 1200564535) (.leaf 1175871262))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1151773927) (.branch 62 (.leaf 1128254024) (.leaf 1105293796))) (.branch 65 (.branch 64 (.leaf 1082876199) (.leaf 1060984869)) (.branch 66 (.leaf 1039604084) (.leaf 1018718740)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 998314314) (.leaf 978376845)) (.branch 70 (.leaf 958892898) (.leaf 939849548))) (.branch 73 (.branch 72 (.leaf 921234351) (.leaf 903035322)) (.branch 74 (.leaf 885240916) (.leaf 867840009))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 850821875) (.branch 77 (.leaf 834176169) (.leaf 817892914))) (.branch 80 (.branch 79 (.leaf 801962479) (.leaf 786375569)) (.branch 81 (.leaf 771123206) (.leaf 756196718)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 741587724) (.leaf 727288124)) (.branch 85 (.leaf 713290084) (.leaf 699586027))) (.branch 88 (.branch 87 (.leaf 686168622) (.leaf 673030773)) (.branch 89 (.leaf 660165609) (.leaf 647566477)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 635226930) (.branch 92 (.leaf 623140722) (.leaf 611301798))) (.branch 95 (.branch 94 (.leaf 599704287) (.leaf 588342493)) (.branch 96 (.leaf 577210893) (.leaf 566304124)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 555616981) (.leaf 545144412)) (.branch 100 (.leaf 534881509) (.leaf 524823502))) (.branch 103 (.branch 102 (.leaf 514965759) (.leaf 505303777)) (.branch 104 (.leaf 495833176) (.leaf 486549700))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 477449207) (.leaf 468527667)) (.branch 108 (.leaf 459781160) (.leaf 451205870))) (.branch 111 (.branch 110 (.leaf 442798081) (.leaf 434554174)) (.branch 112 (.leaf 426470628) (.leaf 418544007)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 410770969) (.leaf 403148253)) (.branch 116 (.leaf 395672681) (.leaf 388341157))) (.branch 119 (.branch 118 (.leaf 381150660) (.leaf 374098243)) (.branch 120 (.leaf 367181033) (.leaf 360396227)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 389).prefactor = (2335350664318451/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 389).cutoff/(generalMeanRows 389).c)).2 =
    (10547553800369/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 389).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 389).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 389).q*(generalMeanRows 389).c/2-2 = (2879/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable152.value]
    have hcontinuation : (generalMeanRows 389).q*(generalMeanRows 389).cutoff/2-2 = (16742/7797:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable150.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 389).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 389

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 389).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 389).criticalRate j.val*(generalMeanRows 389).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 389).c*(generalMeanRows 389).criticalPoint j.val)).2-
      (generalMeanRows 389).J/2-(generalMeanRows 389).error (generalMeanGrid j.val)+
      (generalMeanRows 389).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 389).c)).2-
      (generalMeanRows 389).J/2-(generalMeanRows 389).error 4 := by
  have he : (generalMeanRows 389).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 389) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 389)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0389

/-! Kernel-checked entropy margins for general spectral rectangle 390. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0390
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5229928663) (.branch 2 (.leaf 5060671540) (.leaf 4898969140))) (.branch 5 (.branch 4 (.leaf 4744384247) (.leaf 4596510810)) (.branch 6 (.leaf 4454971224) (.leaf 4319413900)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4189511090) (.leaf 4064956937)) (.branch 10 (.leaf 3945465710) (.leaf 3830770223))) (.branch 13 (.branch 12 (.leaf 3720620397) (.leaf 3614781956)) (.branch 14 (.leaf 3513035245) (.leaf 3415174153))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3321005127) (.branch 17 (.leaf 3230346279) (.leaf 3143026554))) (.branch 20 (.branch 19 (.leaf 3058884985) (.leaf 2977769994)) (.branch 21 (.leaf 2899538758) (.leaf 2824056619)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2751196547) (.leaf 2680838635)) (.branch 25 (.leaf 2612869642) (.leaf 2547182562))) (.branch 28 (.branch 27 (.leaf 2483676228) (.leaf 2422254947)) (.branch 29 (.leaf 2362828159) (.leaf 2305310117)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2249619596) (.branch 32 (.leaf 2195679614) (.leaf 2143417185))) (.branch 35 (.branch 34 (.leaf 2092763072) (.leaf 2043651569)) (.branch 36 (.leaf 1996020296) (.leaf 1949810001)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1904964381) (.leaf 1861429913)) (.branch 40 (.leaf 1819155695) (.leaf 1778093300))) (.branch 43 (.branch 42 (.leaf 1738196631) (.leaf 1699421798)) (.branch 44 (.leaf 1661726992) (.leaf 1625072371))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1589419952) (.branch 47 (.leaf 1554733509) (.leaf 1520978483))) (.branch 50 (.branch 49 (.leaf 1488121886) (.leaf 1456132222)) (.branch 51 (.leaf 1424979405) (.leaf 1394634687)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1365070586) (.leaf 1336260823)) (.branch 55 (.leaf 1308180257) (.leaf 1280804827))) (.branch 58 (.branch 57 (.leaf 1254111498) (.leaf 1228078209)) (.branch 59 (.leaf 1202683822) (.leaf 1177908078))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1153731551) (.branch 62 (.leaf 1130135611) (.leaf 1107102379))) (.branch 65 (.branch 64 (.leaf 1084614694) (.leaf 1062656078)) (.branch 66 (.leaf 1041210701) (.leaf 1020263352)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 999799409) (.leaf 979804811)) (.branch 70 (.leaf 960266032) (.leaf 941170052))) (.branch 73 (.branch 72 (.leaf 922504342) (.leaf 904256834)) (.branch 74 (.leaf 886415900) (.leaf 868970338))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 851909348) (.branch 77 (.leaf 835222512) (.leaf 818899784))) (.branch 80 (.branch 79 (.leaf 802931466) (.leaf 787308199)) (.branch 81 (.leaf 772020942) (.leaf 757060966)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 742419831) (.leaf 728089383)) (.branch 85 (.leaf 714061734) (.leaf 700329259))) (.branch 88 (.branch 87 (.leaf 686884576) (.leaf 673720543)) (.branch 89 (.leaf 660830245) (.leaf 648206985)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 635844275) (.branch 92 (.leaf 623735830) (.leaf 611875556))) (.branch 95 (.branch 94 (.leaf 600257545) (.leaf 588876067)) (.branch 96 (.leaf 577725565) (.leaf 566800644)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 556096068) (.leaf 545606755)) (.branch 100 (.leaf 535327768) (.leaf 525254312))) (.branch 103 (.branch 102 (.leaf 515381726) (.leaf 505705483)) (.branch 104 (.leaf 496221180) (.leaf 486924537))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 477811389) (.leaf 468877686)) (.branch 108 (.leaf 460119488) (.leaf 451532957))) (.branch 111 (.branch 110 (.leaf 443114362) (.leaf 434860064)) (.branch 112 (.leaf 426766524) (.leaf 418830293)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 411048009) (.leaf 403416398)) (.branch 116 (.leaf 395932269) (.leaf 388592509))) (.branch 119 (.branch 118 (.leaf 381394086) (.leaf 374334040)) (.branch 120 (.leaf 367409486) (.leaf 360617608)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 390).prefactor = (2336158287255847/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 390).cutoff/(generalMeanRows 390).c)).2 =
    (209478320892503/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 390).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 390).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 390).q*(generalMeanRows 390).c/2-2 = (2879/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable152.value]
    have hcontinuation : (generalMeanRows 390).q*(generalMeanRows 390).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 390).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 390

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 390).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 390).criticalRate j.val*(generalMeanRows 390).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 390).c*(generalMeanRows 390).criticalPoint j.val)).2-
      (generalMeanRows 390).J/2-(generalMeanRows 390).error (generalMeanGrid j.val)+
      (generalMeanRows 390).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 390).c)).2-
      (generalMeanRows 390).J/2-(generalMeanRows 390).error 4 := by
  have he : (generalMeanRows 390).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 390) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 390)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0390

/-! Kernel-checked entropy margins for general spectral rectangle 391. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0391
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5157909944) (.branch 2 (.leaf 4988417295) (.leaf 4826514725))) (.branch 5 (.branch 4 (.leaf 4671763470) (.leaf 4523756018)) (.branch 6 (.leaf 4382113375) (.leaf 4246482633)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4116534787) (.leaf 3991962781)) (.branch 10 (.leaf 3872479742) (.leaf 3757817390))) (.branch 13 (.branch 12 (.leaf 3647724602) (.leaf 3541966099)) (.branch 14 (.leaf 3440321267) (.leaf 3342583073))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3248557081) (.branch 17 (.leaf 3158060550) (.leaf 3070921610))) (.branch 20 (.branch 19 (.leaf 2986978506) (.leaf 2906078901)) (.branch 21 (.leaf 2828079243) (.leaf 2752844170)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2680245972) (.leaf 2610164088)) (.branch 25 (.leaf 2542484643) (.leaf 2477100022))) (.branch 28 (.branch 27 (.leaf 2413908469) (.leaf 2352813720)) (.branch 29 (.leaf 2293724665) (.leaf 2236555024)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2181223057) (.branch 32 (.leaf 2127651287) (.leaf 2075766244))) (.branch 35 (.branch 34 (.leaf 2025498227) (.leaf 1976781081)) (.branch 36 (.leaf 1929551989) (.leaf 1883751277)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1839322235) (.leaf 1796210946)) (.branch 40 (.leaf 1754366126) (.leaf 1713738978))) (.branch 43 (.branch 42 (.leaf 1674283050) (.leaf 1635954104)) (.branch 44 (.leaf 1598709997) (.leaf 1562510563))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1527317506) (.branch 47 (.leaf 1493094300) (.leaf 1459806089))) (.branch 50 (.branch 49 (.leaf 1427419604) (.leaf 1395903074)) (.branch 51 (.leaf 1365226149) (.leaf 1335359825)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1306276373) (.leaf 1277949274)) (.branch 55 (.leaf 1250353155) (.leaf 1223463733))) (.branch 58 (.branch 57 (.leaf 1197257757) (.leaf 1171712957)) (.branch 59 (.leaf 1146807995) (.leaf 1122522418))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1098836613) (.branch 62 (.leaf 1075731768) (.leaf 1053189830))) (.branch 65 (.branch 64 (.leaf 1031193470) (.leaf 1009726048)) (.branch 66 (.leaf 988771578) (.leaf 968314700)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 948340645) (.leaf 928835213)) (.branch 70 (.leaf 909784744) (.leaf 891176090))) (.branch 73 (.branch 72 (.leaf 872996596) (.leaf 855234076)) (.branch 74 (.leaf 837876787) (.leaf 820913417))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 804333060) (.branch 77 (.leaf 788125197) (.leaf 772279685))) (.branch 80 (.branch 79 (.leaf 756786733) (.leaf 741636892)) (.branch 81 (.leaf 726821038) (.leaf 712330356)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 698156332) (.leaf 684290736)) (.branch 85 (.leaf 670725610) (.leaf 657453259))) (.branch 88 (.branch 87 (.leaf 644466238) (.leaf 631757344)) (.branch 89 (.leaf 619319602) (.leaf 607146260)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 595230779) (.branch 92 (.leaf 583566822) (.leaf 572148248))) (.branch 95 (.branch 94 (.leaf 560969106) (.leaf 550023624)) (.branch 96 (.leaf 539306202) (.leaf 528811411)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 518533980) (.leaf 508468793)) (.branch 100 (.leaf 498610883) (.leaf 488955425))) (.branch 103 (.branch 102 (.leaf 479497735) (.leaf 470233258)) (.branch 104 (.leaf 461157569) (.leaf 452266369))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 443555472) (.leaf 435020813)) (.branch 108 (.leaf 426658435) (.leaf 418464486))) (.branch 111 (.branch 110 (.leaf 410435222) (.leaf 402566995)) (.branch 112 (.leaf 394856255) (.leaf 387299545)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 379893497) (.leaf 372634832)) (.branch 116 (.leaf 365520353) (.leaf 358546946))) (.branch 119 (.branch 118 (.leaf 351711576) (.leaf 345011283)) (.branch 120 (.leaf 338443182) (.leaf 332004460)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 391).prefactor = (937649445461797/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 391).cutoff/(generalMeanRows 391).c)).2 =
    (411082585354099/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 391).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 391).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 391).q*(generalMeanRows 391).c/2-2 = (593/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable154.value]
    have hcontinuation : (generalMeanRows 391).q*(generalMeanRows 391).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 391).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 391

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 391).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 391).criticalRate j.val*(generalMeanRows 391).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 391).c*(generalMeanRows 391).criticalPoint j.val)).2-
      (generalMeanRows 391).J/2-(generalMeanRows 391).error (generalMeanGrid j.val)+
      (generalMeanRows 391).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 391).c)).2-
      (generalMeanRows 391).J/2-(generalMeanRows 391).error 4 := by
  have he : (generalMeanRows 391).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 391) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 391)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0391

/-! Kernel-checked entropy margins for general spectral rectangle 392. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0392
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5228348937) (.branch 2 (.leaf 5059142105) (.leaf 4897501988))) (.branch 5 (.branch 4 (.leaf 4742989614) (.leaf 4595197350)) (.branch 6 (.leaf 4453746166) (.leaf 4318283187)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4188479513) (.leaf 4064028247)) (.branch 10 (.leaf 3944642732) (.leaf 3830054951))) (.branch 13 (.branch 12 (.leaf 3720014085) (.leaf 3614285198)) (.branch 14 (.leaf 3512648053) (.leaf 3414896020))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3320835092) (.branch 17 (.leaf 3230282981) (.leaf 3143068286))) (.branch 20 (.branch 19 (.leaf 3059029737) (.leaf 2978015497)) (.branch 21 (.leaf 2899882521) (.leaf 2824495965)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2751728642) (.leaf 2681460518)) (.branch 25 (.leaf 2613578250) (.leaf 2547974753))) (.branch 28 (.branch 27 (.leaf 2484548801) (.leaf 2423204663)) (.branch 29 (.leaf 2363851752) (.leaf 2306404314)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2250781128) (.branch 32 (.leaf 2196905230) (.leaf 2144703657))) (.branch 35 (.branch 34 (.leaf 2094107209) (.leaf 2045050224)) (.branch 36 (.leaf 1997470371) (.leaf 1951308454)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1906508233) (.leaf 1863016249)) (.branch 40 (.leaf 1820781671) (.leaf 1779756143))) (.branch 43 (.branch 42 (.leaf 1739893644) (.leaf 1701150360)) (.branch 44 (.leaf 1663484561) (.leaf 1626856483))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1591228224) (.branch 47 (.leaf 1556563639) (.leaf 1522828248))) (.branch 50 (.branch 49 (.leaf 1489989143) (.leaf 1458014909)) (.branch 51 (.leaf 1426875537) (.leaf 1396542359)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1366987970) (.leaf 1338186165)) (.branch 55 (.leaf 1310111878) (.leaf 1282741122))) (.branch 58 (.branch 57 (.leaf 1256050932) (.leaf 1230019319)) (.branch 59 (.leaf 1204625212) (.leaf 1179848418))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1155669579) (.branch 62 (.leaf 1132070124) (.leaf 1109032238))) (.branch 65 (.branch 64 (.leaf 1086538818) (.leaf 1064573444)) (.branch 66 (.leaf 1043120343) (.leaf 1022164358)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1001690919) (.leaf 981686015)) (.branch 70 (.leaf 962136167) (.leaf 943028407))) (.branch 73 (.branch 72 (.leaf 924350247) (.leaf 906089663)) (.branch 74 (.leaf 888235072) (.leaf 870775310))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 853699615) (.branch 77 (.leaf 836997608) (.leaf 820659278))) (.branch 80 (.branch 79 (.leaf 804674961) (.leaf 789035332)) (.branch 81 (.leaf 773731380) (.leaf 758754406)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 744096000) (.leaf 729748035)) (.branch 85 (.leaf 715702649) (.leaf 701952241))) (.branch 88 (.branch 87 (.leaf 688489454) (.leaf 675307169)) (.branch 89 (.leaf 662398491) (.leaf 649756745)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 637375462) (.branch 92 (.leaf 625248375) (.leaf 613369408))) (.branch 95 (.branch 94 (.leaf 601732670) (.leaf 590332448)) (.branch 96 (.leaf 579163197) (.leaf 568219537)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 557496248) (.leaf 546988257)) (.branch 100 (.leaf 536690642) (.leaf 526598616))) (.branch 103 (.branch 102 (.leaf 516707531) (.leaf 507012869)) (.branch 104 (.leaf 497510236) (.leaf 488195360))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 479064086) (.leaf 470112371)) (.branch 108 (.leaf 461336281) (.leaf 452731986))) (.branch 111 (.branch 110 (.leaf 444295759) (.leaf 436023970)) (.branch 112 (.leaf 427913082) (.leaf 419959651)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 412160322) (.leaf 404511823)) (.branch 116 (.leaf 397010967) (.leaf 389654646))) (.branch 119 (.branch 118 (.leaf 382439828) (.leaf 375363557)) (.branch 120 (.leaf 368422952) (.leaf 361615197)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 392).prefactor = (4686499069635937/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 392).cutoff/(generalMeanRows 392).c)).2 =
    (10547553800369/25000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 392).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 392).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 392).q*(generalMeanRows 392).c/2-2 = (2879/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable152.value]
    have hcontinuation : (generalMeanRows 392).q*(generalMeanRows 392).cutoff/2-2 = (16742/7797:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable150.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 392).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 392

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 392).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 392).criticalRate j.val*(generalMeanRows 392).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 392).c*(generalMeanRows 392).criticalPoint j.val)).2-
      (generalMeanRows 392).J/2-(generalMeanRows 392).error (generalMeanGrid j.val)+
      (generalMeanRows 392).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 392).c)).2-
      (generalMeanRows 392).J/2-(generalMeanRows 392).error 4 := by
  have he : (generalMeanRows 392).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 392) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 392)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0392

/-! Kernel-checked entropy margins for general spectral rectangle 393. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0393
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5155988776) (.branch 2 (.leaf 4986550048) (.leaf 4824713272))) (.branch 5 (.branch 4 (.leaf 4670037941) (.leaf 4522114969)) (.branch 6 (.leaf 4380563943) (.leaf 4245030678)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4115185022) (.leaf 3990718889)) (.branch 10 (.leaf 3871344484) (.leaf 3756792702))) (.branch 13 (.branch 12 (.leaf 3646811682) (.leaf 3541165494)) (.branch 14 (.leaf 3439632943) (.leaf 3342006482))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3248091223) (.branch 17 (.leaf 3157704030) (.leaf 3070672689))) (.branch 20 (.branch 19 (.leaf 2986835143) (.leaf 2906038802)) (.branch 21 (.leaf 2828139891) (.leaf 2753002865)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2680499859) (.leaf 2610510187)) (.branch 25 (.leaf 2542919873) (.leaf 2477621223))) (.branch 28 (.branch 27 (.leaf 2414512425) (.leaf 2353497177)) (.branch 29 (.leaf 2294484343) (.leaf 2237387638)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2182125326) (.branch 32 (.leaf 2128619946) (.leaf 2076798056))) (.branch 35 (.branch 34 (.leaf 2026589991) (.leaf 1977929638)) (.branch 36 (.leaf 1930754231) (.leaf 1885004154)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1840622758) (.leaf 1797556192)) (.branch 40 (.leaf 1755753241) (.leaf 1715165181))) (.branch 43 (.branch 42 (.leaf 1675745633) (.leaf 1637450439)) (.branch 44 (.leaf 1600237533) (.leaf 1564066828))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1528900108) (.branch 47 (.leaf 1494700926) (.leaf 1461434509))) (.branch 50 (.branch 49 (.leaf 1429067667) (.leaf 1397568707)) (.branch 51 (.leaf 1366907360) (.leaf 1337054698)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1307983070) (.leaf 1279666031)) (.branch 55 (.leaf 1252078285) (.leaf 1225195621))) (.branch 58 (.branch 57 (.leaf 1198994858) (.leaf 1173453797)) (.branch 59 (.leaf 1148551169) (.leaf 1124266585))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1100580498) (.branch 62 (.leaf 1077474160) (.leaf 1054929577))) (.branch 65 (.branch 64 (.leaf 1032929482) (.leaf 1011457290)) (.branch 66 (.leaf 990497073) (.leaf 970033522)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 950051923) (.leaf 930538126)) (.branch 70 (.leaf 911478518) (.leaf 892859999))) (.branch 73 (.branch 72 (.leaf 874669960) (.leaf 856896256)) (.branch 74 (.leaf 839527189) (.leaf 822551485))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 805958277) (.branch 77 (.leaf 789737085) (.leaf 773877798))) (.branch 80 (.branch 79 (.leaf 758370662) (.leaf 743206261)) (.branch 81 (.leaf 728375499) (.leaf 713869595)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 699680062) (.leaf 685798696)) (.branch 85 (.leaf 672217567) (.leaf 658929004))) (.branch 88 (.branch 87 (.leaf 645925587) (.leaf 633200133)) (.branch 89 (.leaf 620745691) (.leaf 608555529)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 596623126) (.branch 92 (.leaf 584942165) (.leaf 573506524))) (.branch 95 (.branch 94 (.leaf 562310265) (.leaf 551347633)) (.branch 96 (.leaf 540613045) (.leaf 530101085)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 519806494) (.leaf 509724169)) (.branch 100 (.leaf 499849156) (.leaf 490176642))) (.branch 103 (.branch 102 (.leaf 480701950) (.leaf 471420538)) (.branch 104 (.leaf 462327991) (.leaf 453420014))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 444692435) (.leaf 436141192)) (.branch 108 (.leaf 427762336) (.leaf 419552025))) (.branch 111 (.branch 110 (.leaf 411506517) (.leaf 403622172)) (.branch 112 (.leaf 395895444) (.leaf 388322881)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 380901120) (.leaf 373626886)) (.branch 116 (.leaf 366496986) (.leaf 359508310))) (.branch 119 (.branch 118 (.leaf 352657824) (.leaf 345942573)) (.branch 120 (.leaf 339359673) (.leaf 332906314)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 393).prefactor = (4702350243428711/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 393).cutoff/(generalMeanRows 393).c)).2 =
    (25876755973991/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 393).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 393).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 393).q*(generalMeanRows 393).c/2-2 = (593/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable154.value]
    have hcontinuation : (generalMeanRows 393).q*(generalMeanRows 393).cutoff/2-2 = (16742/7797:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable150.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 393).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 393

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 393).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 393).criticalRate j.val*(generalMeanRows 393).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 393).c*(generalMeanRows 393).criticalPoint j.val)).2-
      (generalMeanRows 393).J/2-(generalMeanRows 393).error (generalMeanGrid j.val)+
      (generalMeanRows 393).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 393).c)).2-
      (generalMeanRows 393).J/2-(generalMeanRows 393).error 4 := by
  have he : (generalMeanRows 393).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 393) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 393)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0393

/-! Kernel-checked entropy margins for general spectral rectangle 394. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0394
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5087344240) (.branch 2 (.leaf 4917654364) (.leaf 4755589641))) (.branch 5 (.branch 4 (.leaf 4600709731) (.leaf 4452605623)) (.branch 6 (.leaf 4310896904) (.leaf 4175229318)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4045272577) (.leaf 3920718400)) (.branch 10 (.leaf 3801278749) (.leaf 3686684230))) (.branch 13 (.branch 12 (.leaf 3576682653) (.leaf 3471037720)) (.branch 14 (.leaf 3369527839) (.leaf 3271945042))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3178093991) (.branch 17 (.leaf 3087791084) (.leaf 3000863619))) (.branch 20 (.branch 19 (.leaf 2917149044) (.leaf 2836494256)) (.branch 21 (.leaf 2758754962) (.leaf 2683795089)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2611486241) (.leaf 2541707197)) (.branch 25 (.leaf 2474343443) (.leaf 2409286750))) (.branch 28 (.branch 27 (.leaf 2346434768) (.leaf 2285690663)) (.branch 29 (.leaf 2226962769) (.leaf 2170164275)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2115212925) (.branch 32 (.leaf 2062030744) (.leaf 2010543782))) (.branch 35 (.branch 34 (.leaf 1960681873) (.leaf 1912378413)) (.branch 36 (.leaf 1865570152) (.leaf 1820196997)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1776201834) (.leaf 1733530355)) (.branch 40 (.leaf 1692130897) (.leaf 1651954298))) (.branch 43 (.branch 42 (.leaf 1612953753) (.leaf 1575084684)) (.branch 44 (.leaf 1538304618) (.leaf 1502573071))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1467851440) (.branch 47 (.leaf 1434102901) (.leaf 1401292312))) (.branch 50 (.branch 49 (.leaf 1369386128) (.leaf 1338352310)) (.branch 51 (.leaf 1308160250) (.leaf 1278780695)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1250185675) (.leaf 1222348440)) (.branch 55 (.leaf 1195243394) (.leaf 1168846037))) (.branch 58 (.branch 57 (.leaf 1143132912) (.leaf 1118081546)) (.branch 59 (.leaf 1093670410) (.leaf 1069878864))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1046687116) (.branch 62 (.leaf 1024076181) (.leaf 1002027841))) (.branch 65 (.branch 64 (.leaf 980524607) (.leaf 959549685)) (.branch 66 (.leaf 939086941) (.leaf 919120873)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 899636577) (.leaf 880619720)) (.branch 70 (.leaf 862056518) (.leaf 843933701))) (.branch 73 (.branch 72 (.leaf 826238500) (.leaf 808958615)) (.branch 74 (.leaf 792082201) (.leaf 775597842))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 759494535) (.branch 77 (.leaf 743761669) (.leaf 728389010))) (.branch 80 (.branch 79 (.leaf 713366684) (.leaf 698685161)) (.branch 81 (.leaf 684335239) (.leaf 670308031)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 656594952) (.leaf 643187705)) (.branch 85 (.leaf 630078270) (.leaf 617258892))) (.branch 88 (.branch 87 (.leaf 604722069) (.leaf 592460544)) (.branch 89 (.leaf 580467293) (.leaf 568735515)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 557258625) (.branch 92 (.leaf 546030245) (.leaf 535044195))) (.branch 95 (.branch 94 (.leaf 524294484) (.leaf 513775307)) (.branch 96 (.leaf 503481033) (.leaf 493406200)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 483545510) (.leaf 473893822)) (.branch 100 (.leaf 464446144) (.leaf 455197631))) (.branch 103 (.branch 102 (.leaf 446143578) (.leaf 437279413)) (.branch 104 (.leaf 428600694) (.leaf 420103107))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 411782456) (.leaf 403634663)) (.branch 108 (.leaf 395655761) (.leaf 387841892))) (.branch 111 (.branch 110 (.leaf 380189303) (.leaf 372694344)) (.branch 112 (.leaf 365353459) (.leaf 358163189)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 351120166) (.leaf 344221109)) (.branch 116 (.leaf 337462825) (.leaf 330842202))) (.branch 119 (.branch 118 (.leaf 324356207) (.leaf 318001885)) (.branch 120 (.leaf 311776358) (.leaf 305676818)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 394).prefactor = (2352116098497401/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 394).cutoff/(generalMeanRows 394).c)).2 =
    (100817511404327/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 394).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 394).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 394).q*(generalMeanRows 394).c/2-2 = (3051/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable153.value]
    have hcontinuation : (generalMeanRows 394).q*(generalMeanRows 394).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 394).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 394

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 394).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 394).criticalRate j.val*(generalMeanRows 394).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 394).c*(generalMeanRows 394).criticalPoint j.val)).2-
      (generalMeanRows 394).J/2-(generalMeanRows 394).error (generalMeanGrid j.val)+
      (generalMeanRows 394).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 394).c)).2-
      (generalMeanRows 394).J/2-(generalMeanRows 394).error 4 := by
  have he : (generalMeanRows 394).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 394) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 394)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0394

/-! Kernel-checked entropy margins for general spectral rectangle 395. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0395
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5104689964) (.branch 2 (.leaf 4934421516) (.leaf 4771804220))) (.branch 5 (.branch 4 (.leaf 4616396234) (.leaf 4467787153)) (.branch 6 (.leaf 4325595267) (.leaf 4189465110)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4059065271) (.leaf 3934086416)) (.branch 10 (.leaf 3814239526) (.leaf 3699254288))) (.branch 13 (.branch 12 (.leaf 3588877651) (.leaf 3482872512)) (.branch 14 (.leaf 3381016525) (.leaf 3283101011))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3188929968) (.branch 17 (.leaf 3098319165) (.leaf 3011095314))) (.branch 20 (.branch 19 (.leaf 2927095307) (.leaf 2846165520)) (.branch 21 (.leaf 2768161167) (.leaf 2692945712)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2620390321) (.leaf 2550373359)) (.branch 25 (.leaf 2482779924) (.leaf 2417501414))) (.branch 28 (.branch 27 (.leaf 2354435133) (.leaf 2293483916)) (.branch 29 (.leaf 2234555784) (.leaf 2177563631)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2122424919) (.branch 32 (.leaf 2069061410) (.leaf 2017398898))) (.branch 35 (.branch 34 (.leaf 1967366981) (.leaf 1918898826)) (.branch 36 (.leaf 1871930969) (.leaf 1826403111)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1782257943) (.leaf 1739440971)) (.branch 40 (.leaf 1697900358) (.leaf 1657586774))) (.branch 43 (.branch 42 (.leaf 1618453253) (.leaf 1580455066)) (.branch 44 (.leaf 1543549596) (.leaf 1507696219))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1472856202) (.branch 47 (.leaf 1438992594) (.leaf 1406070135))) (.branch 50 (.branch 49 (.leaf 1374055164) (.leaf 1342915534)) (.branch 51 (.leaf 1312620531) (.leaf 1283140804)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1254448287) (.leaf 1226516139)) (.branch 55 (.leaf 1199318676) (.leaf 1172831315))) (.branch 58 (.branch 57 (.leaf 1147030518) (.leaf 1121893739)) (.branch 59 (.leaf 1097399371) (.leaf 1073526705))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1050255883) (.branch 62 (.leaf 1027567854) (.leaf 1005444339))) (.branch 65 (.branch 64 (.leaf 983867788) (.leaf 962821349)) (.branch 66 (.leaf 942288836) (.leaf 922254692)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 902703963) (.leaf 883622267)) (.branch 70 (.leaf 864995771) (.leaf 846811163))) (.branch 73 (.branch 72 (.leaf 829055629) (.leaf 811716827)) (.branch 74 (.leaf 794782872) (.leaf 778242308))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 762084095) (.branch 77 (.leaf 746297586) (.leaf 730872513))) (.branch 80 (.branch 79 (.leaf 715798968) (.leaf 701067386)) (.branch 81 (.leaf 686668537) (.leaf 672593502)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 658833667) (.leaf 645380707)) (.branch 85 (.leaf 632226574) (.leaf 619363487))) (.branch 88 (.branch 87 (.leaf 606783920) (.leaf 594480588)) (.branch 89 (.leaf 582446445) (.leaf 570674666)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 559158645) (.branch 92 (.leaf 547891981) (.leaf 536868473))) (.branch 95 (.branch 94 (.leaf 526082110) (.leaf 515527067)) (.branch 96 (.leaf 505197693) (.leaf 495088509)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 485194199) (.leaf 475509602)) (.branch 100 (.leaf 466029712) (.leaf 456749666))) (.branch 103 (.branch 102 (.leaf 447664742) (.leaf 438770353)) (.branch 104 (.leaf 430062044) (.leaf 421535484))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 413186463) (.leaf 405010889)) (.branch 108 (.leaf 397004782) (.leaf 389164271))) (.branch 111 (.branch 110 (.leaf 381485590) (.leaf 373965076)) (.branch 112 (.leaf 366599162) (.leaf 359384376)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 352317339) (.leaf 345394760)) (.branch 116 (.leaf 338613433) (.leaf 331970236))) (.branch 119 (.branch 118 (.leaf 325462126) (.leaf 319086139)) (.branch 120 (.leaf 312839385) (.leaf 306719048)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 395).prefactor = (1180067917191777/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 395).cutoff/(generalMeanRows 395).c)).2 =
    (100817511404327/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 395).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 395).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 395).q*(generalMeanRows 395).c/2-2 = (3051/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable153.value]
    have hcontinuation : (generalMeanRows 395).q*(generalMeanRows 395).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 395).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 395

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 395).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 395).criticalRate j.val*(generalMeanRows 395).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 395).c*(generalMeanRows 395).criticalPoint j.val)).2-
      (generalMeanRows 395).J/2-(generalMeanRows 395).error (generalMeanGrid j.val)+
      (generalMeanRows 395).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 395).c)).2-
      (generalMeanRows 395).J/2-(generalMeanRows 395).error 4 := by
  have he : (generalMeanRows 395).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 395) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 395)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0395

/-! Kernel-checked entropy margins for general spectral rectangle 396. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0396
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5153802224) (.branch 2 (.leaf 4984431059) (.leaf 4822673021))) (.branch 5 (.branch 4 (.leaf 4668085892) (.leaf 4520259039)) (.branch 6 (.leaf 4378810662) (.leaf 4243385324)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4113651753) (.leaf 3989300859)) (.branch 10 (.leaf 3870043947) (.leaf 3755611112))) (.branch 13 (.branch 12 (.leaf 3645749782) (.leaf 3540223392)) (.branch 14 (.leaf 3438810188) (.leaf 3341302132))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3247503905) (.branch 17 (.leaf 3157231992) (.leaf 3070313851))) (.branch 20 (.branch 19 (.leaf 2986587147) (.leaf 2905899046)) (.branch 21 (.leaf 2828105572) (.leaf 2753071009)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2680667353) (.leaf 2610773806)) (.branch 25 (.leaf 2543276305) (.leaf 2478067091))) (.branch 28 (.branch 27 (.leaf 2415044305) (.leaf 2354111618)) (.branch 29 (.leaf 2295177883) (.leaf 2238156818)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2182966702) (.branch 32 (.leaf 2129530100) (.leaf 2077773605))) (.branch 35 (.branch 34 (.leaf 2027627596) (.leaf 1979026013)) (.branch 36 (.leaf 1931906149) (.leaf 1886208451)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1841876338) (.leaf 1798856031)) (.branch 40 (.leaf 1757096393) (.leaf 1716548776))) (.branch 43 (.branch 42 (.leaf 1677166883) (.leaf 1638906638)) (.branch 44 (.leaf 1601726057) (.leaf 1565585138))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1530445750) (.branch 47 (.leaf 1496271530) (.leaf 1463027787))) (.branch 50 (.branch 49 (.leaf 1430681417) (.leaf 1399200811)) (.branch 51 (.leaf 1368555779) (.leaf 1338717477)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1309658331) (.leaf 1281351977)) (.branch 55 (.leaf 1253773193) (.leaf 1226897845))) (.branch 58 (.branch 57 (.leaf 1200702827) (.leaf 1175166009)) (.branch 59 (.leaf 1150266193) (.leaf 1125983060))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1102297128) (.branch 62 (.leaf 1079189713) (.leaf 1056642885))) (.branch 65 (.branch 64 (.leaf 1034639437) (.leaf 1013162843)) (.branch 66 (.leaf 992197231) (.leaf 971727350)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 951738536) (.leaf 932216691)) (.branch 70 (.leaf 913148252) (.leaf 894520168))) (.branch 73 (.branch 72 (.leaf 876319874) (.leaf 858535269)) (.branch 74 (.leaf 841154700) (.leaf 824166931))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 807561136) (.branch 77 (.leaf 791326872) (.leaf 775454064))) (.branch 80 (.branch 79 (.leaf 759932994) (.leaf 744754276)) (.branch 81 (.leaf 729908849) (.leaf 715387960)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 701183151) (.leaf 687286247)) (.branch 85 (.leaf 673689344) (.leaf 660384796))) (.branch 88 (.branch 87 (.leaf 647365206) (.leaf 634623415)) (.branch 89 (.leaf 622152493) (.leaf 609945729)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 597996622) (.branch 92 (.leaf 586298873) (.leaf 574846377))) (.branch 95 (.branch 94 (.leaf 563633214) (.leaf 552653644)) (.branch 96 (.leaf 541902100) (.leaf 531373179)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 521061635) (.leaf 510962380)) (.branch 100 (.leaf 501070470) (.leaf 491381103))) (.branch 103 (.branch 102 (.leaf 481889613) (.leaf 472591469)) (.branch 104 (.leaf 463482263) (.leaf 454557711))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 445813647) (.leaf 437246019)) (.branch 108 (.leaf 428850884) (.leaf 420624405))) (.branch 111 (.branch 110 (.leaf 412562848) (.leaf 404662578)) (.branch 112 (.leaf 396920054) (.leaf 389331830)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 381894547) (.leaf 374604933)) (.branch 116 (.leaf 367459800) (.leaf 360456040))) (.branch 119 (.branch 118 (.leaf 353590623) (.leaf 346860597)) (.branch 120 (.leaf 340263081) (.leaf 333795266)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 396).prefactor = (471622362165803/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 396).cutoff/(generalMeanRows 396).c)).2 =
    (52122788435161/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 396).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 396).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 396).q*(generalMeanRows 396).c/2-2 = (593/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable154.value]
    have hcontinuation : (generalMeanRows 396).q*(generalMeanRows 396).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable148.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 396).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 396

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 396).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 396).criticalRate j.val*(generalMeanRows 396).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 396).c*(generalMeanRows 396).criticalPoint j.val)).2-
      (generalMeanRows 396).J/2-(generalMeanRows 396).error (generalMeanGrid j.val)+
      (generalMeanRows 396).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 396).c)).2-
      (generalMeanRows 396).J/2-(generalMeanRows 396).error 4 := by
  have he : (generalMeanRows 396).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 396) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 396)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0396

/-! Kernel-checked entropy margins for general spectral rectangle 397. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0397
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5279285943) (.branch 2 (.leaf 5108434758) (.leaf 4945238120))) (.branch 5 (.branch 4 (.leaf 4789250883) (.leaf 4640059727)) (.branch 6 (.leaf 4497280380) (.leaf 4360555136)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4229550630) (.leaf 4103955847)) (.branch 10 (.leaf 3983480321) (.leaf 3867852514))) (.branch 13 (.branch 12 (.leaf 3756818347) (.leaf 3650139871)) (.branch 14 (.leaf 3547594052) (.leaf 3448971675))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3354076333) (.branch 17 (.leaf 3262723511) (.leaf 3174739746))) (.branch 20 (.branch 19 (.leaf 3089961852) (.leaf 3008236211)) (.branch 21 (.leaf 2929418128) (.leaf 2853371223)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2779966881) (.leaf 2709083742)) (.branch 25 (.leaf 2640607228) (.leaf 2574429105))) (.branch 28 (.branch 27 (.leaf 2510447078) (.leaf 2448564421)) (.branch 29 (.leaf 2388689618) (.leaf 2330736053)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2274621696) (.branch 32 (.leaf 2220268833) (.leaf 2167603800))) (.branch 35 (.branch 34 (.leaf 2116556742) (.leaf 2067061387)) (.branch 36 (.leaf 2019054831) (.leaf 1972477347)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1927272192) (.leaf 1883385445)) (.branch 40 (.leaf 1840765834) (.leaf 1799364594))) (.branch 43 (.branch 42 (.leaf 1759135323) (.leaf 1720033845)) (.branch 44 (.leaf 1682018094) (.leaf 1645047989))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1609085329) (.branch 47 (.leaf 1574093691) (.leaf 1540038331))) (.branch 50 (.branch 49 (.leaf 1506886094) (.leaf 1474605331)) (.branch 51 (.leaf 1443165813) (.leaf 1412538665)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1382696285) (.leaf 1353612283)) (.branch 55 (.leaf 1325261417) (.leaf 1297619535))) (.branch 58 (.branch 57 (.leaf 1270663516) (.leaf 1244371217)) (.branch 59 (.leaf 1218721429) (.leaf 1193693824))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1169268914) (.branch 62 (.leaf 1145428008) (.leaf 1122153172))) (.branch 65 (.branch 64 (.leaf 1099427194) (.leaf 1077233547)) (.branch 66 (.leaf 1055556355) (.leaf 1034380366)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1013690915) (.leaf 993473902)) (.branch 70 (.leaf 973715763) (.leaf 954403445))) (.branch 73 (.branch 72 (.leaf 935524383) (.leaf 917066475)) (.branch 74 (.leaf 899018064) (.leaf 881367915))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 864105197) (.branch 77 (.leaf 847219465) (.leaf 830700642))) (.branch 80 (.branch 79 (.leaf 814539003) (.leaf 798725160)) (.branch 81 (.leaf 783250046) (.leaf 768104902)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 753281264) (.leaf 738770950)) (.branch 85 (.leaf 724566047) (.leaf 710658901))) (.branch 88 (.branch 87 (.leaf 697042106) (.leaf 683708493)) (.branch 89 (.leaf 670651120) (.leaf 657863265)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 645338415) (.branch 92 (.leaf 633070257) (.leaf 621052672))) (.branch 95 (.branch 94 (.leaf 609279726) (.leaf 597745665)) (.branch 96 (.leaf 586444902) (.leaf 575372020)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 564521755) (.leaf 553889000)) (.branch 100 (.leaf 543468792) (.leaf 533256309))) (.branch 103 (.branch 102 (.leaf 523246867) (.leaf 513435910)) (.branch 104 (.leaf 503819011) (.leaf 494391863))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 485150277) (.leaf 476090177)) (.branch 108 (.leaf 467207596) (.leaf 458498674))) (.branch 111 (.branch 110 (.leaf 449959649) (.leaf 441586862)) (.branch 112 (.leaf 433376746) (.leaf 425325827)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 417430719) (.leaf 409688123)) (.branch 116 (.leaf 402094822) (.leaf 394647680))) (.branch 119 (.branch 118 (.leaf 387343638) (.leaf 380179715)) (.branch 120 (.leaf 373152998) (.leaf 366260650)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 397).prefactor = (4747926258742349/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 397).cutoff/(generalMeanRows 397).c)).2 =
    (424856363912193/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 397).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 397).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 397).q*(generalMeanRows 397).c/2-2 = (2879/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable152.value]
    have hcontinuation : (generalMeanRows 397).q*(generalMeanRows 397).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable148.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 397).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 397

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 397).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 397).criticalRate j.val*(generalMeanRows 397).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 397).c*(generalMeanRows 397).criticalPoint j.val)).2-
      (generalMeanRows 397).J/2-(generalMeanRows 397).error (generalMeanGrid j.val)+
      (generalMeanRows 397).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 397).c)).2-
      (generalMeanRows 397).J/2-(generalMeanRows 397).error 4 := by
  have he : (generalMeanRows 397).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 397) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 397)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0397

/-! Kernel-checked entropy margins for general spectral rectangle 398. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0398
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5173427907) (.branch 2 (.leaf 5003416086) (.leaf 4841031929))) (.branch 5 (.branch 4 (.leaf 4685833439) (.leaf 4537410145)) (.branch 6 (.leaf 4395380351) (.leaf 4259388671)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4129103837) (.leaf 4004216722)) (.branch 10 (.leaf 3884438556) (.leaf 3769499324))) (.branch 13 (.branch 12 (.leaf 3659146315) (.leaf 3553142800)) (.branch 14 (.leaf 3451266834) (.leaf 3353310170))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3259077261) (.branch 17 (.leaf 3168384352) (.leaf 3081058643))) (.branch 20 (.branch 19 (.leaf 2996937533) (.leaf 2915867914)) (.branch 21 (.leaf 2837705525) (.leaf 2762314363)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2689566129) (.leaf 2619339731)) (.branch 25 (.leaf 2551520806) (.leaf 2486001297))) (.branch 28 (.branch 27 (.leaf 2422679045) (.leaf 2361457424)) (.branch 29 (.leaf 2302244991) (.leaf 2244955167)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2189505941) (.branch 32 (.leaf 2135819590) (.leaf 2083822423))) (.branch 35 (.branch 34 (.leaf 2033444538) (.leaf 1984619601)) (.branch 36 (.leaf 1937284632) (.leaf 1891379815)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1846848308) (.leaf 1803636077)) (.branch 40 (.leaf 1761691736) (.leaf 1720966394))) (.branch 43 (.branch 42 (.leaf 1681413518) (.leaf 1642988798)) (.branch 44 (.leaf 1605650026) (.leaf 1569356980))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1534071316) (.branch 47 (.leaf 1499756462) (.leaf 1466377528))) (.branch 50 (.branch 49 (.leaf 1433901211) (.leaf 1402295712)) (.branch 51 (.leaf 1371530659) (.leaf 1341577026)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1312407069) (.leaf 1283994253)) (.branch 55 (.leaf 1256313197) (.leaf 1229339607))) (.branch 58 (.branch 57 (.leaf 1203050225) (.leaf 1177422777)) (.branch 59 (.leaf 1152435920) (.leaf 1128069199))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1104302998) (.branch 62 (.leaf 1081118507) (.leaf 1058497672))) (.branch 65 (.branch 64 (.leaf 1036423165) (.leaf 1014878348)) (.branch 66 (.leaf 993847237) (.leaf 973314472)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 953265290) (.leaf 933685491)) (.branch 70 (.leaf 914561417) (.leaf 895879925))) (.branch 73 (.branch 72 (.leaf 877628361) (.leaf 859794541)) (.branch 74 (.leaf 842366727) (.leaf 825333606))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 808684274) (.branch 77 (.leaf 792408217) (.leaf 776495290))) (.branch 80 (.branch 79 (.leaf 760935704) (.leaf 745720012)) (.branch 81 (.leaf 730839088) (.leaf 716284121)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 702046594) (.leaf 688118277)) (.branch 85 (.leaf 674491212) (.leaf 661157704))) (.branch 88 (.branch 87 (.leaf 648110304) (.leaf 635341809)) (.branch 89 (.leaf 622845243) (.leaf 610613850)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 598641088) (.branch 92 (.leaf 586920619) (.leaf 575446298))) (.branch 95 (.branch 94 (.leaf 564212170) (.leaf 553212459)) (.branch 96 (.leaf 542441564) (.leaf 531894049)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 521564638) (.leaf 511448212)) (.branch 100 (.leaf 501539799) (.leaf 491834569))) (.branch 103 (.branch 102 (.leaf 482327831) (.leaf 473015027)) (.branch 104 (.leaf 463891725) (.leaf 454953619))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 446196520) (.leaf 437616355)) (.branch 108 (.leaf 429209160) (.leaf 420971078))) (.branch 111 (.branch 110 (.leaf 412898358) (.leaf 404987345)) (.branch 112 (.leaf 397234483) (.leaf 389636308)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 382189444) (.leaf 374890607)) (.branch 116 (.leaf 367736591) (.leaf 360724277))) (.branch 119 (.branch 118 (.leaf 353850621) (.leaf 347112656)) (.branch 120 (.leaf 340507491) (.leaf 334032305)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 398).prefactor = (4718255030741271/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 398).cutoff/(generalMeanRows 398).c)).2 =
    (25876755973991/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 398).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 398).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 398).q*(generalMeanRows 398).c/2-2 = (593/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable154.value]
    have hcontinuation : (generalMeanRows 398).q*(generalMeanRows 398).cutoff/2-2 = (16742/7797:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable150.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 398).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 398

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 398).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 398).criticalRate j.val*(generalMeanRows 398).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 398).c*(generalMeanRows 398).criticalPoint j.val)).2-
      (generalMeanRows 398).J/2-(generalMeanRows 398).error (generalMeanGrid j.val)+
      (generalMeanRows 398).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 398).c)).2-
      (generalMeanRows 398).J/2-(generalMeanRows 398).error 4 := by
  have he : (generalMeanRows 398).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 398) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 398)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0398

/-! Kernel-checked entropy margins for general spectral rectangle 399. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0399
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5190926023) (.branch 2 (.leaf 5020339170) (.leaf 4857405780))) (.branch 5 (.branch 4 (.leaf 4701682361) (.leaf 4552757055)) (.branch 6 (.leaf 4410246872) (.leaf 4273795226)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4143069730) (.leaf 4017760208)) (.branch 10 (.leaf 3897576915) (.leaf 3782248924))) (.branch 13 (.branch 12 (.leaf 3671522668) (.leaf 3565160616)) (.branch 14 (.leaf 3462940074) (.leaf 3364652091))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3270100458) (.branch 17 (.leaf 3179100797) (.leaf 3091479726))) (.branch 20 (.branch 19 (.leaf 3007074093) (.leaf 2925730271)) (.branch 21 (.leaf 2847303513) (.leaf 2771657355)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2698663065) (.leaf 2628199139)) (.branch 25 (.leaf 2560150830) (.leaf 2494409714))) (.branch 28 (.branch 27 (.leaf 2430873287) (.leaf 2369444596)) (.branch 29 (.leaf 2310031888) (.leaf 2252548292)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2196911520) (.branch 32 (.leaf 2143043585) (.leaf 2090870548))) (.branch 35 (.branch 34 (.leaf 2040322270) (.leaf 1991332192)) (.branch 36 (.leaf 1943837122) (.leaf 1897777040)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1853094914) (.leaf 1809736526)) (.branch 40 (.leaf 1767650316) (.leaf 1726787229))) (.branch 43 (.branch 42 (.leaf 1687100573) (.leaf 1648545888)) (.branch 44 (.leaf 1611080825) (.leaf 1574665026))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1539260015) (.branch 47 (.leaf 1504829097) (.leaf 1471337265))) (.branch 50 (.branch 49 (.leaf 1438751103) (.leaf 1407038705)) (.branch 51 (.leaf 1376169595) (.leaf 1346114650)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1316846031) (.leaf 1288337115)) (.branch 55 (.leaf 1260562433) (.leaf 1233497610))) (.branch 58 (.branch 57 (.leaf 1207119309) (.leaf 1181405181)) (.branch 59 (.leaf 1156333811) (.leaf 1131884674))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1108038089) (.branch 62 (.leaf 1084775181) (.leaf 1062077835))) (.branch 65 (.branch 64 (.leaf 1039928666) (.leaf 1018310977)) (.branch 66 (.leaf 997208732) (.leaf 976606520)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 956489524) (.leaf 936843501)) (.branch 70 (.leaf 917654744) (.leaf 898910065))) (.branch 73 (.branch 72 (.leaf 880596769) (.leaf 862702630)) (.branch 74 (.leaf 845215869) (.leaf 828125137))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 811419492) (.branch 77 (.leaf 795088384) (.leaf 779121634))) (.branch 80 (.branch 79 (.leaf 763509421) (.leaf 748242265)) (.branch 81 (.leaf 733311009) (.leaf 718706813)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 704421130) (.leaf 690445704)) (.branch 85 (.leaf 676772548) (.leaf 663393941))) (.branch 88 (.branch 87 (.leaf 650302412) (.leaf 637490730)) (.branch 89 (.leaf 624951896) (.leaf 612679133)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 600665875) (.branch 92 (.leaf 588905764) (.leaf 577392634))) (.branch 95 (.branch 94 (.leaf 566120508) (.leaf 555083593)) (.branch 96 (.leaf 544276267) (.leaf 533693077)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 523328729) (.leaf 513178087)) (.branch 100 (.leaf 503236160) (.leaf 493498104))) (.branch 103 (.branch 102 (.leaf 483959211) (.leaf 474614908)) (.branch 104 (.leaf 465460749) (.leaf 456492412))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 447705694) (.leaf 439096507)) (.branch 108 (.leaf 430660876) (.leaf 422394931))) (.branch 111 (.branch 110 (.leaf 414294907) (.leaf 406357136)) (.branch 112 (.leaf 398578052) (.leaf 390954177)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 383482126) (.leaf 376158601)) (.branch 116 (.leaf 368980389) (.leaf 361944357))) (.branch 119 (.branch 118 (.leaf 355047452) (.leaf 348286697)) (.branch 120 (.leaf 341659192) (.leaf 335162105)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 399).prefactor = (4734213612910951/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 399).cutoff/(generalMeanRows 399).c)).2 =
    (25876755973991/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 399).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 399).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 399).q*(generalMeanRows 399).c/2-2 = (593/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable154.value]
    have hcontinuation : (generalMeanRows 399).q*(generalMeanRows 399).cutoff/2-2 = (16742/7797:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable150.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 399).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 399

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 399).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 399).criticalRate j.val*(generalMeanRows 399).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 399).c*(generalMeanRows 399).criticalPoint j.val)).2-
      (generalMeanRows 399).J/2-(generalMeanRows 399).error (generalMeanGrid j.val)+
      (generalMeanRows 399).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 399).c)).2-
      (generalMeanRows 399).J/2-(generalMeanRows 399).error 4 := by
  have he : (generalMeanRows 399).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 399) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 399)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0399

/-! Kernel-checked entropy margins for general spectral rectangle 400. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0400
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5035310267) (.branch 2 (.leaf 4864880892) (.leaf 4702137550))) (.branch 5 (.branch 4 (.leaf 4546636779) (.leaf 4397966642)) (.branch 6 (.leaf 4255743975) (.leaf 4119611932)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3989237785) (.leaf 3864310952)) (.branch 10 (.leaf 3744541220) (.leaf 3629657138))) (.branch 13 (.branch 12 (.leaf 3519404567) (.leaf 3413545364)) (.branch 14 (.leaf 3311856185) (.leaf 3214127397))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3120162082) (.branch 17 (.leaf 3029775132) (.leaf 2942792416))) (.branch 20 (.branch 19 (.leaf 2859050014) (.leaf 2778393524)) (.branch 21 (.leaf 2700677411) (.leaf 2625764419)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2553525019) (.leaf 2483836908)) (.branch 25 (.leaf 2416584541) (.leaf 2351658698))) (.branch 28 (.branch 27 (.leaf 2288956083) (.leaf 2228378955)) (.branch 29 (.leaf 2169834781) (.leaf 2113235918)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2058499314) (.branch 32 (.leaf 2005546228) (.leaf 1954301979))) (.branch 35 (.branch 34 (.leaf 1904695696) (.leaf 1856660101)) (.branch 36 (.leaf 1810131296) (.leaf 1765048568)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1721354204) (.leaf 1678993323)) (.branch 40 (.leaf 1637913713) (.leaf 1598065681))) (.branch 43 (.branch 42 (.leaf 1559401914) (.leaf 1521877347)) (.branch 44 (.leaf 1485449037) (.leaf 1450076048))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1415719344) (.branch 47 (.leaf 1382341685) (.leaf 1349907528))) (.branch 50 (.branch 49 (.leaf 1318382942) (.leaf 1287735519)) (.branch 51 (.leaf 1257934296) (.leaf 1228949676)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1200753363) (.leaf 1173318289)) (.branch 55 (.leaf 1146618555) (.leaf 1120629370))) (.branch 58 (.branch 57 (.leaf 1095326995) (.leaf 1070688690)) (.branch 59 (.leaf 1046692666) (.leaf 1023318034))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1000544764) (.branch 62 (.leaf 978353642) (.leaf 956726229))) (.branch 65 (.branch 64 (.leaf 935644825) (.leaf 915092434)) (.branch 66 (.leaf 895052728) (.leaf 875510017)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 856449218) (.leaf 837855829)) (.branch 70 (.leaf 819715898) (.leaf 802016001))) (.branch 73 (.branch 72 (.leaf 784743214) (.leaf 767885097)) (.branch 74 (.leaf 751429664) (.leaf 735365367))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 719681077) (.branch 77 (.leaf 704366061) (.leaf 689409972))) (.branch 80 (.branch 79 (.leaf 674802823) (.leaf 660534980)) (.branch 81 (.leaf 646597140) (.leaf 632980321)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 619675846) (.leaf 606675331)) (.branch 85 (.leaf 593970675) (.leaf 581554043))) (.branch 88 (.branch 87 (.leaf 569417859) (.leaf 557554794)) (.branch 89 (.leaf 545957759) (.leaf 534619887)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 523534536) (.branch 92 (.leaf 512695269) (.leaf 502095852))) (.branch 95 (.branch 94 (.leaf 491730245) (.leaf 481592595)) (.branch 96 (.leaf 471677226) (.leaf 461978635)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 452491484) (.leaf 443210595)) (.branch 100 (.leaf 434130944) (.leaf 425247653))) (.branch 103 (.branch 102 (.leaf 416555986) (.leaf 408051346)) (.branch 104 (.leaf 399729267) (.leaf 391585410))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 383615559) (.leaf 375815616)) (.branch 108 (.leaf 368181599) (.leaf 360709633))) (.branch 111 (.branch 110 (.leaf 353395954) (.leaf 346236896)) (.branch 112 (.leaf 339228897) (.leaf 332368487)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 325652291) (.leaf 319077024)) (.branch 116 (.leaf 312639486) (.leaf 306336562))) (.branch 119 (.branch 118 (.leaf 300165220) (.leaf 294122503)) (.branch 120 (.leaf 288205532) (.leaf 282411503)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 400).prefactor = (1184091457113829/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 400).cutoff/(generalMeanRows 400).c)).2 =
    (395518068812987/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 400).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 400).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 400).q*(generalMeanRows 400).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 400).q*(generalMeanRows 400).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 400).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 400

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 400).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 400).criticalRate j.val*(generalMeanRows 400).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 400).c*(generalMeanRows 400).criticalPoint j.val)).2-
      (generalMeanRows 400).J/2-(generalMeanRows 400).error (generalMeanGrid j.val)+
      (generalMeanRows 400).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 400).c)).2-
      (generalMeanRows 400).J/2-(generalMeanRows 400).error 4 := by
  have he : (generalMeanRows 400).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 400) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 400)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0400

/-! Kernel-checked entropy margins for general spectral rectangle 401. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0401
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5052478577) (.branch 2 (.leaf 4881468108) (.leaf 4718169879))) (.branch 5 (.branch 4 (.leaf 4562138916) (.leaf 4412961876)) (.branch 6 (.leaf 4270254289) (.leaf 4133658092)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4002839423) (.leaf 3877486643)) (.branch 10 (.leaf 3757308546) (.leaf 3642032757))) (.branch 13 (.branch 12 (.leaf 3531404271) (.leaf 3425184132)) (.branch 14 (.leaf 3323148235) (.leaf 3225086232))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3130800535) (.branch 17 (.leaf 3040105403) (.leaf 2952826112))) (.branch 20 (.branch 19 (.leaf 2868798183) (.leaf 2787866688)) (.branch 21 (.leaf 2709885596) (.leaf 2634717181)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2562231475) (.leaf 2492305757)) (.branch 25 (.leaf 2424824088) (.leaf 2359676874))) (.branch 28 (.branch 27 (.leaf 2296760470) (.leaf 2235976799)) (.branch 29 (.leaf 2177233014) (.leaf 2120441172)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2065517939) (.branch 32 (.leaf 2012384305) (.leaf 1960965334))) (.branch 35 (.branch 34 (.leaf 1911189914) (.leaf 1862990538)) (.branch 36 (.leaf 1816303090) (.leaf 1771066648)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1727223305) (.leaf 1684717991)) (.branch 40 (.leaf 1643498316) (.leaf 1603514419))) (.branch 43 (.branch 42 (.leaf 1564718825) (.leaf 1527066315)) (.branch 44 (.leaf 1490513799) (.leaf 1455020203))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1420546357) (.branch 47 (.leaf 1387054894) (.leaf 1354510150))) (.branch 50 (.branch 49 (.leaf 1322878079) (.leaf 1292126161)) (.branch 51 (.leaf 1262223328) (.leaf 1233139883)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1204847432) (.leaf 1177318816)) (.branch 55 (.leaf 1150528047) (.leaf 1124450249))) (.branch 58 (.branch 57 (.leaf 1099061604) (.leaf 1074339293)) (.branch 59 (.leaf 1050261452) (.leaf 1026807122))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1003956205) (.branch 62 (.leaf 981689420) (.leaf 959988267))) (.branch 65 (.branch 64 (.leaf 938834984) (.leaf 918212518)) (.branch 66 (.leaf 898104485) (.leaf 878495141)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 859369353) (.leaf 840712568)) (.branch 70 (.leaf 822510788) (.leaf 804750541))) (.branch 73 (.branch 72 (.leaf 787418862) (.leaf 770503266)) (.branch 74 (.leaf 753991726) (.leaf 737872657))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 722134889) (.branch 77 (.leaf 706767656) (.leaf 691760573))) (.branch 80 (.branch 79 (.leaf 677103620) (.leaf 662787129)) (.branch 81 (.leaf 648801767) (.leaf 635138520)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 621788682) (.leaf 608743841)) (.branch 85 (.leaf 595995867) (.leaf 583536900))) (.branch 88 (.branch 87 (.leaf 571359336) (.leaf 559455824)) (.branch 89 (.leaf 547819247) (.leaf 536442718)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 525319570) (.branch 92 (.leaf 514443346) (.leaf 503807789))) (.branch 95 (.branch 94 (.leaf 493406840) (.leaf 483234625)) (.branch 96 (.leaf 473285449) (.leaf 463553789)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 454034291) (.leaf 444721759)) (.branch 100 (.leaf 435611150) (.leaf 426697570))) (.branch 103 (.branch 102 (.leaf 417976268) (.leaf 409442631)) (.branch 104 (.leaf 401092177) (.leaf 392920553))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 384923528) (.leaf 377096991)) (.branch 108 (.leaf 369436944) (.leaf 361939503))) (.branch 111 (.branch 110 (.leaf 354600887) (.leaf 347417420)) (.branch 112 (.leaf 340385526) (.leaf 333501725)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 326762630) (.leaf 320164943)) (.branch 116 (.leaf 313705456) (.leaf 307381042))) (.branch 119 (.branch 118 (.leaf 301188658) (.leaf 295125338)) (.branch 120 (.leaf 289188193) (.leaf 283374409)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 401).prefactor = (4752514862522413/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 401).cutoff/(generalMeanRows 401).c)).2 =
    (395518068812987/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 401).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 401).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 401).q*(generalMeanRows 401).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 401).q*(generalMeanRows 401).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 401).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 401

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 401).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 401).criticalRate j.val*(generalMeanRows 401).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 401).c*(generalMeanRows 401).criticalPoint j.val)).2-
      (generalMeanRows 401).J/2-(generalMeanRows 401).error (generalMeanGrid j.val)+
      (generalMeanRows 401).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 401).c)).2-
      (generalMeanRows 401).J/2-(generalMeanRows 401).error 4 := by
  have he : (generalMeanRows 401).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 401) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 401)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0401

/-! Kernel-checked entropy margins for general spectral rectangle 402. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0402
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5001257347) (.branch 2 (.leaf 4829537583) (.leaf 4665591124))) (.branch 5 (.branch 4 (.leaf 4508969816) (.leaf 4359257332)) (.branch 6 (.leaf 4216066399) (.leaf 4079036315)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3947830735) (.leaf 3822135673)) (.branch 10 (.leaf 3701657709) (.leaf 3586122374))) (.branch 13 (.branch 12 (.leaf 3475272680) (.leaf 3368867793)) (.branch 14 (.leaf 3266681826) (.leaf 3168502739))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3074131337) (.branch 17 (.leaf 2983380351) (.leaf 2896073601))) (.branch 20 (.branch 19 (.leaf 2812045226) (.leaf 2731138976)) (.branch 21 (.leaf 2653207562) (.leaf 2578112058)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2505721349) (.leaf 2435911620)) (.branch 25 (.leaf 2368565887) (.leaf 2303573556))) (.branch 28 (.branch 27 (.leaf 2240830024) (.leaf 2180236302)) (.branch 29 (.leaf 2121698666) (.leaf 2065128336)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2010441172) (.branch 32 (.leaf 1957557398) (.leaf 1906401339))) (.branch 35 (.branch 34 (.leaf 1856901178) (.leaf 1808988730)) (.branch 36 (.leaf 1762599229) (.leaf 1717671132)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1674145932) (.leaf 1631967986)) (.branch 40 (.leaf 1591084356) (.leaf 1551444650))) (.branch 43 (.branch 42 (.leaf 1513000888) (.leaf 1475707365)) (.branch 44 (.leaf 1439520523) (.leaf 1404398840))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1370302717) (.branch 47 (.leaf 1337194371) (.leaf 1305037745))) (.branch 50 (.branch 49 (.leaf 1273798410) (.leaf 1243443481)) (.branch 51 (.leaf 1213941539) (.leaf 1185262550)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1157377798) (.leaf 1130259813)) (.branch 55 (.leaf 1103882308) (.leaf 1078220124))) (.branch 58 (.branch 57 (.leaf 1053249166) (.leaf 1028946354)) (.branch 59 (.leaf 1005289571) (.leaf 982257617))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 959830160) (.branch 62 (.leaf 937987699) (.leaf 916711520))) (.branch 65 (.branch 64 (.leaf 895983658) (.leaf 875786862)) (.branch 66 (.leaf 856104562) (.leaf 836920836)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 818220379) (.leaf 799988472)) (.branch 70 (.leaf 782210961) (.leaf 764874225))) (.branch 73 (.branch 72 (.leaf 747965156) (.leaf 731471130)) (.branch 74 (.leaf 715379991) (.leaf 699680028))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 684359954) (.branch 77 (.leaf 669408887) (.leaf 654816336))) (.branch 80 (.branch 79 (.leaf 640572177) (.leaf 626666646)) (.branch 81 (.leaf 613090314) (.leaf 599834082)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 586889158) (.leaf 574247051)) (.branch 85 (.leaf 561899556) (.leaf 549838741))) (.branch 88 (.branch 87 (.leaf 538056936) (.leaf 526546724)) (.branch 89 (.leaf 515300931) (.leaf 504312612)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 493575047) (.branch 92 (.leaf 483081728) (.leaf 472826354))) (.branch 95 (.branch 94 (.leaf 462802820) (.leaf 453005211)) (.branch 96 (.leaf 443427794) (.leaf 434065014)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 424911480) (.leaf 415961968)) (.branch 100 (.leaf 407211407) (.leaf 398654878))) (.branch 103 (.branch 102 (.leaf 390287606) (.leaf 382104957)) (.branch 104 (.leaf 374102430) (.leaf 366275655))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 358620387) (.leaf 351132501)) (.branch 108 (.leaf 343807989) (.leaf 336642954))) (.branch 111 (.branch 110 (.leaf 329633610) (.leaf 322776274)) (.branch 112 (.leaf 316067365) (.leaf 309503399)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 303080987) (.leaf 296796831)) (.branch 116 (.leaf 290647723) (.leaf 284630538))) (.branch 119 (.branch 118 (.leaf 278742236) (.leaf 272979855)) (.branch 120 (.leaf 267340512) (.leaf 261821397)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 402).prefactor = (4784978302826323/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 402).cutoff/(generalMeanRows 402).c)).2 =
    (38782572318983/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 402).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 402).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 402).q*(generalMeanRows 402).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 402).q*(generalMeanRows 402).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 402).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 402

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 402).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 402).criticalRate j.val*(generalMeanRows 402).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 402).c*(generalMeanRows 402).criticalPoint j.val)).2-
      (generalMeanRows 402).J/2-(generalMeanRows 402).error (generalMeanGrid j.val)+
      (generalMeanRows 402).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 402).c)).2-
      (generalMeanRows 402).J/2-(generalMeanRows 402).error 4 := by
  have he : (generalMeanRows 402).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 402) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 402)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0402

/-! Kernel-checked entropy margins for general spectral rectangle 403. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0403
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5177293925) (.branch 2 (.leaf 5007178457) (.leaf 4844666541))) (.branch 5 (.branch 4 (.leaf 4689319688) (.leaf 4540730592)) (.branch 6 (.leaf 4398520406) (.leaf 4262336318)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4131849370) (.leaf 4006752510)) (.branch 10 (.leaf 3886758830) (.leaf 3771599978))) (.branch 13 (.branch 12 (.leaf 3661024728) (.leaf 3554797673)) (.branch 14 (.leaf 3452698044) (.leaf 3354518631))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3260064801) (.branch 17 (.leaf 3169153603) (.leaf 3081612940))) (.branch 20 (.branch 19 (.leaf 2997280817) (.leaf 2916004651)) (.branch 21 (.leaf 2837640630) (.leaf 2762053129)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2689114168) (.leaf 2618702911)) (.branch 25 (.leaf 2550705209) (.leaf 2485013164))) (.branch 28 (.branch 27 (.leaf 2421524742) (.leaf 2360143399)) (.branch 29 (.leaf 2300777745) (.leaf 2243341223)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2187751816) (.branch 32 (.leaf 2133931775) (.leaf 2081807358))) (.branch 35 (.branch 34 (.leaf 2031308598) (.leaf 1982369076)) (.branch 36 (.leaf 1934925717) (.leaf 1888918592)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1844290743) (.leaf 1800988006)) (.branch 40 (.leaf 1758958859) (.leaf 1718154268))) (.branch 43 (.branch 42 (.leaf 1678527554) (.leaf 1640034255)) (.branch 44 (.leaf 1602632009) (.leaf 1566280437))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1530941037) (.branch 47 (.leaf 1496577078) (.leaf 1463153512))) (.branch 50 (.branch 49 (.leaf 1430636876) (.leaf 1398995214)) (.branch 51 (.leaf 1368197998) (.leaf 1338216046)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1309021462) (.leaf 1280587562)) (.branch 55 (.leaf 1252888814) (.leaf 1225900780))) (.branch 58 (.branch 57 (.leaf 1199600061) (.leaf 1173964242)) (.branch 59 (.leaf 1148971846) (.leaf 1124602283))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1100835811) (.branch 62 (.leaf 1077653490) (.leaf 1055037148))) (.branch 65 (.branch 64 (.leaf 1032969336) (.leaf 1011433302)) (.branch 66 (.leaf 990412949) (.leaf 969892811)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 949858019) (.leaf 930294274)) (.branch 70 (.leaf 911187819) (.leaf 892525417))) (.branch 73 (.branch 72 (.leaf 874294324) (.leaf 856482269)) (.branch 74 (.leaf 839077429) (.leaf 822068411))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 805444234) (.branch 77 (.leaf 789194308) (.leaf 773308417))) (.branch 80 (.branch 79 (.leaf 757776705) (.leaf 742589656)) (.branch 81 (.leaf 727738085) (.leaf 713213117)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 699006180) (.leaf 685108988)) (.branch 85 (.leaf 671513530) (.leaf 658212061))) (.branch 88 (.branch 87 (.leaf 645197085) (.leaf 632461352)) (.branch 89 (.leaf 619997843) (.leaf 607799762)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 595860526) (.branch 92 (.leaf 584173761) (.leaf 572733285))) (.branch 95 (.branch 94 (.leaf 561533111) (.leaf 550567430)) (.branch 96 (.leaf 539830610) (.leaf 529317188)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 519021861) (.leaf 508939484)) (.branch 100 (.leaf 499065061) (.leaf 489393739))) (.branch 103 (.branch 102 (.leaf 479920806) (.leaf 470641683)) (.branch 104 (.leaf 461551921) (.leaf 452647196))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 443923301) (.leaf 435376147)) (.branch 108 (.leaf 427001758) (.leaf 418796263))) (.branch 111 (.branch 110 (.leaf 410755897) (.leaf 402876995)) (.branch 112 (.leaf 395155989) (.leaf 387589404)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 380173859) (.leaf 372906057)) (.branch 116 (.leaf 365782787) (.leaf 358800921))) (.branch 119 (.branch 118 (.leaf 351957411) (.leaf 345249283)) (.branch 120 (.leaf 338673640) (.leaf 332227657)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 403).prefactor = (4689977528016961/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 403).cutoff/(generalMeanRows 403).c)).2 =
    (102036431420197/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 403).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 403).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 403).q*(generalMeanRows 403).c/2-2 = (593/800:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable154.value]
    have hcontinuation : (generalMeanRows 403).q*(generalMeanRows 403).cutoff/2-2 = (16650/7843:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable158.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 403).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 403

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 403).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 403).criticalRate j.val*(generalMeanRows 403).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 403).c*(generalMeanRows 403).criticalPoint j.val)).2-
      (generalMeanRows 403).J/2-(generalMeanRows 403).error (generalMeanGrid j.val)+
      (generalMeanRows 403).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 403).c)).2-
      (generalMeanRows 403).J/2-(generalMeanRows 403).error 4 := by
  have he : (generalMeanRows 403).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 403) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 403)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0403

/-! Kernel-checked entropy margins for general spectral rectangle 404. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0404
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5106825701) (.branch 2 (.leaf 4936508489) (.leaf 4773830148))) (.branch 5 (.branch 4 (.leaf 4618350592) (.leaf 4469661005)) (.branch 6 (.leaf 4327381110) (.leaf 4191156731)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4060657618) (.leaf 3935575483)) (.branch 10 (.leaf 3815622242) (.leaf 3700528421))) (.branch 13 (.branch 12 (.leaf 3590041718) (.leaf 3483925699)) (.branch 14 (.leaf 3381958609) (.leaf 3283932295))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3189651220) (.branch 17 (.leaf 3098931561) (.leaf 3011600386))) (.branch 20 (.branch 19 (.leaf 2927494898) (.leaf 2846461739)) (.branch 21 (.leaf 2768356356) (.leaf 2693042406)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2620391219) (.leaf 2550281295)) (.branch 25 (.leaf 2482597843) (.leaf 2417232348))) (.branch 28 (.branch 27 (.leaf 2354082179) (.leaf 2293050216)) (.branch 29 (.leaf 2234044514) (.leaf 2176977980)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2121768079) (.branch 32 (.leaf 2068336561) (.leaf 2016609203))) (.branch 35 (.branch 34 (.leaf 1966515570) (.leaf 1917988793)) (.branch 36 (.leaf 1870965361) (.leaf 1825384926)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1781190121) (.leaf 1738326392)) (.branch 40 (.leaf 1696741835) (.leaf 1656387052))) (.branch 43 (.branch 42 (.leaf 1617215007) (.leaf 1579180899)) (.branch 44 (.leaf 1542242033) (.leaf 1506357712))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1471489124) (.branch 47 (.leaf 1437599243) (.leaf 1404652730))) (.branch 50 (.branch 49 (.leaf 1372615846) (.leaf 1341456369)) (.branch 51 (.leaf 1311143507) (.leaf 1281647833)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1252941208) (.leaf 1224996715)) (.branch 55 (.leaf 1197788599) (.leaf 1171292205))) (.branch 58 (.branch 57 (.leaf 1145483926) (.leaf 1120341145)) (.branch 59 (.leaf 1095842191) (.leaf 1071966290))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1048693518) (.branch 62 (.leaf 1026004764) (.leaf 1003881687))) (.branch 65 (.branch 64 (.leaf 982306680) (.leaf 961262835)) (.branch 66 (.leaf 940733909) (.leaf 920704292)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 901158979) (.leaf 882083539)) (.branch 70 (.leaf 863464090) (.leaf 845287273))) (.branch 73 (.branch 72 (.leaf 827540229) (.leaf 810210575)) (.branch 74 (.leaf 793286382) (.leaf 776756156))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 760608817) (.branch 77 (.leaf 744833683) (.leaf 729420448))) (.branch 80 (.branch 79 (.leaf 714359171) (.leaf 699640255)) (.branch 81 (.leaf 685254438) (.leaf 671192772)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 657446614) (.leaf 644007611)) (.branch 85 (.leaf 630867690) (.leaf 618019044))) (.branch 88 (.branch 87 (.leaf 605454123) (.leaf 593165621)) (.branch 89 (.leaf 581146469) (.leaf 569389822)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 557889054) (.branch 92 (.leaf 546637745) (.leaf 535629677))) (.branch 95 (.branch 94 (.leaf 524858823) (.leaf 514319340)) (.branch 96 (.leaf 504005564) (.leaf 493912000)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 484033319) (.leaf 474364349)) (.branch 100 (.leaf 464900070) (.leaf 455635607))) (.branch 103 (.branch 102 (.leaf 446566229) (.leaf 437687340)) (.branch 104 (.leaf 428994473) (.leaf 420483288))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 412149569) (.leaf 403989214)) (.branch 108 (.leaf 395998237) (.leaf 388172760))) (.branch 111 (.branch 110 (.leaf 380509011) (.leaf 373003320)) (.branch 112 (.leaf 365652115) (.leaf 358451920)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 351399350) (.leaf 344491110)) (.branch 116 (.leaf 337723991) (.leaf 331094866))) (.branch 119 (.branch 118 (.leaf 324600689) (.leaf 318238494)) (.branch 120 (.leaf 312005388) (.leaf 305898552)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 404).prefactor = (2353049031288557/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 404).cutoff/(generalMeanRows 404).c)).2 =
    (100083296485999/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 404).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 404).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 404).q*(generalMeanRows 404).c/2-2 = (3051/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable153.value]
    have hcontinuation : (generalMeanRows 404).q*(generalMeanRows 404).cutoff/2-2 = (16650/7843:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable158.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 404).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 404

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 404).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 404).criticalRate j.val*(generalMeanRows 404).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 404).c*(generalMeanRows 404).criticalPoint j.val)).2-
      (generalMeanRows 404).J/2-(generalMeanRows 404).error (generalMeanGrid j.val)+
      (generalMeanRows 404).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 404).c)).2-
      (generalMeanRows 404).J/2-(generalMeanRows 404).error 4 := by
  have he : (generalMeanRows 404).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 404) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 404)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0404

/-! Kernel-checked entropy margins for general spectral rectangle 405. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0405
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5039975839) (.branch 2 (.leaf 4869454863) (.leaf 4706594909))) (.branch 5 (.branch 4 (.leaf 4550956042) (.leaf 4402129508)) (.branch 6 (.leaf 4259735021) (.leaf 4123418329)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3992849039) (.leaf 3867718670)) (.branch 10 (.leaf 3747738895) (.leaf 3632639952))) (.branch 13 (.branch 12 (.leaf 3522169214) (.leaf 3416089885)) (.branch 14 (.leaf 3314179821) (.leaf 3216230453))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3122045804) (.branch 17 (.leaf 3031441593) (.leaf 2944244414))) (.branch 20 (.branch 19 (.leaf 2860290981) (.leaf 2779427440)) (.branch 21 (.leaf 2701508726) (.leaf 2626397985)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2553966026) (.leaf 2484090829)) (.branch 25 (.leaf 2416657078) (.leaf 2351555735))) (.branch 28 (.branch 27 (.leaf 2288683646) (.leaf 2227943175)) (.branch 29 (.leaf 2169241857) (.leaf 2112492088)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2057610829) (.branch 32 (.leaf 2004519328) (.leaf 1953142869))) (.branch 35 (.branch 34 (.leaf 1903410531) (.leaf 1855254967)) (.branch 36 (.leaf 1808612195) (.leaf 1763421406)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1719624780) (.leaf 1677167320)) (.branch 40 (.leaf 1635996689) (.leaf 1596063065))) (.branch 43 (.branch 42 (.leaf 1557318997) (.leaf 1519719278)) (.branch 44 (.leaf 1483220821) (.leaf 1447782544))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1413365261) (.branch 47 (.leaf 1379931581) (.leaf 1347445811))) (.branch 50 (.branch 49 (.leaf 1315873869) (.leaf 1285183196)) (.branch 51 (.leaf 1255342679) (.leaf 1226322575)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1198094438) (.leaf 1170631058)) (.branch 55 (.leaf 1143906392) (.leaf 1117895511))) (.branch 58 (.branch 57 (.leaf 1092574537) (.leaf 1067920596)) (.branch 59 (.leaf 1043911768) (.leaf 1020527035))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 997746242) (.branch 62 (.leaf 975550054) (.leaf 953919912))) (.branch 65 (.branch 64 (.leaf 932838001) (.leaf 912287213)) (.branch 66 (.leaf 892251111) (.leaf 872713901)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 853660397) (.leaf 835075999)) (.branch 70 (.leaf 816946660) (.leaf 799258863))) (.branch 73 (.branch 72 (.leaf 781999598) (.leaf 765156336)) (.branch 74 (.leaf 748717011) (.leaf 732669996))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 717004084) (.branch 77 (.leaf 701708471) (.leaf 686772737))) (.branch 80 (.branch 79 (.leaf 672186830) (.leaf 657941050)) (.branch 81 (.leaf 644026033) (.leaf 630432736)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 617152426) (.leaf 604176666)) (.branch 85 (.leaf 591497301) (.leaf 579106447))) (.branch 88 (.branch 87 (.leaf 566996481) (.leaf 555160029)) (.branch 89 (.leaf 543589956) (.leaf 532279359)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 521221553) (.branch 92 (.leaf 510410065) (.leaf 499838627))) (.branch 95 (.branch 94 (.leaf 489501165) (.leaf 479391792)) (.branch 96 (.leaf 469504804) (.leaf 459834669)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 450376022) (.leaf 441123660)) (.branch 100 (.leaf 432072533) (.leaf 423217742))) (.branch 103 (.branch 102 (.leaf 414554529) (.leaf 406078277)) (.branch 104 (.leaf 397784500) (.leaf 389668842))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 381727070) (.leaf 373955071)) (.branch 108 (.leaf 366348846) (.leaf 358904510))) (.branch 111 (.branch 110 (.leaf 351618282) (.leaf 344486488)) (.branch 112 (.leaf 337505552) (.leaf 330671995)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 323982432) (.leaf 317433569)) (.branch 116 (.leaf 311022200) (.leaf 304745200))) (.branch 119 (.branch 118 (.leaf 298599531) (.leaf 292582230)) (.branch 120 (.leaf 286690413) (.leaf 280921270)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 405).prefactor = (94158965879761/20000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 405).cutoff/(generalMeanRows 405).c)).2 =
    (389652949360589/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 405).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 405).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 405).q*(generalMeanRows 405).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 405).q*(generalMeanRows 405).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable151.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 405).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 405

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 405).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 405).criticalRate j.val*(generalMeanRows 405).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 405).c*(generalMeanRows 405).criticalPoint j.val)).2-
      (generalMeanRows 405).J/2-(generalMeanRows 405).error (generalMeanGrid j.val)+
      (generalMeanRows 405).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 405).c)).2-
      (generalMeanRows 405).J/2-(generalMeanRows 405).error 4 := by
  have he : (generalMeanRows 405).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 405) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 405)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0405

/-! Kernel-checked entropy margins for general spectral rectangle 406. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0406
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5057440649) (.branch 2 (.leaf 4886328774) (.leaf 4722904469))) (.branch 5 (.branch 4 (.leaf 4566726273) (.leaf 4417384017)) (.branch 6 (.leaf 4274496097) (.leaf 4137707032)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4006685286) (.leaf 3881121309)) (.branch 10 (.leaf 3760725773) (.leaf 3645227982))) (.branch 13 (.branch 12 (.leaf 3534374434) (.leaf 3427927513)) (.branch 14 (.leaf 3325664305) (.leaf 3227375517))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3132864494) (.branch 17 (.leaf 3041946317) (.leaf 2954446977))) (.branch 20 (.branch 19 (.leaf 2870202624) (.leaf 2789058869)) (.branch 21 (.leaf 2710870147) (.leaf 2635499128)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2562816174) (.leaf 2492698842)) (.branch 25 (.leaf 2425031415) (.leaf 2359704479))) (.branch 28 (.branch 27 (.leaf 2296614523) (.leaf 2235663570)) (.branch 29 (.leaf 2176758837) (.leaf 2119812416)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2064740979) (.branch 32 (.leaf 2011465502) (.leaf 1959911011))) (.branch 35 (.branch 34 (.leaf 1910006337) (.leaf 1861683902)) (.branch 36 (.leaf 1814879500) (.leaf 1769532113)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1725583721) (.leaf 1682979135)) (.branch 40 (.leaf 1641665838) (.leaf 1601593833))) (.branch 43 (.branch 42 (.leaf 1562715507) (.leaf 1524985495)) (.branch 44 (.leaf 1488360562) (.leaf 1452799483))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1418262935) (.branch 47 (.leaf 1384713398) (.leaf 1352115057))) (.branch 50 (.branch 49 (.leaf 1320433710) (.leaf 1289636686)) (.branch 51 (.leaf 1259692764) (.leaf 1230572097)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1202246143) (.leaf 1174687595)) (.branch 55 (.leaf 1147870322) (.leaf 1121769306))) (.branch 58 (.branch 57 (.leaf 1096360588) (.leaf 1071621215)) (.branch 59 (.leaf 1047529190) (.leaf 1024063423))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1001203689) (.branch 62 (.leaf 978930585) (.leaf 957225489))) (.branch 65 (.branch 64 (.leaf 936070524) (.leaf 915448522)) (.branch 66 (.leaf 895342990) (.leaf 875738079)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 856618550) (.leaf 837969752)) (.branch 70 (.leaf 819777590) (.leaf 802028500))) (.branch 73 (.branch 72 (.leaf 784709427) (.leaf 767807799)) (.branch 74 (.leaf 751311508) (.leaf 735208885))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 719488687) (.branch 77 (.leaf 704140071) (.leaf 689152581))) (.branch 80 (.branch 79 (.leaf 674516130) (.leaf 660220985)) (.branch 81 (.leaf 646257748) (.leaf 632617347)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 619291018) (.leaf 606270294)) (.branch 85 (.leaf 593546991) (.leaf 581113199))) (.branch 88 (.branch 87 (.leaf 568961269) (.leaf 557083801)) (.branch 89 (.leaf 545473635) (.leaf 534123844)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 523027720) (.branch 92 (.leaf 512178767) (.leaf 501570696))) (.branch 95 (.branch 94 (.leaf 491197412) (.leaf 481053008)) (.branch 96 (.leaf 471131759) (.leaf 461428114)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 451936691) (.leaf 442652267)) (.branch 100 (.leaf 433569775) (.leaf 424684300))) (.branch 103 (.branch 102 (.leaf 415991067) (.leaf 407485442)) (.branch 104 (.leaf 399162925) (.leaf 391019144))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 383049852) (.leaf 375250921)) (.branch 108 (.leaf 367618339) (.leaf 360148206))) (.branch 111 (.branch 110 (.leaf 352836730) (.leaf 345680222)) (.branch 112 (.leaf 338675095) (.leaf 331817858)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 325105114) (.leaf 318533558)) (.branch 116 (.leaf 312099971) (.leaf 305801221))) (.branch 119 (.branch 118 (.leaf 299634255) (.leaf 293596103)) (.branch 120 (.leaf 287683869) (.leaf 281894734)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 406).prefactor = (36908301122203/7812500000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 406).cutoff/(generalMeanRows 406).c)).2 =
    (389652949360589/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 406).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 406).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 406).q*(generalMeanRows 406).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 406).q*(generalMeanRows 406).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable151.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 406).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 406

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 406).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 406).criticalRate j.val*(generalMeanRows 406).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 406).c*(generalMeanRows 406).criticalPoint j.val)).2-
      (generalMeanRows 406).J/2-(generalMeanRows 406).error (generalMeanGrid j.val)+
      (generalMeanRows 406).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 406).c)).2-
      (generalMeanRows 406).J/2-(generalMeanRows 406).error 4 := by
  have he : (generalMeanRows 406).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 406) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 406)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0406

/-! Kernel-checked entropy margins for general spectral rectangle 407. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0407
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5037776228) (.branch 2 (.leaf 4867294116) (.leaf 4704485881))) (.branch 5 (.branch 4 (.leaf 4548909810) (.leaf 4400155543)) (.branch 6 (.leaf 4257841340) (.leaf 4121611639)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3991134867) (.leaf 3866101481)) (.branch 10 (.leaf 3746222196) (.leaf 3631226396))) (.branch 13 (.branch 12 (.leaf 3520860685) (.leaf 3414887584)) (.branch 14 (.leaf 3313084337) (.leaf 3215241834))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3121163618) (.branch 17 (.leaf 3030664984) (.leaf 2943572155))) (.branch 20 (.branch 19 (.leaf 2859721519) (.leaf 2778958940)) (.branch 21 (.leaf 2701139111) (.leaf 2626124967)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2553787144) (.leaf 2484003471)) (.branch 25 (.leaf 2416658511) (.leaf 2351643129))) (.branch 28 (.branch 27 (.leaf 2288854094) (.leaf 2228193712)) (.branch 29 (.leaf 2169569479) (.leaf 2112893765)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2058083519) (.branch 32 (.leaf 2005059992) (.leaf 1953748478))) (.branch 35 (.branch 34 (.leaf 1904078079) (.leaf 1855981477)) (.branch 36 (.leaf 1809394730) (.leaf 1764257071)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1720510732) (.leaf 1678100768)) (.branch 40 (.leaf 1636974904) (.leaf 1597083378))) (.branch 43 (.branch 42 (.leaf 1558378806) (.leaf 1520816049)) (.branch 44 (.leaf 1484352089) (.leaf 1448945915))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1414558414) (.branch 47 (.leaf 1381152268) (.leaf 1348691857))) (.branch 50 (.branch 49 (.leaf 1317143172) (.leaf 1286473729)) (.branch 51 (.leaf 1256652488) (.leaf 1227649776)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1199437222) (.leaf 1171987685)) (.branch 55 (.leaf 1145275193) (.leaf 1119274885))) (.branch 58 (.branch 57 (.leaf 1093962950) (.leaf 1069316582)) (.branch 59 (.leaf 1045313923) (.leaf 1021934020))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 999156780) (.branch 62 (.leaf 976962926) (.leaf 955333960))) (.branch 65 (.branch 64 (.leaf 934252123) (.leaf 913700362)) (.branch 66 (.leaf 893662295) (.leaf 874122178)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 855064877) (.leaf 836475839)) (.branch 70 (.leaf 818341065) (.leaf 800647085))) (.branch 73 (.branch 72 (.leaf 783380930) (.leaf 766530117)) (.branch 74 (.leaf 750082617) (.leaf 734026844))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 718351629) (.branch 77 (.leaf 703046204) (.leaf 688100185))) (.branch 80 (.branch 79 (.leaf 673503552) (.leaf 659246637)) (.branch 81 (.leaf 645320107) (.leaf 631714950)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 618422461) (.leaf 605434228)) (.branch 85 (.leaf 592742122) (.leaf 580338286))) (.branch 88 (.branch 87 (.leaf 568215119) (.leaf 556365271)) (.branch 89 (.leaf 544781627) (.leaf 533457304)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 522385637) (.branch 92 (.leaf 511560173) (.leaf 500974659))) (.branch 95 (.branch 94 (.leaf 490623038) (.leaf 480499442)) (.branch 96 (.leaf 470598179) (.leaf 460913732)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 451440749) (.leaf 442174041)) (.branch 100 (.leaf 433108569) (.leaf 424239446))) (.branch 103 (.branch 102 (.leaf 415561925) (.leaf 407071397)) (.branch 104 (.leaf 398763389) (.leaf 390633551))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 382677659) (.leaf 374891609)) (.branch 108 (.leaf 367271409) (.leaf 359813179))) (.branch 111 (.branch 110 (.leaf 352513147) (.leaf 345367643)) (.branch 112 (.leaf 338373098) (.leaf 331526037)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 324823082) (.leaf 318260940)) (.branch 116 (.leaf 311836411) (.leaf 305546374))) (.branch 119 (.branch 118 (.leaf 299387794) (.leaf 293357710)) (.branch 120 (.leaf 287453243) (.leaf 281671584)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 407).prefactor = (236113700356647/50000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 407).cutoff/(generalMeanRows 407).c)).2 =
    (392581209139677/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 407).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 407).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 407).q*(generalMeanRows 407).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 407).q*(generalMeanRows 407).cutoff/2-2 = (16650/7843:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable158.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 407).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 407

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 407).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 407).criticalRate j.val*(generalMeanRows 407).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 407).c*(generalMeanRows 407).criticalPoint j.val)).2-
      (generalMeanRows 407).J/2-(generalMeanRows 407).error (generalMeanGrid j.val)+
      (generalMeanRows 407).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 407).c)).2-
      (generalMeanRows 407).J/2-(generalMeanRows 407).error 4 := by
  have he : (generalMeanRows 407).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 407) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 407)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0407

/-! Kernel-checked entropy margins for general spectral rectangle 408. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0408
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4970115106) (.branch 2 (.leaf 4799503534) (.leaf 4636600502))) (.branch 5 (.branch 4 (.leaf 4480962635) (.leaf 4332177999)) (.branch 6 (.leaf 4189863366) (.leaf 4053661757)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3923240255) (.leaf 3798288036)) (.branch 10 (.leaf 3678514597) (.leaf 3563648158))) (.branch 13 (.branch 12 (.leaf 3453434213) (.leaf 3347634221)) (.branch 14 (.leaf 3246024413) (.leaf 3148394705))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3054547711) (.branch 17 (.leaf 2964297833) (.leaf 2877470437))) (.branch 20 (.branch 19 (.leaf 2793901093) (.leaf 2713434874)) (.branch 21 (.leaf 2635925715) (.leaf 2561235825)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2489235138) (.leaf 2419800811)) (.branch 25 (.leaf 2352816760) (.leaf 2288173225))) (.branch 28 (.branch 27 (.leaf 2225766377) (.leaf 2165497943)) (.branch 29 (.leaf 2107274862) (.leaf 2051008970)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1996616700) (.branch 32 (.leaf 1944018805) (.leaf 1893140100))) (.branch 35 (.branch 34 (.leaf 1843909226) (.leaf 1796258421)) (.branch 36 (.leaf 1750123312) (.leaf 1705442722)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1662158483) (.leaf 1620215270)) (.branch 40 (.leaf 1579560435) (.leaf 1540143861))) (.branch 43 (.branch 42 (.leaf 1501917823) (.leaf 1464836850)) (.branch 44 (.leaf 1428857607) (.leaf 1393938778))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1360040952) (.branch 47 (.leaf 1327126530) (.leaf 1295159617))) (.branch 50 (.branch 49 (.leaf 1264105943) (.leaf 1233932770)) (.branch 51 (.leaf 1204608814) (.leaf 1176104169)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1148390239) (.leaf 1121439667)) (.branch 55 (.leaf 1095226273) (.leaf 1069724995))) (.branch 58 (.branch 57 (.leaf 1044911834) (.leaf 1020763797)) (.branch 59 (.leaf 997258851) (.leaf 974375874))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 952094609) (.branch 62 (.leaf 930395626) (.leaf 909260277))) (.branch 65 (.branch 64 (.leaf 888670660) (.leaf 868609586)) (.branch 66 (.leaf 849060542) (.leaf 830007660)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 811435687) (.leaf 793329957)) (.branch 70 (.leaf 775676361) (.leaf 758461326))) (.branch 73 (.branch 72 (.leaf 741671786) (.leaf 725295162)) (.branch 74 (.leaf 709319338) (.leaf 693732642))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 678523825) (.branch 77 (.leaf 663682044) (.leaf 649196841))) (.branch 80 (.branch 79 (.leaf 635058129) (.leaf 621256176)) (.branch 81 (.leaf 607781587) (.leaf 594625294)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 581778536) (.leaf 569232854)) (.branch 85 (.leaf 556980070) (.leaf 545012281))) (.branch 88 (.branch 87 (.leaf 533321848) (.leaf 521901380)) (.branch 89 (.leaf 510743728) (.leaf 499841976)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 489189429) (.branch 92 (.leaf 478779605) (.leaf 468606227))) (.branch 95 (.branch 94 (.leaf 458663216) (.leaf 448944680)) (.branch 96 (.leaf 439444911) (.leaf 430158375)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 421079706) (.leaf 412203702)) (.branch 100 (.leaf 403525314) (.leaf 395039644))) (.branch 103 (.branch 102 (.leaf 386741941) (.leaf 378627591)) (.branch 104 (.leaf 370692113) (.leaf 362931159))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 355340504) (.leaf 347916042)) (.branch 108 (.leaf 340653785) (.leaf 333549857))) (.branch 111 (.branch 110 (.leaf 326600490) (.leaf 319802020)) (.branch 112 (.leaf 313150885) (.leaf 306643619)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300276851) (.leaf 294047302)) (.branch 116 (.leaf 287951781) (.leaf 281987180))) (.branch 119 (.branch 118 (.leaf 276150475) (.leaf 270438724)) (.branch 120 (.leaf 264849058) (.leaf 259378685)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 408).prefactor = (4738505552141363/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 408).cutoff/(generalMeanRows 408).c)).2 =
    (96222215879131/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 408).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 408).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 408).q*(generalMeanRows 408).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 408).q*(generalMeanRows 408).cutoff/2-2 = (16650/7843:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable158.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 408).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 408

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 408).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 408).criticalRate j.val*(generalMeanRows 408).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 408).c*(generalMeanRows 408).criticalPoint j.val)).2-
      (generalMeanRows 408).J/2-(generalMeanRows 408).error (generalMeanGrid j.val)+
      (generalMeanRows 408).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 408).c)).2-
      (generalMeanRows 408).J/2-(generalMeanRows 408).error 4 := by
  have he : (generalMeanRows 408).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 408) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 408)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0408

/-! Kernel-checked entropy margins for general spectral rectangle 409. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0409
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4989874066) (.branch 2 (.leaf 4818628109) (.leaf 4655104635))) (.branch 5 (.branch 4 (.leaf 4498860504) (.leaf 4349483963)) (.branch 6 (.leaf 4206591901) (.leaf 4069827410)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3938857599) (.leaf 3813371625)) (.branch 10 (.leaf 3693078933) (.leaf 3577707654))) (.branch 13 (.branch 12 (.leaf 3467003165) (.leaf 3360726782)) (.branch 14 (.leaf 3258654568) (.leaf 3160576250))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3066294237) (.branch 17 (.leaf 2975622710) (.leaf 2888386801))) (.branch 20 (.branch 19 (.leaf 2804421831) (.leaf 2723572618)) (.branch 21 (.leaf 2645692834) (.leaf 2570644416)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2498297023) (.leaf 2428527534)) (.branch 25 (.leaf 2361219580) (.leaf 2296263122))) (.branch 28 (.branch 27 (.leaf 2233554044) (.leaf 2172993788)) (.branch 29 (.leaf 2114489013) (.leaf 2057951273)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2003296719) (.branch 32 (.leaf 1950445830) (.leaf 1899323148))) (.branch 35 (.branch 34 (.leaf 1849857043) (.leaf 1801979488)) (.branch 36 (.leaf 1755625849) (.leaf 1710734690)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1667247594) (.leaf 1625108987)) (.branch 40 (.leaf 1584265979) (.leaf 1544668218))) (.branch 43 (.branch 42 (.leaf 1506267746) (.leaf 1469018867)) (.branch 44 (.leaf 1432878025) (.leaf 1397803690))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1363756242) (.branch 47 (.leaf 1330697876) (.leaf 1298592502))) (.branch 50 (.branch 49 (.leaf 1267405656) (.leaf 1237104412)) (.branch 51 (.leaf 1207657305) (.leaf 1179034254)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1151206489) (.leaf 1124146489)) (.branch 55 (.leaf 1097827913) (.leaf 1072225544))) (.branch 58 (.branch 57 (.leaf 1047315229) (.leaf 1023073832)) (.branch 59 (.leaf 999479179) (.leaf 976510009))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 954145935) (.branch 62 (.leaf 932367398) (.leaf 911155627))) (.branch 65 (.branch 64 (.leaf 890492601) (.leaf 870361017)) (.branch 66 (.leaf 850744249) (.leaf 831626324)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 812991884) (.leaf 794826164)) (.branch 70 (.leaf 777114958) (.leaf 759844602))) (.branch 73 (.branch 72 (.leaf 743001939) (.leaf 726574305)) (.branch 74 (.leaf 710549501) (.leaf 694915775))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 679661801) (.branch 77 (.leaf 664776662) (.leaf 650249828))) (.branch 80 (.branch 79 (.leaf 636071146) (.leaf 622230814)) (.branch 81 (.leaf 608719378) (.leaf 595527705)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 582646978) (.leaf 570068680)) (.branch 85 (.leaf 557784579) (.leaf 545786721))) (.branch 88 (.branch 87 (.leaf 534067415) (.leaf 522619222)) (.branch 89 (.leaf 511434949) (.leaf 500507633)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 489830537) (.branch 92 (.leaf 479397138) (.leaf 469201120))) (.branch 95 (.branch 94 (.leaf 459236365) (.leaf 449496945)) (.branch 96 (.leaf 439977118) (.leaf 430671316)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 421574141) (.leaf 412680358)) (.branch 100 (.leaf 403984891) (.leaf 395482814))) (.branch 103 (.branch 102 (.leaf 387169346) (.leaf 379039847)) (.branch 104 (.leaf 371089814) (.leaf 363314872))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 355710773) (.leaf 348273390)) (.branch 108 (.leaf 340998713) (.leaf 333882847))) (.branch 111 (.branch 110 (.leaf 326922002) (.leaf 320112497)) (.branch 112 (.leaf 313450751) (.leaf 306933281)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 300556700) (.leaf 294317713)) (.branch 116 (.leaf 288213112) (.leaf 282239777))) (.branch 119 (.branch 118 (.leaf 276394669) (.leaf 270674832)) (.branch 120 (.leaf 265077385) (.leaf 259599523)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 409).prefactor = (296289582897489/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 409).cutoff/(generalMeanRows 409).c)).2 =
    (76392120747487/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 409).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 409).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 409).q*(generalMeanRows 409).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 409).q*(generalMeanRows 409).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable151.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 409).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 409

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 409).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 409).criticalRate j.val*(generalMeanRows 409).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 409).c*(generalMeanRows 409).criticalPoint j.val)).2-
      (generalMeanRows 409).J/2-(generalMeanRows 409).error (generalMeanGrid j.val)+
      (generalMeanRows 409).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 409).c)).2-
      (generalMeanRows 409).J/2-(generalMeanRows 409).error 4 := by
  have he : (generalMeanRows 409).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 409) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 409)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0409

/-! Kernel-checked entropy margins for general spectral rectangle 410. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0410
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4923663302) (.branch 2 (.leaf 4752317344) (.leaf 4588728409))) (.branch 5 (.branch 4 (.leaf 4432451649) (.leaf 4283073692)) (.branch 6 (.leaf 4140209898) (.leaf 4003501906)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3872615444) (.leaf 3747238359)) (.branch 10 (.leaf 3627078846) (.leaf 3511863845))) (.branch 13 (.branch 12 (.leaf 3401337599) (.leaf 3295260338)) (.branch 14 (.leaf 3193407090) (.leaf 3095566592))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3001540303) (.branch 17 (.leaf 2911141498) (.leaf 2824194437))) (.branch 20 (.branch 19 (.leaf 2740533609) (.leaf 2660003031)) (.branch 21 (.leaf 2582455608) (.leaf 2507752540)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2435762778) (.leaf 2366362522)) (.branch 25 (.leaf 2299434751) (.leaf 2234868795))) (.branch 28 (.branch 27 (.leaf 2172559938) (.leaf 2112409040)) (.branch 29 (.leaf 2054322202) (.leaf 1998210441)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1943989394) (.branch 32 (.leaf 1891579041) (.leaf 1840903446))) (.branch 35 (.branch 34 (.leaf 1791890521) (.leaf 1744471795)) (.branch 36 (.leaf 1698582209) (.leaf 1654159919)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1611146111) (.leaf 1569484834)) (.branch 40 (.leaf 1529122833) (.leaf 1490009406))) (.branch 43 (.branch 42 (.leaf 1452096256) (.leaf 1415337363)) (.branch 44 (.leaf 1379688861) (.leaf 1345108918))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1311557627) (.branch 47 (.leaf 1278996906) (.leaf 1247390399))) (.branch 50 (.branch 49 (.leaf 1216703386) (.leaf 1186902696)) (.branch 51 (.leaf 1157956628) (.leaf 1129834874)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1102508450) (.leaf 1075949625)) (.branch 55 (.leaf 1050131859) (.leaf 1025029742))) (.branch 58 (.branch 57 (.leaf 1000618942) (.leaf 976876144)) (.branch 59 (.leaf 953779007) (.leaf 931306110))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 909436913) (.branch 62 (.leaf 888151710) (.leaf 867431588))) (.branch 65 (.branch 64 (.leaf 847258396) (.leaf 827614699)) (.branch 66 (.leaf 808483752) (.leaf 789849465)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 771696371) (.leaf 754009599)) (.branch 70 (.leaf 736774844) (.leaf 719978345))) (.branch 73 (.branch 72 (.leaf 703606859) (.leaf 687647634)) (.branch 74 (.leaf 672088391) (.leaf 656917302))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 642122970) (.branch 77 (.leaf 627694408) (.leaf 613621026))) (.branch 80 (.branch 79 (.leaf 599892606) (.leaf 586499295)) (.branch 81 (.leaf 573431582) (.leaf 560680286)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 548236546) (.leaf 536091800)) (.branch 85 (.leaf 524237778) (.leaf 512666489))) (.branch 88 (.branch 87 (.leaf 501370207) (.leaf 490341465)) (.branch 89 (.leaf 479573039) (.leaf 469057941)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 458789412) (.branch 92 (.leaf 448760908) (.leaf 438966094))) (.branch 95 (.branch 94 (.leaf 429398837) (.leaf 420053195)) (.branch 96 (.leaf 410923412) (.leaf 402003912)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 393289289) (.leaf 384774302)) (.branch 100 (.leaf 376453870) (.leaf 368323064))) (.branch 103 (.branch 102 (.leaf 360377104) (.leaf 352611349)) (.branch 104 (.leaf 345021297) (.leaf 337602579))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 330350951) (.leaf 323262292)) (.branch 108 (.leaf 316332601) (.leaf 309557988))) (.branch 111 (.branch 110 (.leaf 302934677) (.leaf 296458996)) (.branch 112 (.leaf 290127377) (.leaf 283936349)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 277882541) (.leaf 271962671)) (.branch 116 (.leaf 266173548) (.leaf 260512069))) (.branch 119 (.branch 118 (.leaf 254975212) (.leaf 249560040)) (.branch 120 (.leaf 244263690) (.leaf 239083379)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 410).prefactor = (951412167608631/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 410).cutoff/(generalMeanRows 410).c)).2 =
    (74865395776473/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 410).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 410).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 410).q*(generalMeanRows 410).c/2-2 = (3309/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable134.value]
    have hcontinuation : (generalMeanRows 410).q*(generalMeanRows 410).cutoff/2-2 = (8302/3933:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable151.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 410).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 410

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 410).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 410).criticalRate j.val*(generalMeanRows 410).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 410).c*(generalMeanRows 410).criticalPoint j.val)).2-
      (generalMeanRows 410).J/2-(generalMeanRows 410).error (generalMeanGrid j.val)+
      (generalMeanRows 410).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 410).c)).2-
      (generalMeanRows 410).J/2-(generalMeanRows 410).error 4 := by
  have he : (generalMeanRows 410).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 410) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 410)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0410

/-! Kernel-checked entropy margins for general spectral rectangle 411. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0411
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4992283244) (.branch 2 (.leaf 4821003311) (.leaf 4657432605))) (.branch 5 (.branch 4 (.leaf 4501129780) (.leaf 4351684703)) (.branch 6 (.leaf 4208715728) (.leaf 4071867273)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3940807641) (.leaf 3815227066)) (.branch 10 (.leaf 3694835960) (.leaf 3579363325))) (.branch 13 (.branch 12 (.leaf 3468555320) (.leaf 3362173956)) (.branch 14 (.leaf 3259995919) (.leaf 3161811494))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3067423579) (.branch 17 (.leaf 2976646791) (.leaf 2889306645))) (.branch 20 (.branch 19 (.leaf 2805238798) (.leaf 2724288361)) (.branch 21 (.leaf 2646309261) (.leaf 2571163652)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2498721380) (.leaf 2428859481)) (.branch 25 (.leaf 2361461717) (.leaf 2296418154))) (.branch 28 (.branch 27 (.leaf 2233624761) (.leaf 2172983048)) (.branch 29 (.leaf 2114399720) (.leaf 2057786362)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2003059147) (.branch 32 (.leaf 1950138556) (.leaf 1898949126))) (.branch 35 (.branch 34 (.leaf 1849419213) (.leaf 1801480763)) (.branch 36 (.leaf 1755069111) (.leaf 1710122784)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1666583316) (.leaf 1624395085)) (.branch 40 (.leaf 1583505147) (.leaf 1543863091))) (.branch 43 (.branch 42 (.leaf 1505420897) (.leaf 1468132805)) (.branch 44 (.leaf 1431955194) (.leaf 1396846464))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1362766928) (.branch 47 (.leaf 1329678710) (.leaf 1297545649))) (.branch 50 (.branch 49 (.leaf 1266333210) (.leaf 1236008396)) (.branch 51 (.leaf 1206539672) (.leaf 1177896886)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1150051199) (.leaf 1122975020)) (.branch 55 (.leaf 1096641940) (.leaf 1071026674))) (.branch 58 (.branch 57 (.leaf 1046105007) (.leaf 1021853734)) (.branch 59 (.leaf 998250618) (.leaf 975274338))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 952904445) (.branch 62 (.leaf 931121322) (.leaf 909906139))) (.branch 65 (.branch 64 (.leaf 889240820) (.leaf 869108007)) (.branch 66 (.leaf 849491021) (.leaf 830373838)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 811741049) (.leaf 793577843)) (.branch 70 (.leaf 775869966) (.leaf 758603708))) (.branch 73 (.branch 72 (.leaf 741765871) (.leaf 725343747)) (.branch 74 (.leaf 709325096) (.leaf 693698129))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 678451482) (.branch 77 (.leaf 663574200) (.leaf 649055720))) (.branch 80 (.branch 79 (.leaf 634885854) (.leaf 621054771)) (.branch 81 (.leaf 607552983) (.leaf 594371328)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 581500963) (.leaf 568933341)) (.branch 85 (.leaf 556660207) (.leaf 544673580))) (.branch 88 (.branch 87 (.leaf 532965746) (.leaf 521529244)) (.branch 89 (.leaf 510356858) (.leaf 499441606)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 488776731) (.branch 92 (.leaf 478355691) (.leaf 468172152))) (.branch 95 (.branch 94 (.leaf 458219979) (.leaf 448493230)) (.branch 96 (.leaf 438986146) (.leaf 429693144)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 420608814) (.leaf 411727908)) (.branch 100 (.leaf 403045336) (.leaf 394556161))) (.branch 103 (.branch 102 (.leaf 386255592) (.leaf 378138978)) (.branch 104 (.leaf 370201807) (.leaf 362439693))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 354848382) (.leaf 347423737)) (.branch 108 (.leaf 340161742) (.leaf 333058493))) (.branch 111 (.branch 110 (.leaf 326110195) (.leaf 319313159)) (.branch 112 (.leaf 312663800) (.leaf 306158629)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 299794254) (.leaf 293567374)) (.branch 116 (.leaf 287474780) (.leaf 281513345))) (.branch 119 (.branch 118 (.leaf 275680028) (.leaf 269971869)) (.branch 120 (.leaf 264385984) (.leaf 258919566)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 411).prefactor = (4726237803964871/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 411).cutoff/(generalMeanRows 411).c)).2 =
    (189520446817049/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 411).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 411).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 411).q*(generalMeanRows 411).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 411).q*(generalMeanRows 411).cutoff/2-2 = (16558/7889:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable155.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 411).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 411

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 411).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 411).criticalRate j.val*(generalMeanRows 411).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 411).c*(generalMeanRows 411).criticalPoint j.val)).2-
      (generalMeanRows 411).J/2-(generalMeanRows 411).error (generalMeanGrid j.val)+
      (generalMeanRows 411).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 411).c)).2-
      (generalMeanRows 411).J/2-(generalMeanRows 411).error 4 := by
  have he : (generalMeanRows 411).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 411) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 411)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0411

/-! Kernel-checked entropy margins for general spectral rectangle 412. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0412
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4926397332) (.branch 2 (.leaf 4755013037) (.leaf 4591372645))) (.branch 5 (.branch 4 (.leaf 4435033090) (.leaf 4285582612)) (.branch 6 (.leaf 4142638028) (.leaf 4005842294)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3874862327) (.leaf 3749387043)) (.branch 10 (.leaf 3629125598) (.leaf 3513805800))) (.branch 13 (.branch 12 (.leaf 3403172664) (.leaf 3296987116)) (.branch 14 (.leaf 3195024801) (.leaf 3097075007))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3002939682) (.branch 17 (.leaf 2912432532) (.leaf 2825378198))) (.branch 20 (.branch 19 (.leaf 2741611501) (.leaf 2660976750)) (.branch 21 (.leaf 2583327100) (.leaf 2508523969)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2436436492) (.leaf 2366941023)) (.branch 25 (.leaf 2299920671) (.leaf 2235264870))) (.branch 28 (.branch 27 (.leaf 2172868988) (.leaf 2112633951)) (.branch 29 (.leaf 2054465905) (.leaf 1998275898)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1943979585) (.branch 32 (.leaf 1891496950) (.leaf 1840752052))) (.branch 35 (.branch 34 (.leaf 1791672785) (.leaf 1744190653)) (.branch 36 (.leaf 1698240566) (.leaf 1653760638)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1610692012) (.leaf 1568978684)) (.branch 40 (.leaf 1528567346) (.leaf 1489407236))) (.branch 43 (.branch 42 (.leaf 1451449995) (.leaf 1414649542)) (.branch 44 (.leaf 1378961940) (.leaf 1344345291))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1310759619) (.branch 47 (.leaf 1278166772) (.leaf 1246530322))) (.branch 50 (.branch 49 (.leaf 1215815478) (.leaf 1185988998)) (.branch 51 (.leaf 1157019111) (.leaf 1128875439)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1101528927) (.leaf 1074951775)) (.branch 55 (.leaf 1049117374) (.leaf 1024000250))) (.branch 58 (.branch 57 (.leaf 999576001) (.leaf 975821250)) (.branch 59 (.leaf 952713592) (.leaf 930231544))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 908354505) (.branch 62 (.leaf 887062709) (.leaf 866337187))) (.branch 65 (.branch 64 (.leaf 846159731) (.leaf 826512852)) (.branch 66 (.leaf 807379753) (.leaf 788744290)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 770590948) (.leaf 752904807)) (.branch 70 (.leaf 735671516) (.leaf 718877270))) (.branch 73 (.branch 72 (.leaf 702508779) (.leaf 686553252)) (.branch 74 (.leaf 670998369) (.leaf 655832263))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 641043498) (.branch 77 (.leaf 626621053) (.leaf 612554300))) (.branch 80 (.branch 79 (.leaf 598832991) (.leaf 585447239)) (.branch 81 (.leaf 572387502) (.leaf 559644572)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 547209555) (.leaf 535073866)) (.branch 85 (.leaf 523229208) (.leaf 511667564))) (.branch 88 (.branch 87 (.leaf 500381186) (.leaf 489362583)) (.branch 89 (.leaf 478604510) (.leaf 468099959)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 457842149) (.branch 92 (.leaf 447824520) (.leaf 438040718))) (.branch 95 (.branch 94 (.leaf 428484592) (.leaf 419150186)) (.branch 96 (.leaf 410031728) (.leaf 401123627)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 392420463) (.leaf 383916983)) (.branch 100 (.leaf 375608093) (.leaf 367488852))) (.branch 103 (.branch 102 (.leaf 359554469) (.leaf 351800293)) (.branch 104 (.leaf 344221813) (.leaf 336814649))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 329574550) (.leaf 322497385)) (.branch 108 (.leaf 315579146) (.leaf 308815937))) (.branch 111 (.branch 110 (.leaf 302203974) (.leaf 295739578)) (.branch 112 (.leaf 289419176) (.leaf 283239293)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 277196551) (.leaf 271287663)) (.branch 116 (.leaf 265509436) (.leaf 259858759))) (.branch 119 (.branch 118 (.leaf 254332611) (.leaf 248928047)) (.branch 120 (.leaf 243642204) (.leaf 238472295)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 412).prefactor = (948549944596367/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 412).cutoff/(generalMeanRows 412).c)).2 =
    (371407268779029/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 412).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 412).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 412).q*(generalMeanRows 412).c/2-2 = (3309/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable134.value]
    have hcontinuation : (generalMeanRows 412).q*(generalMeanRows 412).cutoff/2-2 = (16558/7889:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable155.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 412).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 412

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 412).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 412).criticalRate j.val*(generalMeanRows 412).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 412).c*(generalMeanRows 412).criticalPoint j.val)).2-
      (generalMeanRows 412).J/2-(generalMeanRows 412).error (generalMeanGrid j.val)+
      (generalMeanRows 412).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 412).c)).2-
      (generalMeanRows 412).J/2-(generalMeanRows 412).error 4 := by
  have he : (generalMeanRows 412).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 412) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 412)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0412

/-! Kernel-checked entropy margins for general spectral rectangle 413. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0413
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4946225652) (.branch 2 (.leaf 4774213334) (.leaf 4609958327))) (.branch 5 (.branch 4 (.leaf 4453017822) (.leaf 4302980254)) (.branch 6 (.leaf 4159462580) (.leaf 4022107849)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3890583019) (.leaf 3764577011)) (.branch 10 (.leaf 3643798948) (.leaf 3527976569))) (.branch 13 (.branch 12 (.leaf 3416854792) (.leaf 3310194418)) (.branch 14 (.leaf 3207770944) (.leaf 3109373488))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3014803810) (.branch 17 (.leaf 2923875412) (.leaf 2836412718))) (.branch 20 (.branch 19 (.leaf 2752250318) (.leaf 2671232281)) (.branch 21 (.leaf 2593211513) (.leaf 2518049176)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2445614144) (.leaf 2375782504)) (.branch 25 (.leaf 2308437098) (.leaf 2243467088))) (.branch 28 (.branch 27 (.leaf 2180767569) (.leaf 2120239195)) (.branch 29 (.leaf 2061787839) (.leaf 2005324278)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1950763897) (.branch 32 (.leaf 1898026413) (.leaf 1847035621))) (.branch 35 (.branch 34 (.leaf 1797719151) (.leaf 1750008252)) (.branch 36 (.leaf 1703837577) (.leaf 1659144991)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1615871391) (.leaf 1573960532)) (.branch 40 (.leaf 1533358870) (.leaf 1494015411))) (.branch 43 (.branch 42 (.leaf 1455881570) (.leaf 1418911043)) (.branch 44 (.leaf 1383059679) (.leaf 1348285368))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1314547928) (.branch 47 (.leaf 1281809006) (.leaf 1250031980))) (.branch 50 (.branch 49 (.leaf 1219181870) (.leaf 1189225247)) (.branch 51 (.leaf 1160130162) (.leaf 1131866062)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1104403722) (.leaf 1077715179)) (.branch 55 (.leaf 1051773665) (.leaf 1026553549))) (.branch 58 (.branch 57 (.leaf 1002030283) (.leaf 978180343)) (.branch 59 (.leaf 954981182) (.leaf 932411183))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 910449614) (.branch 62 (.leaf 889076580) (.leaf 868272992))) (.branch 65 (.branch 64 (.leaf 848020520) (.leaf 828301561)) (.branch 66 (.leaf 809099208) (.leaf 790397209)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 772179946) (.leaf 754432399)) (.branch 70 (.leaf 737140122) (.leaf 720289214))) (.branch 73 (.branch 72 (.leaf 703866299) (.leaf 687858496)) (.branch 74 (.leaf 672253405) (.leaf 657039076))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 642203998) (.branch 77 (.leaf 627737073) (.leaf 613627604))) (.branch 80 (.branch 79 (.leaf 599865272) (.leaf 586440123)) (.branch 81 (.leaf 573342553) (.leaf 560563291)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 548093384) (.leaf 535924190)) (.branch 85 (.leaf 524047355) (.leaf 512454813))) (.branch 88 (.branch 87 (.leaf 501138762) (.leaf 490091663)) (.branch 89 (.leaf 479306225) (.leaf 468775393)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 458492346) (.branch 92 (.leaf 448450478) (.leaf 438643397))) (.branch 95 (.branch 94 (.leaf 429064914) (.leaf 419709034)) (.branch 96 (.leaf 410569951) (.leaf 401642040)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 392919847) (.leaf 384398089)) (.branch 100 (.leaf 376071640) (.leaf 367935531))) (.branch 103 (.branch 102 (.leaf 359984942) (.leaf 352215198)) (.branch 104 (.leaf 344621759) (.leaf 337200222))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 329946311) (.leaf 322855875)) (.branch 108 (.leaf 315924881) (.leaf 309149414))) (.branch 111 (.branch 110 (.leaf 302525669) (.leaf 296049949)) (.branch 112 (.leaf 289718660) (.leaf 283528312)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 277475507) (.leaf 271556945)) (.branch 116 (.leaf 265769415) (.leaf 260109793))) (.branch 119 (.branch 118 (.leaf 254575040) (.leaf 249162201)) (.branch 120 (.leaf 243868398) (.leaf 238690831)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 413).prefactor = (474485534498957/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 413).cutoff/(generalMeanRows 413).c)).2 =
    (368496058571569/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 413).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 413).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 413).q*(generalMeanRows 413).c/2-2 = (3309/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable134.value]
    have hcontinuation : (generalMeanRows 413).q*(generalMeanRows 413).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 413).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 413

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 413).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 413).criticalRate j.val*(generalMeanRows 413).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 413).c*(generalMeanRows 413).criticalPoint j.val)).2-
      (generalMeanRows 413).J/2-(generalMeanRows 413).error (generalMeanGrid j.val)+
      (generalMeanRows 413).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 413).c)).2-
      (generalMeanRows 413).J/2-(generalMeanRows 413).error 4 := by
  have he : (generalMeanRows 413).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 413) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 413)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0413

/-! Kernel-checked entropy margins for general spectral rectangle 414. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0414
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5255361059) (.branch 2 (.leaf 5087455443) (.leaf 4926994389))) (.branch 5 (.branch 4 (.leaf 4773548128) (.leaf 4626717508)) (.branch 6 (.leaf 4486131316) (.leaf 4351443899)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4222333019) (.leaf 4098497939)) (.branch 10 (.leaf 3979657696) (.leaf 3865549539))) (.branch 13 (.branch 12 (.leaf 3755927522) (.leaf 3650561221)) (.branch 14 (.leaf 3549234576) (.leaf 3451744828))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3357901559) (.branch 17 (.leaf 3267525803) (.leaf 3180449245))) (.branch 20 (.branch 19 (.leaf 3096513475) (.leaf 3015569308)) (.branch 21 (.leaf 2937476163) (.leaf 2862101480)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2789320194) (.leaf 2719014242)) (.branch 25 (.leaf 2651072108) (.leaf 2585388407))) (.branch 28 (.branch 27 (.leaf 2521863493) (.leaf 2460403097)) (.branch 29 (.leaf 2400917999) (.leaf 2343323709)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2287540182) (.branch 32 (.leaf 2233491548) (.leaf 2181105861))) (.branch 35 (.branch 34 (.leaf 2130314866) (.leaf 2081053778)) (.branch 36 (.leaf 2033261084) (.leaf 1986878348)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1941850035) (.leaf 1898123343)) (.branch 40 (.leaf 1855648051) (.leaf 1814376370))) (.branch 43 (.branch 42 (.leaf 1774262809) (.leaf 1735264046)) (.branch 44 (.leaf 1697338804) (.leaf 1660447747))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1624553367) (.branch 47 (.leaf 1589619887) (.leaf 1555613168))) (.branch 50 (.branch 49 (.leaf 1522500621) (.leaf 1490251125)) (.branch 51 (.leaf 1458834948) (.leaf 1428223677)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1398390144) (.leaf 1369308366)) (.branch 55 (.leaf 1340953483) (.leaf 1313301699))) (.branch 58 (.branch 57 (.leaf 1286330227) (.leaf 1260017243)) (.branch 59 (.leaf 1234341829) (.leaf 1209283938))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1184824341) (.branch 62 (.leaf 1160944593) (.leaf 1137626991))) (.branch 65 (.branch 64 (.leaf 1114854542) (.leaf 1092610923)) (.branch 66 (.leaf 1070880453) (.leaf 1049648060)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1028899253) (.leaf 1008620096)) (.branch 70 (.leaf 988797177) (.leaf 969417589))) (.branch 73 (.branch 72 (.leaf 950468906) (.leaf 931939157)) (.branch 74 (.leaf 913816807) (.leaf 896090740))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 878750237) (.branch 77 (.leaf 861784959) (.leaf 845184929))) (.branch 80 (.branch 79 (.leaf 828940519) (.leaf 813042433)) (.branch 81 (.leaf 797481690) (.leaf 782249615)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 767337823) (.leaf 752738208)) (.branch 85 (.leaf 738442929) (.leaf 724444402))) (.branch 88 (.branch 87 (.leaf 710735286) (.leaf 697308477)) (.branch 89 (.leaf 684157095) (.leaf 671274473)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 658654156) (.branch 92 (.leaf 646289884) (.leaf 634175591))) (.branch 95 (.branch 94 (.leaf 622305391) (.leaf 610673577)) (.branch 96 (.leaf 599274611) (.leaf 588103116)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 577153875) (.leaf 566421818)) (.branch 100 (.leaf 555902022) (.leaf 545589705))) (.branch 103 (.branch 102 (.leaf 535480217) (.leaf 525569040)) (.branch 104 (.leaf 515851779) (.leaf 506324160))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 496982026) (.leaf 487821331)) (.branch 108 (.leaf 478838139) (.leaf 470028616))) (.branch 111 (.branch 110 (.leaf 461389030) (.leaf 452915747)) (.branch 112 (.leaf 444605225) (.leaf 436454016)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 428458758) (.leaf 420616174)) (.branch 116 (.leaf 412923069) (.leaf 405376329))) (.branch 119 (.branch 118 (.leaf 397972917) (.leaf 390709868)) (.branch 120 (.leaf 383584293) (.leaf 376593371)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 414).prefactor = (2313144709905769/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 414).cutoff/(generalMeanRows 414).c)).2 =
    (84273090461937/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 414).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 414).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 414).q*(generalMeanRows 414).c/2-2 = (227/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable159.value]
    have hcontinuation : (generalMeanRows 414).q*(generalMeanRows 414).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable160.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 414).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 414

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 414).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 414).criticalRate j.val*(generalMeanRows 414).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 414).c*(generalMeanRows 414).criticalPoint j.val)).2-
      (generalMeanRows 414).J/2-(generalMeanRows 414).error (generalMeanGrid j.val)+
      (generalMeanRows 414).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 414).c)).2-
      (generalMeanRows 414).J/2-(generalMeanRows 414).error 4 := by
  have he : (generalMeanRows 414).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 414) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 414)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0414

/-! Kernel-checked entropy margins for general spectral rectangle 415. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0415
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4943608542) (.branch 2 (.leaf 4771625487) (.leaf 4607413389))) (.branch 5 (.branch 4 (.leaf 4450527635) (.leaf 4300555027)) (.branch 6 (.leaf 4157111041) (.leaf 4019837389)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3888399820) (.leaf 3762486167)) (.branch 10 (.leaf 3641804568) (.leaf 3526081880))) (.branch 13 (.branch 12 (.leaf 3415062229) (.leaf 3308505704)) (.branch 14 (.leaf 3206187166) (.leaf 3107895168))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3013430965) (.branch 17 (.leaf 2922607612) (.leaf 2835249139))) (.branch 20 (.branch 19 (.leaf 2751189789) (.leaf 2670273327)) (.branch 21 (.leaf 2592352395) (.leaf 2517287926)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2444948599) (.leaf 2375210336)) (.branch 25 (.leaf 2307955836) (.leaf 2243074150))) (.branch 28 (.branch 27 (.leaf 2180460277) (.leaf 2120014798)) (.branch 29 (.leaf 2061643532) (.leaf 2005257216)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1950771209) (.branch 32 (.leaf 1898105217) (.leaf 1847183034))) (.branch 35 (.branch 34 (.leaf 1797932300) (.leaf 1750284281)) (.branch 36 (.leaf 1704173659) (.leaf 1659538333)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1616319240) (.leaf 1574460179)) (.branch 40 (.leaf 1533907657) (.leaf 1494610734))) (.branch 43 (.branch 42 (.leaf 1456520884) (.leaf 1419591861)) (.branch 44 (.leaf 1383779579) (.leaf 1349041991))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1315338982) (.branch 47 (.leaf 1282632266) (.leaf 1250885288))) (.branch 50 (.branch 49 (.leaf 1220063137) (.leaf 1190132453)) (.branch 51 (.leaf 1161061355) (.leaf 1132819359)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1105377307) (.leaf 1078707302)) (.branch 55 (.leaf 1052782645) (.leaf 1027577769))) (.branch 58 (.branch 57 (.leaf 1003068190) (.leaf 979230449)) (.branch 59 (.leaf 956042060) (.leaf 933481467))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 911527996) (.branch 62 (.leaf 890161814) (.leaf 869363884))) (.branch 65 (.branch 64 (.leaf 849115934) (.leaf 829400416)) (.branch 66 (.leaf 810200472) (.leaf 791499903)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 773283139) (.leaf 755535208)) (.branch 70 (.leaf 738241710) (.leaf 721388790))) (.branch 73 (.branch 72 (.leaf 704963114) (.leaf 688951844)) (.branch 74 (.leaf 673342617) (.leaf 658123525))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 643283093) (.branch 77 (.leaf 628810261) (.leaf 614694363))) (.branch 80 (.branch 79 (.leaf 600925117) (.leaf 587492599)) (.branch 81 (.leaf 574387236) (.leaf 561599785)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 549121326) (.leaf 536943238)) (.branch 85 (.leaf 525057199) (.leaf 513455162))) (.branch 88 (.branch 87 (.leaf 502129353) (.leaf 491072254)) (.branch 89 (.leaf 480276596) (.leaf 469735346)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 459441699) (.branch 92 (.leaf 449389072) (.leaf 439571088))) (.branch 95 (.branch 94 (.leaf 429981576) (.leaf 420614559)) (.branch 96 (.leaf 411464244) (.leaf 402525021)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 393791451) (.leaf 385258263)) (.branch 100 (.leaf 376920344) (.leaf 368772737))) (.branch 103 (.branch 102 (.leaf 360810634) (.leaf 353029368)) (.branch 104 (.leaf 345424411) (.leaf 337991369))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 330725975) (.leaf 323624085)) (.branch 108 (.leaf 316681676) (.leaf 309894838))) (.branch 111 (.branch 110 (.leaf 303259775) (.leaf 296772795)) (.branch 112 (.leaf 290430312) (.leaf 284228838)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 278164984) (.leaf 272235453)) (.branch 116 (.leaf 266437038) (.leaf 260766620))) (.branch 119 (.branch 118 (.leaf 255221165) (.leaf 249797720)) (.branch 120 (.leaf 244493410) (.leaf 239305439)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 415).prefactor = (4759319329208149/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 415).cutoff/(generalMeanRows 415).c)).2 =
    (371407268779029/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 415).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 415).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 415).q*(generalMeanRows 415).c/2-2 = (3309/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable134.value]
    have hcontinuation : (generalMeanRows 415).q*(generalMeanRows 415).cutoff/2-2 = (16558/7889:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable155.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 415).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 415

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 415).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 415).criticalRate j.val*(generalMeanRows 415).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 415).c*(generalMeanRows 415).criticalPoint j.val)).2-
      (generalMeanRows 415).J/2-(generalMeanRows 415).error (generalMeanGrid j.val)+
      (generalMeanRows 415).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 415).c)).2-
      (generalMeanRows 415).J/2-(generalMeanRows 415).error 4 := by
  have he : (generalMeanRows 415).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 415) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 415)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0415

/-! Kernel-checked entropy margins for general spectral rectangle 416. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0416
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5254065918) (.branch 2 (.leaf 5086205041) (.leaf 4925800498))) (.branch 5 (.branch 4 (.leaf 4772420815) (.leaf 4625665300)) (.branch 6 (.leaf 4485161354) (.leaf 4350562071)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4221544091) (.leaf 4097805666)) (.branch 10 (.leaf 3979064927) (.leaf 3865058315))) (.branch 13 (.branch 12 (.leaf 3755539160) (.leaf 3650276395)) (.branch 14 (.leaf 3549053387) (.leaf 3451666874))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3357925990) (.branch 17 (.leaf 3267651380) (.leaf 3180674386))) (.branch 20 (.branch 19 (.leaf 3096836301) (.leaf 3015987687)) (.branch 21 (.leaf 2937987742) (.leaf 2862703723)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2790010409) (.leaf 2719789610)) (.branch 25 (.leaf 2651929709) (.leaf 2586325241))) (.branch 28 (.branch 27 (.leaf 2522876500) (.leaf 2461489177)) (.branch 29 (.leaf 2402074024) (.leaf 2344546541)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2288826686) (.branch 32 (.leaf 2234838601) (.leaf 2182510364))) (.branch 35 (.branch 34 (.leaf 2131773751) (.leaf 2082564021)) (.branch 36 (.leaf 2034819705) (.leaf 1988482420)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1943496688) (.leaf 1899809773)) (.branch 40 (.leaf 1857371517) (.leaf 1816134201))) (.branch 43 (.branch 42 (.leaf 1776052406) (.leaf 1737082881)) (.branch 44 (.leaf 1699184427) (.leaf 1662317783))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1626445516) (.branch 47 (.leaf 1591531928) (.leaf 1557542957))) (.branch 50 (.branch 49 (.leaf 1524446091) (.leaf 1492210285)) (.branch 51 (.leaf 1460805884) (.leaf 1430204548)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1400379186) (.leaf 1371303886)) (.branch 55 (.leaf 1342953862) (.leaf 1315305386))) (.branch 58 (.branch 57 (.leaf 1288335742) (.leaf 1262023172)) (.branch 59 (.leaf 1236346827) (.leaf 1211286720))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1186823689) (.branch 62 (.leaf 1162939347) (.leaf 1139616053))) (.branch 65 (.branch 64 (.leaf 1116836869) (.leaf 1094585530)) (.branch 66 (.leaf 1072846407) (.leaf 1051604483)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1030845316) (.leaf 1010555019)) (.branch 70 (.leaf 990720228) (.leaf 971328082))) (.branch 73 (.branch 72 (.leaf 952366197) (.leaf 933822645)) (.branch 74 (.leaf 915685934) (.leaf 897944986))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 880589118) (.branch 77 (.leaf 863608028) (.leaf 846991775))) (.branch 80 (.branch 79 (.leaf 830730763) (.leaf 814815728)) (.branch 81 (.leaf 799237720) (.leaf 783988093)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 769058490) (.leaf 754440831)) (.branch 85 (.leaf 740127301) (.leaf 726110341))) (.branch 88 (.branch 87 (.leaf 712382632) (.leaf 698937093)) (.branch 89 (.leaf 685766863) (.leaf 672865298)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 660225960) (.branch 92 (.leaf 647842609) (.leaf 635709192))) (.branch 95 (.branch 94 (.leaf 623819844) (.leaf 612168871)) (.branch 96 (.leaf 600750749) (.leaf 589560117)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 578591768) (.leaf 567840647)) (.branch 100 (.leaf 557301841) (.leaf 546970580))) (.branch 103 (.branch 102 (.leaf 536842223) (.leaf 526912261)) (.branch 104 (.leaf 517176311) (.leaf 507630105))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 498269494) (.leaf 489090441)) (.branch 108 (.leaf 480089015) (.leaf 471261389))) (.branch 111 (.branch 110 (.leaf 462603838) (.leaf 454112732)) (.branch 112 (.leaf 445784535) (.leaf 437615803)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 429603179) (.leaf 421743389)) (.branch 116 (.leaf 414033243) (.leaf 406469629))) (.branch 119 (.branch 118 (.leaf 399049513) (.leaf 391769934)) (.branch 120 (.leaf 384628004) (.leaf 377620904)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 416).prefactor = (4640093825441773/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 416).cutoff/(generalMeanRows 416).c)).2 =
    (212138331258571/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 416).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 416).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 416).q*(generalMeanRows 416).c/2-2 = (227/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable159.value]
    have hcontinuation : (generalMeanRows 416).q*(generalMeanRows 416).cutoff/2-2 = (6610/3087:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable161.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 416).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 416

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 416).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 416).criticalRate j.val*(generalMeanRows 416).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 416).c*(generalMeanRows 416).criticalPoint j.val)).2-
      (generalMeanRows 416).J/2-(generalMeanRows 416).error (generalMeanGrid j.val)+
      (generalMeanRows 416).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 416).c)).2-
      (generalMeanRows 416).J/2-(generalMeanRows 416).error 4 := by
  have he : (generalMeanRows 416).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 416) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 416)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0416

/-! Kernel-checked entropy margins for general spectral rectangle 417. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0417
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5273254132) (.branch 2 (.leaf 5104776843) (.leaf 4943769463))) (.branch 5 (.branch 4 (.leaf 4789800760) (.leaf 4642470221)) (.branch 6 (.leaf 4501405372) (.leaf 4366259381)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4236708913) (.leaf 4112452209)) (.branch 10 (.leaf 3993207347) (.leaf 3878710683))) (.branch 13 (.branch 12 (.leaf 3768715432) (.leaf 3662990388)) (.branch 14 (.leaf 3561318753) (.leaf 3463497079))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3369334299) (.branch 17 (.leaf 3278650839) (.leaf 3191277809))) (.branch 20 (.branch 19 (.leaf 3107056260) (.leaf 3025836501)) (.branch 21 (.leaf 2947477469) (.leaf 2871846156)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2798817070) (.leaf 2728271745)) (.branch 25 (.leaf 2660098287) (.leaf 2594190951))) (.branch 28 (.branch 27 (.leaf 2530449751) (.leaf 2468780100)) (.branch 29 (.leaf 2409092471) (.leaf 2351302088)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2295328634) (.branch 32 (.leaf 2241095979) (.leaf 2188531933))) (.branch 35 (.branch 34 (.leaf 2137568008) (.leaf 2088139200)) (.branch 36 (.leaf 2040183785) (.leaf 1993643128)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1948461505) (.leaf 1904585936)) (.branch 40 (.leaf 1861966027) (.leaf 1820553827))) (.branch 43 (.branch 42 (.leaf 1780303691) (.leaf 1741172147)) (.branch 44 (.leaf 1703117781) (.leaf 1666101120))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1630084529) (.branch 47 (.leaf 1595032110) (.leaf 1560909607))) (.branch 50 (.branch 49 (.leaf 1527684321) (.leaf 1495325024)) (.branch 51 (.leaf 1463801884) (.leaf 1433086389)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1403151281) (.leaf 1373970488)) (.branch 55 (.leaf 1345519065) (.leaf 1317773134))) (.branch 58 (.branch 57 (.leaf 1290709832) (.leaf 1264307258)) (.branch 59 (.leaf 1238544427) (.leaf 1213401220))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1188858345) (.branch 62 (.leaf 1164897293) (.leaf 1141500301))) (.branch 65 (.branch 64 (.leaf 1118650318) (.leaf 1096330966)) (.branch 66 (.leaf 1074526509) (.leaf 1053221826)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1032402375) (.leaf 1012054172)) (.branch 70 (.leaf 992163762) (.leaf 972718192))) (.branch 73 (.branch 72 (.leaf 953704994) (.leaf 935112156)) (.branch 74 (.leaf 916928104) (.leaf 899141685))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 881742143) (.branch 77 (.leaf 864719102) (.leaf 848062554))) (.branch 80 (.branch 79 (.leaf 831762836) (.leaf 815810621)) (.branch 81 (.leaf 800196898) (.leaf 784912962)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 769950400) (.leaf 755301077)) (.branch 85 (.leaf 740957126) (.leaf 726910938))) (.branch 88 (.branch 87 (.leaf 713155147) (.leaf 699682623)) (.branch 89 (.leaf 686486463) (.leaf 673559980)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 660896694) (.branch 92 (.leaf 648490325) (.leaf 636334786))) (.branch 95 (.branch 94 (.leaf 624424171) (.leaf 612752755)) (.branch 96 (.leaf 601314978) (.leaf 590105447)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 579118926) (.leaf 568350330)) (.branch 100 (.leaf 557794717) (.leaf 547447289))) (.branch 103 (.branch 102 (.leaf 537303382) (.leaf 527358459)) (.branch 104 (.leaf 517608113) (.leaf 508048056))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 498674114) (.leaf 489482230)) (.branch 108 (.leaf 480468452) (.leaf 471628935))) (.branch 111 (.branch 110 (.leaf 462959934) (.leaf 454457802)) (.branch 112 (.leaf 446118985) (.leaf 437940023)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 429917543) (.leaf 422048257)) (.branch 116 (.leaf 414328960) (.leaf 406756525))) (.branch 119 (.branch 118 (.leaf 399327906) (.leaf 392040129)) (.branch 120 (.leaf 384890294) (.leaf 377875569)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 417).prefactor = (2321020337684241/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 417).cutoff/(generalMeanRows 417).c)).2 =
    (84273090461937/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 417).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 417).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 417).q*(generalMeanRows 417).c/2-2 = (227/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable159.value]
    have hcontinuation : (generalMeanRows 417).q*(generalMeanRows 417).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable160.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 417).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 417

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 417).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 417).criticalRate j.val*(generalMeanRows 417).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 417).c*(generalMeanRows 417).criticalPoint j.val)).2-
      (generalMeanRows 417).J/2-(generalMeanRows 417).error (generalMeanGrid j.val)+
      (generalMeanRows 417).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 417).c)).2-
      (generalMeanRows 417).J/2-(generalMeanRows 417).error 4 := by
  have he : (generalMeanRows 417).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 417) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 417)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0417

/-! Kernel-checked entropy margins for general spectral rectangle 418. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0418
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5201053731) (.branch 2 (.leaf 5032317051) (.leaf 4871085806))) (.branch 5 (.branch 4 (.leaf 4716927234) (.leaf 4569439377)) (.branch 6 (.leaf 4428248386) (.leaf 4293006120)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4163388003) (.leaf 4039091087)) (.branch 10 (.leaf 3919832317) (.leaf 3805346968))) (.branch 13 (.branch 12 (.leaf 3695387216) (.leaf 3589720861)) (.branch 14 (.leaf 3488130155) (.leaf 3390410734))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3296370652) (.branch 17 (.leaf 3205829491) (.leaf 3118617550))) (.branch 20 (.branch 19 (.leaf 3034575095) (.leaf 2953551682)) (.branch 21 (.leaf 2875405523) (.leaf 2800002907)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2727217667) (.leaf 2656930685)) (.branch 25 (.leaf 2589029436) (.leaf 2523407567))) (.branch 28 (.branch 27 (.leaf 2459964504) (.leaf 2398605090)) (.branch 29 (.leaf 2339239250) (.leaf 2281781675)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2226151535) (.branch 32 (.leaf 2172272202) (.leaf 2120071004))) (.branch 35 (.branch 34 (.leaf 2069478989) (.leaf 2020430701)) (.branch 36 (.leaf 1972863980) (.leaf 1926719768)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1881941934) (.leaf 1838477099)) (.branch 40 (.leaf 1796274488) (.leaf 1755285780))) (.branch 43 (.branch 42 (.leaf 1715464967) (.leaf 1676768233)) (.branch 44 (.leaf 1639153825) (.leaf 1602581945))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1567014644) (.branch 47 (.leaf 1532415715) (.leaf 1498750610))) (.branch 50 (.branch 49 (.leaf 1465986342) (.leaf 1434091407)) (.branch 51 (.leaf 1403035705) (.leaf 1372790464)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1343328177) (.leaf 1314622528)) (.branch 55 (.leaf 1286648338) (.leaf 1259381504))) (.branch 58 (.branch 57 (.leaf 1232798942) (.leaf 1206878541)) (.branch 59 (.leaf 1181599109) (.leaf 1156940331))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1132882723) (.branch 62 (.leaf 1109407592) (.leaf 1086496998))) (.branch 65 (.branch 64 (.leaf 1064133717) (.leaf 1042301206)) (.branch 66 (.leaf 1020983569) (.leaf 1000165529)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 979832398) (.leaf 959970047)) (.branch 70 (.leaf 940564882) (.leaf 921603820))) (.branch 73 (.branch 72 (.leaf 903074262) (.leaf 884964075)) (.branch 74 (.leaf 867261566) (.leaf 849955466))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 833034911) (.branch 77 (.leaf 816489421) (.leaf 800308885))) (.branch 80 (.branch 79 (.leaf 784483544) (.leaf 769003977)) (.branch 81 (.leaf 753861084) (.leaf 739046076)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 724550456) (.leaf 710366012)) (.branch 85 (.leaf 696484803) (.leaf 682899146))) (.branch 88 (.branch 87 (.leaf 669601608) (.leaf 656584994)) (.branch 89 (.leaf 643842338) (.leaf 631366894)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 619152127) (.branch 92 (.leaf 607191702) (.leaf 595479481))) (.branch 95 (.branch 94 (.leaf 584009512) (.leaf 572776021)) (.branch 96 (.leaf 561773407) (.leaf 550996237)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 540439234) (.leaf 530097278)) (.branch 100 (.leaf 519965395) (.leaf 510038752))) (.branch 103 (.branch 102 (.leaf 500312656) (.leaf 490782544)) (.branch 104 (.leaf 481443981) (.leaf 472292656))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 463324373) (.leaf 454535054)) (.branch 108 (.leaf 445920729) (.leaf 437477535))) (.branch 111 (.branch 110 (.leaf 429201712) (.leaf 421089599)) (.branch 112 (.leaf 413137631) (.leaf 405342335)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 397700329) (.leaf 390208316)) (.branch 116 (.leaf 382863085) (.leaf 375661505))) (.branch 119 (.branch 118 (.leaf 368600523) (.leaf 361677162)) (.branch 120 (.leaf 354888521) (.leaf 348231767)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 418).prefactor = (4657845559660923/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 418).cutoff/(generalMeanRows 418).c)).2 =
    (41355291257289/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 418).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 418).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 418).q*(generalMeanRows 418).c/2-2 = (1169/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable162.value]
    have hcontinuation : (generalMeanRows 418).q*(generalMeanRows 418).cutoff/2-2 = (824/387:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable160.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 418).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 418

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 418).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 418).criticalRate j.val*(generalMeanRows 418).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 418).c*(generalMeanRows 418).criticalPoint j.val)).2-
      (generalMeanRows 418).J/2-(generalMeanRows 418).error (generalMeanGrid j.val)+
      (generalMeanRows 418).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 418).c)).2-
      (generalMeanRows 418).J/2-(generalMeanRows 418).error 4 := by
  have he : (generalMeanRows 418).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 418) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 418)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0418

/-! Kernel-checked entropy margins for general spectral rectangle 419. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0419
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4987198538) (.branch 2 (.leaf 4816000535) (.leaf 4652537568))) (.branch 5 (.branch 4 (.leaf 4496364737) (.leaf 4347068695)) (.branch 6 (.leaf 4204264893) (.leaf 4067595127)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3936725337) (.leaf 3811343628)) (.branch 10 (.leaf 3691158500) (.leaf 3575897238))) (.branch 13 (.branch 12 (.leaf 3465304463) (.leaf 3359140812)) (.branch 14 (.leaf 3257181748) (.leaf 3159216464))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3065046896) (.branch 17 (.leaf 2974486808) (.leaf 2887360967))) (.branch 20 (.branch 19 (.leaf 2803504376) (.leaf 2722761575)) (.branch 21 (.leaf 2644986000) (.leaf 2570039383)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2497791213) (.leaf 2428118225)) (.branch 25 (.leaf 2360903934) (.leaf 2296038205))) (.branch 28 (.branch 27 (.leaf 2233416850) (.leaf 2172941259)) (.branch 29 (.leaf 2114518052) (.leaf 2058058761)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2003479532) (.branch 32 (.leaf 1950700846) (.leaf 1899647259))) (.branch 35 (.branch 34 (.leaf 1850247167) (.leaf 1802432575)) (.branch 36 (.leaf 1756138890) (.leaf 1711304722)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1667871705) (.leaf 1625784323)) (.branch 40 (.leaf 1584989748) (.leaf 1545437691))) (.branch 43 (.branch 42 (.leaf 1507080261) (.leaf 1469871832)) (.branch 44 (.leaf 1433768921) (.leaf 1398730067))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1364715727) (.branch 47 (.leaf 1331688170) (.leaf 1299611380))) (.branch 50 (.branch 49 (.leaf 1268450967) (.leaf 1238174082)) (.branch 51 (.leaf 1208749332) (.leaf 1180146710)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1152337521) (.leaf 1125294314)) (.branch 55 (.leaf 1098990818) (.leaf 1073401887))) (.branch 58 (.branch 57 (.leaf 1048503437) (.leaf 1024272398)) (.branch 59 (.leaf 1000686660) (.leaf 977725028))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 955367178) (.branch 62 (.leaf 933593611) (.leaf 912385614))) (.branch 65 (.branch 64 (.leaf 891725226) (.leaf 871595198)) (.branch 66 (.leaf 851978959) (.leaf 832860588)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 814224779) (.leaf 796056815)) (.branch 70 (.leaf 778342540) (.leaf 761068333))) (.branch 73 (.branch 72 (.leaf 744221083) (.leaf 727788169)) (.branch 74 (.leaf 711757432) (.leaf 696117161))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 680856068) (.branch 77 (.leaf 665963272) (.leaf 651428280))) (.branch 80 (.branch 79 (.leaf 637240970) (.leaf 623391577)) (.branch 81 (.leaf 609870673) (.leaf 596669158)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 583778243) (.leaf 571189438)) (.branch 85 (.leaf 558894539) (.leaf 546885614))) (.branch 88 (.branch 87 (.leaf 535154998) (.leaf 523695275)) (.branch 89 (.leaf 512499272) (.leaf 501560049)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 490870886) (.branch 92 (.leaf 480425281) (.leaf 470216935))) (.branch 95 (.branch 94 (.leaf 460239747) (.leaf 450487806)) (.branch 96 (.leaf 440955384) (.leaf 431636928)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 422527054) (.leaf 413620541)) (.branch 100 (.leaf 404912323) (.leaf 396397487))) (.branch 103 (.branch 102 (.leaf 388071263) (.leaf 379929021)) (.branch 104 (.leaf 371966268) (.leaf 364178637))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 356561891) (.leaf 349111909)) (.branch 108 (.leaf 341824691) (.leaf 334696345))) (.branch 111 (.branch 110 (.leaf 327723091) (.leaf 320901254)) (.branch 112 (.leaf 314227257) (.leaf 307697624)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 301308972) (.leaf 295058011)) (.branch 116 (.leaf 288941537) (.leaf 282956434))) (.branch 119 (.branch 118 (.leaf 277099668) (.leaf 271368284)) (.branch 120 (.leaf 265759405) (.leaf 260270230)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 419).prefactor = (4754792888713973/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 419).cutoff/(generalMeanRows 419).c)).2 =
    (96222215879131/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 419).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 419).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 419).q*(generalMeanRows 419).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 419).q*(generalMeanRows 419).cutoff/2-2 = (16650/7843:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable158.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 419).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 419

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 419).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 419).criticalRate j.val*(generalMeanRows 419).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 419).c*(generalMeanRows 419).criticalPoint j.val)).2-
      (generalMeanRows 419).J/2-(generalMeanRows 419).error (generalMeanGrid j.val)+
      (generalMeanRows 419).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 419).c)).2-
      (generalMeanRows 419).J/2-(generalMeanRows 419).error 4 := by
  have he : (generalMeanRows 419).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 419) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 419)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0419

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock05 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 5 i) := by
  fin_cases i
  · exact EntropyRow0350.numerical
  · exact EntropyRow0351.numerical
  · exact EntropyRow0352.numerical
  · exact EntropyRow0353.numerical
  · exact EntropyRow0354.numerical
  · exact EntropyRow0355.numerical
  · exact EntropyRow0356.numerical
  · exact EntropyRow0357.numerical
  · exact EntropyRow0358.numerical
  · exact EntropyRow0359.numerical
  · exact EntropyRow0360.numerical
  · exact EntropyRow0361.numerical
  · exact EntropyRow0362.numerical
  · exact EntropyRow0363.numerical
  · exact EntropyRow0364.numerical
  · exact EntropyRow0365.numerical
  · exact EntropyRow0366.numerical
  · exact EntropyRow0367.numerical
  · exact EntropyRow0368.numerical
  · exact EntropyRow0369.numerical
  · exact EntropyRow0370.numerical
  · exact EntropyRow0371.numerical
  · exact EntropyRow0372.numerical
  · exact EntropyRow0373.numerical
  · exact EntropyRow0374.numerical
  · exact EntropyRow0375.numerical
  · exact EntropyRow0376.numerical
  · exact EntropyRow0377.numerical
  · exact EntropyRow0378.numerical
  · exact EntropyRow0379.numerical
  · exact EntropyRow0380.numerical
  · exact EntropyRow0381.numerical
  · exact EntropyRow0382.numerical
  · exact EntropyRow0383.numerical
  · exact EntropyRow0384.numerical
  · exact EntropyRow0385.numerical
  · exact EntropyRow0386.numerical
  · exact EntropyRow0387.numerical
  · exact EntropyRow0388.numerical
  · exact EntropyRow0389.numerical
  · exact EntropyRow0390.numerical
  · exact EntropyRow0391.numerical
  · exact EntropyRow0392.numerical
  · exact EntropyRow0393.numerical
  · exact EntropyRow0394.numerical
  · exact EntropyRow0395.numerical
  · exact EntropyRow0396.numerical
  · exact EntropyRow0397.numerical
  · exact EntropyRow0398.numerical
  · exact EntropyRow0399.numerical
  · exact EntropyRow0400.numerical
  · exact EntropyRow0401.numerical
  · exact EntropyRow0402.numerical
  · exact EntropyRow0403.numerical
  · exact EntropyRow0404.numerical
  · exact EntropyRow0405.numerical
  · exact EntropyRow0406.numerical
  · exact EntropyRow0407.numerical
  · exact EntropyRow0408.numerical
  · exact EntropyRow0409.numerical
  · exact EntropyRow0410.numerical
  · exact EntropyRow0411.numerical
  · exact EntropyRow0412.numerical
  · exact EntropyRow0413.numerical
  · exact EntropyRow0414.numerical
  · exact EntropyRow0415.numerical
  · exact EntropyRow0416.numerical
  · exact EntropyRow0417.numerical
  · exact EntropyRow0418.numerical
  · exact EntropyRow0419.numerical
end SingularValueBounds.KL.Certificates
