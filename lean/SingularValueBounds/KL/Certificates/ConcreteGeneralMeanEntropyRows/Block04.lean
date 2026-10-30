import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block08
import SingularValueBounds.KL.Certificates.GeneralMeanDecayTables.Block09
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false

/-! Exact integer-evaluated entropy nodes and critical margins for seventy rows. -/

/-! Kernel-checked entropy margins for general spectral rectangle 280. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0280
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4818944753) (.branch 2 (.leaf 4643836770) (.leaf 4476803254))) (.branch 5 (.branch 4 (.leaf 4317379387) (.leaf 4165133222)) (.branch 6 (.leaf 4019662820) (.leaf 3880593696)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3747576524) (.leaf 3620285090)) (.branch 10 (.leaf 3498414438) (.leaf 3381679200))) (.branch 13 (.branch 12 (.leaf 3269812088) (.leaf 3162562521)) (.branch 14 (.leaf 3059695386) (.leaf 2960989896))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2866238564) (.branch 17 (.leaf 2775246254) (.leaf 2687829314))) (.branch 20 (.branch 19 (.leaf 2603814787) (.leaf 2523039677)) (.branch 21 (.leaf 2445350284) (.leaf 2370601581)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2298656645) (.leaf 2229386136)) (.branch 25 (.leaf 2162667804) (.leaf 2098386044))) (.branch 28 (.branch 27 (.leaf 2036431474) (.leaf 1976700551)) (.branch 29 (.leaf 1919095211) (.leaf 1863522534)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1809894436) (.branch 32 (.leaf 1758127374) (.leaf 1708142083))) (.branch 35 (.branch 34 (.leaf 1659863320) (.leaf 1613219630)) (.branch 36 (.leaf 1568143130) (.leaf 1524569299)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1482436792) (.leaf 1441687254)) (.branch 40 (.leaf 1402265162) (.leaf 1364117655))) (.branch 43 (.branch 42 (.leaf 1327194399) (.leaf 1291447440)) (.branch 44 (.leaf 1256831079) (.leaf 1223301746))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1190817891) (.branch 47 (.leaf 1159339872) (.leaf 1128829853))) (.branch 50 (.branch 49 (.leaf 1099251715) (.leaf 1070570960)) (.branch 51 (.leaf 1042754630) (.leaf 1015771224)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 989590630) (.leaf 964184047)) (.branch 55 (.leaf 939523922) (.leaf 915583889))) (.branch 58 (.branch 57 (.leaf 892338704) (.leaf 869764195)) (.branch 59 (.leaf 847837208) (.leaf 826535552))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 805837958) (.branch 62 (.leaf 785724034) (.leaf 766174217))) (.branch 65 (.branch 64 (.leaf 747169739) (.leaf 728692588)) (.branch 66 (.leaf 710725472) (.leaf 693251781)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 676255564) (.leaf 659721489)) (.branch 70 (.leaf 643634821) (.leaf 627981393))) (.branch 73 (.branch 72 (.leaf 612747577) (.leaf 597920263)) (.branch 74 (.leaf 583486836) (.leaf 569435152))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 555753518) (.branch 77 (.leaf 542430669) (.leaf 529455757))) (.branch 80 (.branch 79 (.leaf 516818323) (.leaf 504508289)) (.branch 81 (.leaf 492515935) (.leaf 480831888)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 469447104) (.leaf 458352858)) (.branch 85 (.leaf 447540725) (.leaf 437002574))) (.branch 88 (.branch 87 (.leaf 426730551) (.leaf 416717071)) (.branch 89 (.leaf 406954803) (.leaf 397436665)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 388155808) (.branch 92 (.leaf 379105611) (.leaf 370279672))) (.branch 95 (.branch 94 (.leaf 361671797) (.leaf 353275992)) (.branch 96 (.leaf 345086457) (.leaf 337097577)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 329303917) (.leaf 321700213)) (.branch 100 (.leaf 314281365) (.leaf 307042433))) (.branch 103 (.branch 102 (.leaf 299978631) (.leaf 293085318)) (.branch 104 (.leaf 286357996) (.leaf 279792306))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 273384017) (.leaf 267129027)) (.branch 108 (.leaf 261023357) (.leaf 255063145))) (.branch 111 (.branch 110 (.leaf 249244643) (.leaf 243564214)) (.branch 112 (.leaf 238018326) (.leaf 232603550)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 227316556) (.leaf 222154109)) (.branch 116 (.leaf 217113067) (.leaf 212190377))) (.branch 119 (.branch 118 (.leaf 207383071) (.leaf 202688266)) (.branch 120 (.leaf 198103159) (.leaf 193625024)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 280).prefactor = (2450754123936641/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 280).cutoff/(generalMeanRows 280).c)).2 =
    (178128549058887/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 280).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 280).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 280).q*(generalMeanRows 280).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 280).q*(generalMeanRows 280).cutoff/2-2 = (2126/1005:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable121.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 280).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 280

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 280).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 280).criticalRate j.val*(generalMeanRows 280).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 280).c*(generalMeanRows 280).criticalPoint j.val)).2-
      (generalMeanRows 280).J/2-(generalMeanRows 280).error (generalMeanGrid j.val)+
      (generalMeanRows 280).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 280).c)).2-
      (generalMeanRows 280).J/2-(generalMeanRows 280).error 4 := by
  have he : (generalMeanRows 280).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 280) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 280)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0280

/-! Kernel-checked entropy margins for general spectral rectangle 281. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0281
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4812475583) (.branch 2 (.leaf 4637644629) (.leaf 4470867315))) (.branch 5 (.branch 4 (.leaf 4311680570) (.leaf 4159654048)) (.branch 6 (.leaf 4014387277) (.leaf 3875507114)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3742665468) (.leaf 3615537253)) (.branch 10 (.leaf 3493818550) (.leaf 3377224940))) (.branch 13 (.branch 12 (.leaf 3265490006) (.leaf 3158363968)) (.branch 14 (.leaf 3055612443) (.leaf 2957015316))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2862365717) (.branch 17 (.leaf 2771469072) (.leaf 2684142248))) (.branch 20 (.branch 19 (.leaf 2600212761) (.leaf 2519518050)) (.branch 21 (.leaf 2441904810) (.leaf 2367228377)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2295352165) (.leaf 2226147134)) (.branch 25 (.leaf 2159491314) (.leaf 2095269353))) (.branch 28 (.branch 27 (.leaf 2033372101) (.leaf 1973696227)) (.branch 29 (.leaf 1916143860) (.leaf 1860622256)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1807043489) (.branch 32 (.leaf 1755324165) (.leaf 1705385149))) (.branch 35 (.branch 34 (.leaf 1657151319) (.leaf 1610551330)) (.branch 36 (.leaf 1565517397) (.leaf 1521985089)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1479893141) (.leaf 1439183274)) (.branch 40 (.leaf 1399800028) (.leaf 1361690604))) (.branch 43 (.branch 42 (.leaf 1324804720) (.leaf 1289094470)) (.branch 44 (.leaf 1254514199) (.leaf 1221020376))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1188571485) (.branch 47 (.leaf 1157127914) (.leaf 1126651857))) (.branch 50 (.branch 49 (.leaf 1097107217) (.leaf 1068459518)) (.branch 51 (.leaf 1040675821) (.leaf 1013724643)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 987575885) (.leaf 962200760)) (.branch 55 (.leaf 937571726) (.leaf 913662426))) (.branch 58 (.branch 57 (.leaf 890447626) (.leaf 867903161)) (.branch 59 (.leaf 846005881) (.leaf 824733602))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 804065061) (.branch 62 (.leaf 783979867) (.leaf 764458461))) (.branch 65 (.branch 64 (.leaf 745482079) (.leaf 727032710)) (.branch 66 (.leaf 709093062) (.leaf 691646529)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 674677160) (.leaf 658169624)) (.branch 70 (.leaf 642109187) (.leaf 626481681))) (.branch 73 (.branch 72 (.leaf 611273480) (.leaf 596471474)) (.branch 74 (.leaf 582063048) (.leaf 568036058))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 554378810) (.branch 77 (.leaf 541080043) (.leaf 528128905))) (.branch 80 (.branch 79 (.leaf 515514941) (.leaf 503228070)) (.branch 81 (.leaf 491258574) (.leaf 479597080)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 468234546) (.leaf 457162244)) (.branch 85 (.leaf 446371754) (.leaf 435854944))) (.branch 88 (.branch 87 (.leaf 425603961) (.leaf 415611220)) (.branch 89 (.leaf 405869393) (.leaf 396371397)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 387110386) (.branch 92 (.leaf 378079741) (.leaf 369273060))) (.branch 95 (.branch 94 (.leaf 360684150) (.leaf 352307021)) (.branch 96 (.leaf 344135873) (.leaf 336165094)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 328389251) (.leaf 320803080)) (.branch 100 (.leaf 313401486) (.leaf 306179529))) (.branch 103 (.branch 102 (.leaf 299132426) (.leaf 292255539)) (.branch 104 (.leaf 285544373) (.leaf 278994569))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 272601901) (.leaf 266362269)) (.branch 108 (.leaf 260271696) (.leaf 254326322))) (.branch 111 (.branch 110 (.leaf 248522404) (.leaf 242856307)) (.branch 112 (.leaf 237324501) (.leaf 231923560)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 226650158) (.leaf 221501061)) (.branch 116 (.leaf 216473132) (.leaf 211563319))) (.branch 119 (.branch 118 (.leaf 206768659) (.leaf 202086271)) (.branch 120 (.leaf 197513355) (.leaf 193047189)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 281).prefactor = (4885466664667211/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 281).cutoff/(generalMeanRows 281).c)).2 =
    (177382836765551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 281).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 281).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 281).q*(generalMeanRows 281).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 281).q*(generalMeanRows 281).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable123.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 281).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 281

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 281).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 281).criticalRate j.val*(generalMeanRows 281).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 281).c*(generalMeanRows 281).criticalPoint j.val)).2-
      (generalMeanRows 281).J/2-(generalMeanRows 281).error (generalMeanGrid j.val)+
      (generalMeanRows 281).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 281).c)).2-
      (generalMeanRows 281).J/2-(generalMeanRows 281).error 4 := by
  have he : (generalMeanRows 281).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 281) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 281)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0281

/-! Kernel-checked entropy margins for general spectral rectangle 282. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0282
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4820918486) (.branch 2 (.leaf 4645780812) (.leaf 4478710908))) (.branch 5 (.branch 4 (.leaf 4319244889) (.leaf 4166951655)) (.branch 6 (.leaf 4021430031) (.leaf 3882306219)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3749231519) (.leaf 3621880273)) (.branch 10 (.leaf 3499948029) (.leaf 3383149870))) (.branch 13 (.branch 12 (.leaf 3271218911) (.leaf 3163904934)) (.branch 14 (.leaf 3060973143) (.leaf 2962203040))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2867387389) (.branch 17 (.leaf 2776331277) (.leaf 2688851249))) (.branch 20 (.branch 19 (.leaf 2604774518) (.leaf 2523938238)) (.branch 21 (.leaf 2446188835) (.leaf 2371381392)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2299379081) (.leaf 2230052638)) (.branch 25 (.leaf 2163279879) (.leaf 2098945248))) (.branch 28 (.branch 27 (.leaf 2036939405) (.leaf 1977158837)) (.branch 29 (.leaf 1919505501) (.leaf 1863886491)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1810213727) (.branch 32 (.leaf 1758403668) (.leaf 1708377040))) (.branch 35 (.branch 34 (.leaf 1660058590) (.leaf 1613376847)) (.branch 36 (.leaf 1568263907) (.leaf 1524655227)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1482489434) (.leaf 1441708146)) (.branch 40 (.leaf 1402255807) (.leaf 1364079524))) (.branch 43 (.branch 42 (.leaf 1327128928) (.leaf 1291356030)) (.branch 44 (.leaf 1256715092) (.leaf 1223162508))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1190656689) (.branch 47 (.leaf 1159157955) (.leaf 1128628431))) (.branch 50 (.branch 49 (.leaf 1099031958) (.leaf 1070334000)) (.branch 51 (.leaf 1042501560) (.leaf 1015503099)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 989308467) (.leaf 963888824)) (.branch 55 (.leaf 939216582) (.leaf 915265336))) (.branch 58 (.branch 57 (.leaf 892009808) (.leaf 869425791)) (.branch 59 (.leaf 847490095) (.leaf 826180497))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 805475696) (.branch 62 (.leaf 785355264) (.leaf 765799611))) (.branch 65 (.branch 64 (.leaf 746789937) (.leaf 728308200)) (.branch 66 (.leaf 710337079) (.leaf 692859939)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 675860799) (.leaf 659324302)) (.branch 70 (.leaf 643235689) (.leaf 627580767))) (.branch 73 (.branch 72 (.leaf 612345885) (.leaf 597517911)) (.branch 74 (.leaf 583084207) (.leaf 569032608))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 555351401) (.branch 77 (.leaf 542029302) (.leaf 529055443))) (.branch 80 (.branch 79 (.leaf 516419349) (.leaf 504110922)) (.branch 81 (.leaf 492120428) (.leaf 480438475)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 469056006) (.leaf 457964280)) (.branch 85 (.leaf 447154859) (.leaf 436619599))) (.branch 88 (.branch 87 (.leaf 426350631) (.leaf 416340360)) (.branch 89 (.leaf 406581442) (.leaf 397066783)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 387789525) (.branch 92 (.leaf 378743036) (.leaf 369920905))) (.branch 95 (.branch 94 (.leaf 361316927) (.leaf 352925100)) (.branch 96 (.leaf 344739617) (.leaf 336754855)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 328965370) (.leaf 321365890)) (.branch 100 (.leaf 313951310) (.leaf 306716684))) (.branch 103 (.branch 102 (.leaf 299657218) (.leaf 292768266)) (.branch 104 (.leaf 286045326) (.leaf 279484031))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 273080148) (.leaf 266829569)) (.branch 108 (.leaf 260728311) (.leaf 254772507))) (.branch 111 (.branch 110 (.leaf 248958407) (.leaf 243282369)) (.branch 112 (.leaf 237740858) (.leaf 232330442)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 227047788) (.leaf 221889658)) (.branch 116 (.leaf 216852908) (.leaf 211934481))) (.branch 119 (.branch 118 (.leaf 207131410) (.leaf 202440807)) (.branch 120 (.leaf 197859868) (.leaf 193385867)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 282).prefactor = (4894037621675089/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 282).cutoff/(generalMeanRows 282).c)).2 =
    (177382836765551/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 282).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 282).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 282).q*(generalMeanRows 282).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 282).q*(generalMeanRows 282).cutoff/2-2 = (386/183:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable123.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 282).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 282

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 282).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 282).criticalRate j.val*(generalMeanRows 282).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 282).c*(generalMeanRows 282).criticalPoint j.val)).2-
      (generalMeanRows 282).J/2-(generalMeanRows 282).error (generalMeanGrid j.val)+
      (generalMeanRows 282).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 282).c)).2-
      (generalMeanRows 282).J/2-(generalMeanRows 282).error 4 := by
  have he : (generalMeanRows 282).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 282) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 282)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0282

/-! Kernel-checked entropy margins for general spectral rectangle 283. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0283
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4817647877) (.branch 2 (.leaf 4642650495) (.leaf 4475710384))) (.branch 5 (.branch 4 (.leaf 4316364536) (.leaf 4164182655)) (.branch 6 (.leaf 4018764304) (.leaf 3879736359)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3746750739) (.leaf 3619482356)) (.branch 10 (.leaf 3497627277) (.leaf 3380901062))) (.branch 13 (.branch 12 (.leaf 3269037267) (.leaf 3161786072)) (.branch 14 (.leaf 3058913054) (.leaf 2960198051))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2865434137) (.branch 17 (.leaf 2774426683) (.leaf 2686992496))) (.branch 20 (.branch 19 (.leaf 2602959027) (.leaf 2522163649)) (.branch 21 (.leaf 2444452989) (.leaf 2369682314)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2297714962) (.leaf 2228421825)) (.branch 25 (.leaf 2161680857) (.leaf 2097376633))) (.branch 28 (.branch 27 (.leaf 2035399929) (.leaf 1975647340)) (.branch 29 (.leaf 1918020921) (.leaf 1862427854)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1808780141) (.branch 32 (.leaf 1756994314) (.leaf 1706991168))) (.branch 35 (.branch 34 (.leaf 1658695509) (.leaf 1612035924)) (.branch 36 (.leaf 1566944559) (.leaf 1523356915)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1481211662) (.leaf 1440450455)) (.branch 40 (.leaf 1401017771) (.leaf 1362860749))) (.branch 43 (.branch 42 (.leaf 1325929047) (.leaf 1290174699)) (.branch 44 (.leaf 1255551992) (.leaf 1222017339))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1189529168) (.branch 47 (.leaf 1158047815) (.leaf 1127535420))) (.branch 50 (.branch 49 (.leaf 1097955837) (.leaf 1069274541)) (.branch 51 (.leaf 1041458543) (.leaf 1014476316)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 988297714) (.leaf 962893908)) (.branch 55 (.leaf 938237313) (.leaf 914301530))) (.branch 58 (.branch 57 (.leaf 891061287) (.leaf 868492378)) (.branch 59 (.leaf 846571619) (.leaf 825276788))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 804586587) (.branch 62 (.leaf 784480592) (.leaf 764939212))) (.branch 65 (.branch 64 (.leaf 745943650) (.leaf 727475866)) (.branch 66 (.leaf 709518538) (.leaf 692055033)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 675069371) (.leaf 658546195)) (.branch 70 (.leaf 642470746) (.leaf 626828832))) (.branch 73 (.branch 72 (.leaf 611606803) (.leaf 596791526)) (.branch 74 (.leaf 582370364) (.leaf 568331153))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 554662178) (.branch 77 (.leaf 541352157) (.leaf 528390221))) (.branch 80 (.branch 79 (.leaf 515765896) (.leaf 503469085)) (.branch 81 (.leaf 491490052) (.leaf 479819407)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 468448093) (.leaf 457367369)) (.branch 85 (.leaf 446568799) (.leaf 436044236))) (.branch 88 (.branch 87 (.leaf 425785816) (.leaf 415785940)) (.branch 89 (.leaf 406037268) (.leaf 396532706)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 387265395) (.branch 92 (.leaf 378228706) (.leaf 369416227))) (.branch 95 (.branch 94 (.leaf 360821755) (.leaf 352439289)) (.branch 96 (.leaf 344263021) (.leaf 336287330)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 328506774) (.leaf 320916082)) (.branch 100 (.leaf 313510150) (.leaf 306284031))) (.branch 103 (.branch 102 (.leaf 299232934) (.leaf 292352215)) (.branch 104 (.leaf 285637371) (.leaf 279084039))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 272687984) (.leaf 266445102)) (.branch 108 (.leaf 260351409) (.leaf 254403043))) (.branch 111 (.branch 110 (.leaf 248596252) (.leaf 242927396)) (.branch 112 (.leaf 237392943) (.leaf 231989461)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 226713619) (.leaf 221562180)) (.branch 116 (.leaf 216532002) (.leaf 211620030))) (.branch 119 (.branch 118 (.leaf 206823297) (.leaf 202138917)) (.branch 120 (.leaf 197564089) (.leaf 193096086)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 283).prefactor = (977197247949593/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 283).cutoff/(generalMeanRows 283).c)).2 =
    (177010397269747/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 283).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 283).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 283).q*(generalMeanRows 283).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 283).q*(generalMeanRows 283).cutoff/2-2 = (8486/4029:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable125.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 283).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 283

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 283).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 283).criticalRate j.val*(generalMeanRows 283).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 283).c*(generalMeanRows 283).criticalPoint j.val)).2-
      (generalMeanRows 283).J/2-(generalMeanRows 283).error (generalMeanGrid j.val)+
      (generalMeanRows 283).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 283).c)).2-
      (generalMeanRows 283).J/2-(generalMeanRows 283).error 4 := by
  have he : (generalMeanRows 283).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 283) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 283)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0283

/-! Kernel-checked entropy margins for general spectral rectangle 284. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0284
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4821880592) (.branch 2 (.leaf 4646729460) (.leaf 4479642678))) (.branch 5 (.branch 4 (.leaf 4320156831) (.leaf 4167841246)) (.branch 6 (.leaf 4022295132) (.leaf 3883145039)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3750042580) (.leaf 3622662381)) (.branch 10 (.leaf 3500700241) (.leaf 3383871473))) (.branch 13 (.branch 12 (.leaf 3271909395) (.leaf 3164563972)) (.branch 14 (.leaf 3061600571) (.leaf 2962798837))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2867951666) (.branch 17 (.leaf 2776864254) (.leaf 2689353249))) (.branch 20 (.branch 19 (.leaf 2605245949) (.leaf 2524379586)) (.branch 21 (.leaf 2446600650) (.leaf 2371764282)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2299733701) (.leaf 2230379684)) (.branch 25 (.leaf 2163580079) (.leaf 2099219358))) (.branch 28 (.branch 27 (.leaf 2037188202) (.leaf 1977383115)) (.branch 29 (.leaf 1919706066) (.leaf 1864064156)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1810369309) (.branch 32 (.leaf 1758537983) (.leaf 1708490905))) (.branch 35 (.branch 34 (.leaf 1660152815) (.leaf 1613452236)) (.branch 36 (.leaf 1568321253) (.leaf 1524695314)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1482513033) (.leaf 1441716014)) (.branch 40 (.leaf 1402248685) (.leaf 1364058139))) (.branch 43 (.branch 42 (.leaf 1327093989) (.leaf 1291308228)) (.branch 44 (.leaf 1256655102) (.leaf 1223090986))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1190574271) (.branch 47 (.leaf 1159065259) (.leaf 1128526057))) (.branch 50 (.branch 49 (.leaf 1098920486) (.leaf 1070213990)) (.branch 51 (.leaf 1042373553) (.leaf 1015367620)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 989166018) (.leaf 963739892)) (.branch 55 (.leaf 939061634) (.leaf 915104822))) (.branch 58 (.branch 57 (.leaf 891844160) (.leaf 869255423)) (.branch 59 (.leaf 847315404) (.leaf 826001865))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 805293486) (.branch 62 (.leaf 785169826) (.leaf 765611277))) (.branch 65 (.branch 64 (.leaf 746599026) (.leaf 728115016)) (.branch 66 (.leaf 710141911) (.leaf 692663063)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 675662477) (.leaf 659124784)) (.branch 70 (.leaf 643035212) (.leaf 627379555))) (.branch 73 (.branch 72 (.leaf 612144152) (.leaf 597315858)) (.branch 74 (.leaf 582882027) (.leaf 568830480))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 555149496) (.branch 77 (.leaf 541827781) (.leaf 528854457))) (.branch 80 (.branch 79 (.leaf 516219041) (.leaf 503911425)) (.branch 81 (.leaf 491921868) (.leaf 480240969)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 468859665) (.leaf 457769206)) (.branch 85 (.leaf 446961147) (.leaf 436427338))) (.branch 88 (.branch 87 (.leaf 426159905) (.leaf 416151244)) (.branch 89 (.leaf 406394007) (.leaf 396881094)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 387605641) (.branch 92 (.leaf 378561013) (.leaf 369740791))) (.branch 95 (.branch 94 (.leaf 361138768) (.leaf 352748937)) (.branch 96 (.leaf 344565486) (.leaf 336582788)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 328795396) (.leaf 321198035)) (.branch 100 (.leaf 313785595) (.leaf 306553128))) (.branch 103 (.branch 102 (.leaf 299495836) (.leaf 292609071)) (.branch 104 (.leaf 285888328) (.leaf 279329238))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 272927564) (.leaf 266679196)) (.branch 108 (.leaf 260580150) (.leaf 254626558))) (.branch 111 (.branch 110 (.leaf 248814665) (.leaf 243140829)) (.branch 112 (.leaf 237601513) (.leaf 232193284)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 226912806) (.leaf 221756842)) (.branch 116 (.leaf 216722244) (.leaf 211805956))) (.branch 119 (.branch 118 (.leaf 207005009) (.leaf 202316514)) (.branch 120 (.leaf 197737666) (.leaf 193265738)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 284).prefactor = (4890278996228833/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 284).cutoff/(generalMeanRows 284).c)).2 =
    (177010397269747/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 284).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 284).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 284).q*(generalMeanRows 284).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 284).q*(generalMeanRows 284).cutoff/2-2 = (8486/4029:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable125.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 284).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 284

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 284).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 284).criticalRate j.val*(generalMeanRows 284).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 284).c*(generalMeanRows 284).criticalPoint j.val)).2-
      (generalMeanRows 284).J/2-(generalMeanRows 284).error (generalMeanGrid j.val)+
      (generalMeanRows 284).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 284).c)).2-
      (generalMeanRows 284).J/2-(generalMeanRows 284).error 4 := by
  have he : (generalMeanRows 284).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 284) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 284)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0284

/-! Kernel-checked entropy margins for general spectral rectangle 285. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0285
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4747418252) (.branch 2 (.leaf 4572730448) (.leaf 4406115788))) (.branch 5 (.branch 4 (.leaf 4247110700) (.leaf 4095284323)) (.branch 6 (.leaf 3950235660) (.leaf 3811591032)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3679001802) (.leaf 3552142336)) (.branch 10 (.leaf 3430708157) (.leaf 3314414291))) (.branch 13 (.branch 12 (.leaf 3202993761) (.leaf 3096196228)) (.branch 14 (.leaf 2993786751) (.leaf 2895544662))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2801262538) (.branch 17 (.leaf 2710745261) (.leaf 2623809155))) (.branch 20 (.branch 19 (.leaf 2540281203) (.leaf 2459998315)) (.branch 21 (.leaf 2382806667) (.leaf 2308561085)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2237124479) (.leaf 2168367317)) (.branch 25 (.leaf 2102167144) (.leaf 2038408135))) (.branch 28 (.branch 27 (.leaf 1976980678) (.leaf 1917780989)) (.branch 29 (.leaf 1860710753) (.leaf 1805676798)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1752590776) (.branch 32 (.leaf 1701368884) (.leaf 1651931590))) (.branch 35 (.branch 34 (.leaf 1604203385) (.leaf 1558112547)) (.branch 36 (.leaf 1513590928) (.leaf 1470573743)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1428999385) (.leaf 1388809242)) (.branch 40 (.leaf 1349947535) (.leaf 1312361154))) (.branch 43 (.branch 42 (.leaf 1275999517) (.leaf 1240814430)) (.branch 44 (.leaf 1206759958) (.leaf 1173792302))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1141869686) (.branch 47 (.leaf 1110952249) (.leaf 1081001946))) (.branch 50 (.branch 49 (.leaf 1051982449) (.leaf 1023859061)) (.branch 51 (.leaf 996598631) (.leaf 970169473)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 944541292) (.leaf 919685115)) (.branch 55 (.leaf 895573223) (.leaf 872179087))) (.branch 58 (.branch 57 (.leaf 849477311) (.leaf 827443575)) (.branch 59 (.leaf 806054582) (.leaf 785288007))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 765122453) (.branch 62 (.leaf 745537402) (.leaf 726513176))) (.branch 65 (.branch 64 (.leaf 708030897) (.leaf 690072445)) (.branch 66 (.leaf 672620429) (.leaf 655658145)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 639169552) (.leaf 623139236)) (.branch 70 (.leaf 607552382) (.leaf 592394748))) (.branch 73 (.branch 72 (.leaf 577652639) (.leaf 563312880)) (.branch 74 (.leaf 549362797) (.leaf 535790190))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 522583313) (.branch 77 (.leaf 509730859) (.leaf 497221933))) (.branch 80 (.branch 79 (.leaf 485046039) (.leaf 473193064)) (.branch 81 (.leaf 461653255) (.leaf 450417212)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 439475867) (.leaf 428820473)) (.branch 85 (.leaf 418442587) (.leaf 408334063))) (.branch 88 (.branch 87 (.leaf 398487036) (.leaf 388893910)) (.branch 89 (.leaf 379547348) (.leaf 370440263)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 361565807) (.branch 92 (.leaf 352917358) (.leaf 344488517))) (.branch 95 (.branch 94 (.leaf 336273096) (.leaf 328265108)) (.branch 96 (.leaf 320458764) (.leaf 312848459)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 305428772) (.leaf 298194453)) (.branch 100 (.leaf 291140419) (.leaf 284261750))) (.branch 103 (.branch 102 (.leaf 277553676) (.leaf 271011581)) (.branch 104 (.leaf 264630988) (.leaf 258407561))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 252337095) (.leaf 246415515)) (.branch 108 (.leaf 240638867) (.leaf 235003320))) (.branch 111 (.branch 110 (.leaf 229505155) (.leaf 224140763)) (.branch 112 (.leaf 218906645) (.leaf 213799404)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 208815741) (.leaf 203952456)) (.branch 116 (.leaf 199206440) (.leaf 194574675))) (.branch 119 (.branch 118 (.leaf 190054229) (.leaf 185642253)) (.branch 120 (.leaf 181335981) (.leaf 177132725)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 285).prefactor = (305675419952237/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 285).cutoff/(generalMeanRows 285).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 285).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 285).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 285).q*(generalMeanRows 285).c/2-2 = (113/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable124.value]
    have hcontinuation : (generalMeanRows 285).q*(generalMeanRows 285).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 285).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 285

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 285).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 285).criticalRate j.val*(generalMeanRows 285).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 285).c*(generalMeanRows 285).criticalPoint j.val)).2-
      (generalMeanRows 285).J/2-(generalMeanRows 285).error (generalMeanGrid j.val)+
      (generalMeanRows 285).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 285).c)).2-
      (generalMeanRows 285).J/2-(generalMeanRows 285).error 4 := by
  have he : (generalMeanRows 285).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 285) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 285)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0285

/-! Kernel-checked entropy margins for general spectral rectangle 286. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0286
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4751597746) (.branch 2 (.leaf 4576756153) (.leaf 4409994810))) (.branch 5 (.branch 4 (.leaf 4250849738) (.leaf 4098889698)) (.branch 6 (.leaf 3953713338) (.leaf 3814946650)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3682240693) (.leaf 3555269543)) (.branch 10 (.leaf 3433728457) (.leaf 3317332209))) (.branch 13 (.branch 12 (.leaf 3205813588) (.leaf 3098922033)) (.branch 14 (.leaf 2996422397) (.leaf 2898093819))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2803728692) (.branch 17 (.leaf 2713131726) (.leaf 2626119084))) (.branch 20 (.branch 19 (.leaf 2542517595) (.leaf 2462164029)) (.branch 21 (.leaf 2384904424) (.leaf 2310593478)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2239093981) (.leaf 2170276287)) (.branch 25 (.leaf 2104017833) (.leaf 2040202693))) (.branch 28 (.branch 27 (.leaf 1978721157) (.leaf 1919469350)) (.branch 29 (.leaf 1862348871) (.leaf 1807266465)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1754133708) (.branch 32 (.leaf 1702866722) (.leaf 1653385905))) (.branch 35 (.branch 34 (.leaf 1605615681) (.leaf 1559484266)) (.branch 36 (.leaf 1514923451) (.leaf 1471868395)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1430257436) (.leaf 1390031911)) (.branch 40 (.leaf 1351135991) (.leaf 1313516520))) (.branch 43 (.branch 42 (.leaf 1277122871) (.leaf 1241906809)) (.branch 44 (.leaf 1207822356) (.leaf 1174825676))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1142874956) (.branch 47 (.leaf 1111930301) (.leaf 1081953630))) (.branch 50 (.branch 49 (.leaf 1052908585) (.leaf 1024760438)) (.branch 51 (.leaf 997476009) (.leaf 971023583)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 945372840) (.leaf 920494780)) (.branch 55 (.leaf 896361661) (.leaf 872946929))) (.branch 58 (.branch 57 (.leaf 850225167) (.leaf 828172034)) (.branch 59 (.leaf 806764210) (.leaf 785979353))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 765796045) (.branch 62 (.leaf 746193752) (.leaf 727152778))) (.branch 65 (.branch 64 (.leaf 708654228) (.leaf 690679966)) (.branch 66 (.leaf 673212585) (.leaf 656235368)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 639732259) (.leaf 623687830)) (.branch 70 (.leaf 608087254) (.leaf 592916276))) (.branch 73 (.branch 72 (.leaf 578161188) (.leaf 563808805)) (.branch 74 (.leaf 549846441) (.leaf 536261885))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 523043381) (.branch 77 (.leaf 510179612) (.leaf 497659673))) (.branch 80 (.branch 79 (.leaf 485473060) (.leaf 473609650)) (.branch 81 (.leaf 462059682) (.leaf 450813747)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 439862770) (.leaf 429197994)) (.branch 85 (.leaf 418810972) (.leaf 408693549))) (.branch 88 (.branch 87 (.leaf 398837853) (.leaf 389236281)) (.branch 89 (.leaf 379881491) (.leaf 370766389)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 361884119) (.branch 92 (.leaf 353228057) (.leaf 344791795))) (.branch 95 (.branch 94 (.leaf 336569142) (.leaf 328554104)) (.branch 96 (.leaf 320740887) (.leaf 313123883)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 305697663) (.leaf 298456975)) (.branch 100 (.leaf 291396731) (.leaf 284512006))) (.branch 103 (.branch 102 (.leaf 277798027) (.leaf 271250172)) (.branch 104 (.leaf 264863962) (.leaf 258635055))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 252559245) (.leaf 246632452)) (.branch 108 (.leaf 240850719) (.leaf 235210211))) (.branch 111 (.branch 110 (.leaf 229707205) (.leaf 224338090)) (.branch 112 (.leaf 219099365) (.leaf 213987627)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 208999577) (.leaf 204132010)) (.branch 116 (.leaf 199381816) (.leaf 194745973))) (.branch 119 (.branch 118 (.leaf 190221547) (.leaf 185805687)) (.branch 120 (.leaf 181495624) (.leaf 177288668)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 286).prefactor = (305944528088669/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 286).cutoff/(generalMeanRows 286).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 286).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 286).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 286).q*(generalMeanRows 286).c/2-2 = (113/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable124.value]
    have hcontinuation : (generalMeanRows 286).q*(generalMeanRows 286).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 286).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 286

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 286).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 286).criticalRate j.val*(generalMeanRows 286).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 286).c*(generalMeanRows 286).criticalPoint j.val)).2-
      (generalMeanRows 286).J/2-(generalMeanRows 286).error (generalMeanGrid j.val)+
      (generalMeanRows 286).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 286).c)).2-
      (generalMeanRows 286).J/2-(generalMeanRows 286).error 4 := by
  have he : (generalMeanRows 286).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 286) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 286)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0286

/-! Kernel-checked entropy margins for general spectral rectangle 287. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0287
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4759967778) (.branch 2 (.leaf 4584818198) (.leaf 4417763101))) (.branch 5 (.branch 4 (.leaf 4258337692) (.leaf 4106109971)) (.branch 6 (.leaf 3960677881) (.leaf 3821666753)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3688727031) (.leaf 3561532219)) (.branch 10 (.leaf 3439777036) (.leaf 3323175754))) (.branch 13 (.branch 12 (.leaf 3211460690) (.leaf 3104380844)) (.branch 14 (.leaf 3001700654) (.leaf 2903198868))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2808667515) (.branch 17 (.leaf 2717910960) (.leaf 2630745044))) (.branch 20 (.branch 19 (.leaf 2546996290) (.leaf 2466501178)) (.branch 21 (.leaf 2389105479) (.leaf 2314663634)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2243038189) (.leaf 2174099271)) (.branch 25 (.leaf 2107724102) (.leaf 2043796550))) (.branch 28 (.branch 27 (.leaf 1982206713) (.leaf 1922850532)) (.branch 29 (.leaf 1865629435) (.leaf 1810450000)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1757223649) (.branch 32 (.leaf 1705866355) (.leaf 1656298376))) (.branch 35 (.branch 34 (.leaf 1608444004) (.leaf 1562231328)) (.branch 36 (.leaf 1517592018) (.leaf 1474461120)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1432776862) (.leaf 1392480480)) (.branch 40 (.leaf 1353516043) (.leaf 1315830305))) (.branch 43 (.branch 42 (.leaf 1279372548) (.leaf 1244094452)) (.branch 44 (.leaf 1209949958) (.leaf 1176895154))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1144888152) (.branch 47 (.leaf 1113888987) (.leaf 1083859512))) (.branch 50 (.branch 49 (.leaf 1054763304) (.leaf 1026565574)) (.branch 51 (.leaf 999233082) (.leaf 972734060)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 947038132) (.leaf 922116250)) (.branch 55 (.leaf 897940619) (.leaf 874484642))) (.branch 58 (.branch 57 (.leaf 851722856) (.leaf 829630875)) (.branch 59 (.leaf 808185341) (.leaf 787363871))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 767145010) (.branch 62 (.leaf 747508187) (.leaf 728433672))) (.branch 65 (.branch 64 (.leaf 709902536) (.leaf 691896612)) (.branch 66 (.leaf 674398462) (.leaf 657391340)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 640859160) (.leaf 624786469)) (.branch 70 (.leaf 609158412) (.leaf 593960709))) (.branch 73 (.branch 72 (.leaf 579179630) (.leaf 564801966)) (.branch 74 (.leaf 550815006) (.leaf 537206520))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 523964732) (.branch 77 (.leaf 511078303) (.leaf 498536310))) (.branch 80 (.branch 79 (.leaf 486328231) (.leaf 474443922)) (.branch 81 (.leaf 462873609) (.leaf 451607864)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 440637597) (.leaf 429954035)) (.branch 85 (.leaf 419548716) (.leaf 409413471))) (.branch 88 (.branch 87 (.leaf 399540414) (.leaf 389921928)) (.branch 89 (.leaf 380550659) (.leaf 371419501)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 362521585) (.branch 92 (.leaf 353850275) (.leaf 345399153))) (.branch 95 (.branch 94 (.leaf 337162015) (.leaf 329132858)) (.branch 96 (.leaf 321305878) (.leaf 313675456)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 306236156) (.leaf 298982713)) (.branch 100 (.leaf 291910032) (.leaf 285013179))) (.branch 103 (.branch 102 (.leaf 278287373) (.leaf 271727984)) (.branch 104 (.leaf 265330525) (.leaf 259090646))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 253004133) (.leaf 247066900)) (.branch 108 (.leaf 241274982) (.leaf 235624538))) (.branch 111 (.branch 110 (.leaf 230111838) (.leaf 224733266)) (.branch 112 (.leaf 219485312) (.leaf 214364570)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 209367734) (.leaf 204491593)) (.branch 116 (.leaf 199733031) (.leaf 195089022))) (.branch 119 (.branch 118 (.leaf 190556626) (.leaf 186132988)) (.branch 120 (.leaf 181815333) (.leaf 177600965)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 287).prefactor = (1225933821264233/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 287).cutoff/(generalMeanRows 287).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 287).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 287).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 287).q*(generalMeanRows 287).c/2-2 = (113/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable124.value]
    have hcontinuation : (generalMeanRows 287).q*(generalMeanRows 287).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 287).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 287

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 287).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 287).criticalRate j.val*(generalMeanRows 287).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 287).c*(generalMeanRows 287).criticalPoint j.val)).2-
      (generalMeanRows 287).J/2-(generalMeanRows 287).error (generalMeanGrid j.val)+
      (generalMeanRows 287).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 287).c)).2-
      (generalMeanRows 287).J/2-(generalMeanRows 287).error 4 := by
  have he : (generalMeanRows 287).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 287) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 287)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0287

/-! Kernel-checked entropy margins for general spectral rectangle 288. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0288
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5320411858) (.branch 2 (.leaf 5153660274) (.leaf 4994362616))) (.branch 5 (.branch 4 (.leaf 4842082075) (.leaf 4696413223)) (.branch 6 (.leaf 4556979279) (.leaf 4423429652)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4295437755) (.leaf 4172699027)) (.branch 10 (.leaf 4054929165) (.leaf 3941862517))) (.branch 13 (.branch 12 (.leaf 3833250637) (.leaf 3728860964)) (.branch 14 (.leaf 3628475628) (.leaf 3531890367))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3438913523) (.branch 17 (.leaf 3349365145) (.leaf 3263076150))) (.branch 20 (.branch 19 (.leaf 3179887562) (.leaf 3099649817)) (.branch 21 (.leaf 3022222111) (.leaf 2947471815)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2875273922) (.leaf 2805510548)) (.branch 25 (.leaf 2738070461) (.leaf 2672848652))) (.branch 28 (.branch 27 (.leaf 2609745935) (.leaf 2548668576)) (.branch 29 (.leaf 2489527950) (.leaf 2432240220)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2376726045) (.branch 32 (.leaf 2322910297) (.leaf 2270721811))) (.branch 35 (.branch 34 (.leaf 2220093138) (.leaf 2170960330)) (.branch 36 (.leaf 2123262726) (.leaf 2076942759)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2031945776) (.leaf 1988219865)) (.branch 40 (.leaf 1945715700) (.leaf 1904386390))) (.branch 43 (.branch 42 (.leaf 1864187340) (.leaf 1825076123)) (.branch 44 (.leaf 1787012353) (.leaf 1749957577))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1713875164) (.branch 47 (.leaf 1678730202) (.leaf 1644489409))) (.branch 50 (.branch 49 (.leaf 1611121039) (.leaf 1578594802)) (.branch 51 (.leaf 1546881785) (.leaf 1515954375)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1485786194) (.leaf 1456352032)) (.branch 55 (.leaf 1427627782) (.leaf 1399590390))) (.branch 58 (.branch 57 (.leaf 1372217793) (.leaf 1345488871)) (.branch 59 (.leaf 1319383398) (.leaf 1293881997))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1268966096) (.branch 62 (.leaf 1244617888) (.leaf 1220820292))) (.branch 65 (.branch 64 (.leaf 1197556917) (.leaf 1174812028)) (.branch 66 (.leaf 1152570516) (.leaf 1130817861)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1109540112) (.leaf 1088723852)) (.branch 70 (.leaf 1068356177) (.leaf 1048424670))) (.branch 73 (.branch 72 (.leaf 1028917379) (.leaf 1009822793)) (.branch 74 (.leaf 991129822) (.leaf 972827780))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 954906364) (.branch 77 (.leaf 937355637) (.leaf 920166012))) (.branch 80 (.branch 79 (.leaf 903328236) (.leaf 886833372)) (.branch 81 (.leaf 870672793) (.leaf 854838159)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 839321410) (.leaf 824114753)) (.branch 85 (.leaf 809210650) (.leaf 794601807))) (.branch 88 (.branch 87 (.leaf 780281163) (.leaf 766241883)) (.branch 89 (.leaf 752477344) (.leaf 738981133)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 725747029) (.branch 92 (.leaf 712769005) (.leaf 700041214))) (.branch 95 (.branch 94 (.leaf 687557983) (.leaf 675313807)) (.branch 96 (.leaf 663303343) (.leaf 651521401)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 639962943) (.leaf 628623069)) (.branch 100 (.leaf 617497022) (.leaf 606580175))) (.branch 103 (.branch 102 (.leaf 595868028) (.leaf 585356205)) (.branch 104 (.leaf 575040449) (.leaf 564916616))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 554980673) (.leaf 545228692)) (.branch 108 (.leaf 535656849) (.leaf 526261418))) (.branch 111 (.branch 110 (.leaf 517038769) (.leaf 507985363)) (.branch 112 (.leaf 499097752) (.leaf 490372573)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 481806546) (.leaf 473396472)) (.branch 116 (.leaf 465139231) (.leaf 457031777))) (.branch 119 (.branch 118 (.leaf 449071137) (.leaf 441254410)) (.branch 120 (.leaf 433578762) (.leaf 426041427)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 288).prefactor = (4650376221336851/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 288).cutoff/(generalMeanRows 288).c)).2 =
    (223363845847411/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 288).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 288).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 288).q*(generalMeanRows 288).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 288).q*(generalMeanRows 288).cutoff/2-2 = (1055/483:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable127.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 288).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 288

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 288).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 288).criticalRate j.val*(generalMeanRows 288).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 288).c*(generalMeanRows 288).criticalPoint j.val)).2-
      (generalMeanRows 288).J/2-(generalMeanRows 288).error (generalMeanGrid j.val)+
      (generalMeanRows 288).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 288).c)).2-
      (generalMeanRows 288).J/2-(generalMeanRows 288).error 4 := by
  have he : (generalMeanRows 288).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 288) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 288)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0288

/-! Kernel-checked entropy margins for general spectral rectangle 289. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0289
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4896536523) (.branch 2 (.leaf 4720898938) (.leaf 4553342803))) (.branch 5 (.branch 4 (.leaf 4393401648) (.leaf 4240642067)) (.branch 6 (.leaf 4094660835) (.leaf 3955082338)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3821556271) (.leaf 3693755564)) (.branch 10 (.leaf 3571374526) (.leaf 3454127163))) (.branch 13 (.branch 12 (.leaf 3341745655) (.leaf 3233978980)) (.branch 14 (.leaf 3130591658) (.leaf 3031362614))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2936084130) (.branch 17 (.leaf 2844560903) (.leaf 2756609163))) (.branch 20 (.branch 19 (.leaf 2672055883) (.leaf 2590738039)) (.branch 21 (.leaf 2512501937) (.leaf 2437202595)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2364703160) (.leaf 2294874390)) (.branch 25 (.leaf 2227594155) (.leaf 2162746989))) (.branch 28 (.branch 27 (.leaf 2100223668) (.leaf 2039920822)) (.branch 29 (.leaf 1981740570) (.leaf 1925590189)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1871381799) (.branch 32 (.leaf 1819032068) (.leaf 1768461949))) (.branch 35 (.branch 34 (.leaf 1719596420) (.leaf 1672364252)) (.branch 36 (.leaf 1626697787) (.leaf 1582532734)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1539807974) (.leaf 1498465382)) (.branch 40 (.leaf 1458449658) (.leaf 1419708167))) (.branch 43 (.branch 42 (.leaf 1382190796) (.leaf 1345849808)) (.branch 44 (.leaf 1310639720) (.leaf 1276517172))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1243440821) (.branch 47 (.leaf 1211371225) (.leaf 1180270749))) (.branch 50 (.branch 49 (.leaf 1150103461) (.leaf 1120835053)) (.branch 51 (.leaf 1092432746) (.leaf 1064865217)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1038102522) (.leaf 1012116026)) (.branch 55 (.leaf 986878335) (.leaf 962363234))) (.branch 58 (.branch 57 (.leaf 938545629) (.leaf 915401488)) (.branch 59 (.leaf 892907793) (.leaf 871042484))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 849784416) (.branch 62 (.leaf 829113316) (.leaf 809009734))) (.branch 65 (.branch 64 (.leaf 789455013) (.leaf 770431241)) (.branch 66 (.leaf 751921223) (.leaf 733908445)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 716377039) (.leaf 699311760)) (.branch 70 (.leaf 682697948) (.leaf 666521509))) (.branch 73 (.branch 72 (.leaf 650768884) (.leaf 635427028)) (.branch 74 (.leaf 620483384) (.leaf 605925864))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 591742824) (.branch 77 (.leaf 577923050) (.leaf 564455734))) (.branch 80 (.branch 79 (.leaf 551330458) (.leaf 538537180)) (.branch 81 (.leaf 526066211) (.leaf 513908207)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 502054151) (.leaf 490495337)) (.branch 85 (.leaf 479223363) (.leaf 468230113))) (.branch 88 (.branch 87 (.leaf 457507745) (.leaf 447048686)) (.branch 89 (.leaf 436845612) (.leaf 426891445)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 417179341) (.branch 92 (.leaf 407702679) (.leaf 398455054))) (.branch 95 (.branch 94 (.leaf 389430268) (.leaf 380622322)) (.branch 96 (.leaf 372025406) (.leaf 363633898)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 355442348) (.leaf 347445478)) (.branch 100 (.leaf 339638175) (.leaf 332015481))) (.branch 103 (.branch 102 (.leaf 324572589) (.leaf 317304842)) (.branch 104 (.leaf 310207719) (.leaf 303276836))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 296507941) (.leaf 289896906)) (.branch 108 (.leaf 283439725) (.leaf 277132508))) (.branch 111 (.branch 110 (.leaf 270971481) (.leaf 264952976)) (.branch 112 (.leaf 259073432) (.leaf 253329387)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 247717480) (.leaf 242234444)) (.branch 116 (.leaf 236877103) (.leaf 231642370))) (.branch 119 (.branch 118 (.leaf 226527243) (.leaf 221528804)) (.branch 120 (.leaf 216644214) (.leaf 211870711)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 289).prefactor = (491626410043127/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 289).cutoff/(generalMeanRows 289).c)).2 =
    (36690950971171/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 289).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 289).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 289).q*(generalMeanRows 289).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 289).q*(generalMeanRows 289).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable119.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 289).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 289

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 289).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 289).criticalRate j.val*(generalMeanRows 289).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 289).c*(generalMeanRows 289).criticalPoint j.val)).2-
      (generalMeanRows 289).J/2-(generalMeanRows 289).error (generalMeanGrid j.val)+
      (generalMeanRows 289).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 289).c)).2-
      (generalMeanRows 289).J/2-(generalMeanRows 289).error 4 := by
  have he : (generalMeanRows 289).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 289) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 289)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0289

/-! Kernel-checked entropy margins for general spectral rectangle 290. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0290
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4930572411) (.branch 2 (.leaf 4753713966) (.leaf 4584993147))) (.branch 5 (.branch 4 (.leaf 4423940239) (.leaf 4270118824)) (.branch 6 (.leaf 4123122874) (.leaf 3982574166)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3848119957) (.leaf 3719430906)) (.branch 10 (.leaf 3596199196) (.leaf 3478136845))) (.branch 13 (.branch 12 (.leaf 3364974172) (.leaf 3256458409)) (.branch 14 (.leaf 3152352441) (.leaf 3052433654))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2956492889) (.branch 17 (.leaf 2864333482) (.leaf 2775770388))) (.branch 20 (.branch 19 (.leaf 2690629377) (.leaf 2608746292)) (.branch 21 (.leaf 2529966370) (.leaf 2454143621)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2381140242) (.leaf 2310826091)) (.branch 25 (.leaf 2243078190) (.leaf 2177780271))) (.branch 28 (.branch 27 (.leaf 2114822350) (.leaf 2054100337)) (.branch 29 (.leaf 1995515674) (.leaf 1938974991)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1884389797) (.branch 32 (.leaf 1831676183) (.leaf 1780754551))) (.branch 35 (.branch 34 (.leaf 1731549357) (.leaf 1683988877)) (.branch 36 (.leaf 1638004984) (.leaf 1593532939)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1550511199) (.leaf 1508881234)) (.branch 40 (.leaf 1468587360) (.leaf 1429576577))) (.branch 43 (.branch 42 (.leaf 1391798422) (.leaf 1355204828)) (.branch 44 (.leaf 1319749993) (.leaf 1285390260))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1252083994) (.branch 47 (.leaf 1219791482) (.leaf 1188474826))) (.branch 50 (.branch 49 (.leaf 1158097845) (.leaf 1128625991)) (.branch 51 (.leaf 1100026260) (.leaf 1072267108)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1045318386) (.leaf 1019151257)) (.branch 55 (.leaf 993738139) (.leaf 969052633))) (.branch 58 (.branch 57 (.leaf 945069471) (.leaf 921764456)) (.branch 59 (.leaf 899114406) (.leaf 877097111))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 855691279) (.branch 62 (.leaf 834876493) (.leaf 814633171))) (.branch 65 (.branch 64 (.leaf 794942525) (.leaf 775786518)) (.branch 66 (.leaf 757147837) (.leaf 739009851)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 721356585) (.leaf 704172685)) (.branch 70 (.leaf 687443390) (.leaf 671154509))) (.branch 73 (.branch 72 (.leaf 655292387) (.leaf 639843889)) (.branch 74 (.leaf 624796372) (.leaf 610137662))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 595856036) (.branch 77 (.leaf 581940200) (.leaf 568379273))) (.branch 80 (.branch 79 (.leaf 555162763) (.leaf 542280558)) (.branch 81 (.leaf 529722904) (.leaf 517480390)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 505543935) (.leaf 493904777)) (.branch 85 (.leaf 482554451) (.leaf 471484786))) (.branch 88 (.branch 87 (.leaf 460687888) (.leaf 450156127)) (.branch 89 (.leaf 439882131) (.leaf 429858773)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 420079160) (.branch 92 (.leaf 410536625) (.leaf 401224720))) (.branch 95 (.branch 94 (.leaf 392137203) (.leaf 383268032)) (.branch 96 (.leaf 374611360) (.leaf 366161522)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 357913032) (.leaf 349860576)) (.branch 100 (.leaf 341999004) (.leaf 334323324))) (.branch 103 (.branch 102 (.leaf 326828698) (.leaf 319510432)) (.branch 104 (.leaf 312363976) (.leaf 305384917))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 298568971) (.leaf 291911983)) (.branch 108 (.leaf 285409918) (.leaf 279058860))) (.branch 111 (.branch 110 (.leaf 272855008) (.leaf 266794668)) (.branch 112 (.leaf 260874254) (.leaf 255090283)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 249439367) (.leaf 243918219)) (.branch 116 (.leaf 238523639) (.leaf 233252519))) (.branch 119 (.branch 118 (.leaf 228101837) (.leaf 223068653)) (.branch 120 (.leaf 218150110) (.leaf 213343427)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 290).prefactor = (4950437114822699/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 290).cutoff/(generalMeanRows 290).c)).2 =
    (36690950971171/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 290).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 290).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 290).q*(generalMeanRows 290).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 290).q*(generalMeanRows 290).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable119.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 290).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 290

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 290).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 290).criticalRate j.val*(generalMeanRows 290).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 290).c*(generalMeanRows 290).criticalPoint j.val)).2-
      (generalMeanRows 290).J/2-(generalMeanRows 290).error (generalMeanGrid j.val)+
      (generalMeanRows 290).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 290).c)).2-
      (generalMeanRows 290).J/2-(generalMeanRows 290).error 4 := by
  have he : (generalMeanRows 290).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 290) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 290)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0290

/-! Kernel-checked entropy margins for general spectral rectangle 291. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0291
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5262065066) (.branch 2 (.leaf 5094461134) (.leaf 4934370865))) (.branch 5 (.branch 4 (.leaf 4781354586) (.leaf 4635004184)) (.branch 6 (.leaf 4494940349) (.leaf 4360810115)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4232284651) (.leaf 4109057281)) (.branch 10 (.leaf 3990841700) (.leaf 3877370362))) (.branch 13 (.branch 12 (.leaf 3768393023) (.leaf 3663675419)) (.branch 14 (.leaf 3562998062) (.leaf 3466155148))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3372953557) (.branch 17 (.leaf 3283211938) (.leaf 3196759877))) (.branch 20 (.branch 19 (.leaf 3113437127) (.leaf 3033092910)) (.branch 21 (.leaf 2955585261) (.leaf 2880780440)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2808552378) (.leaf 2738782171)) (.branch 25 (.leaf 2671357611) (.leaf 2606172753))) (.branch 28 (.branch 27 (.leaf 2543127512) (.leaf 2482127292)) (.branch 29 (.leaf 2423082638) (.leaf 2365908919)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2310526026) (.branch 32 (.leaf 2256858096) (.leaf 2204833253))) (.branch 35 (.branch 34 (.leaf 2154383368) (.leaf 2105443835)) (.branch 36 (.leaf 2057953361) (.leaf 2011853768)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1967089816) (.leaf 1923609026)) (.branch 40 (.leaf 1881361526) (.leaf 1840299898))) (.branch 43 (.branch 42 (.leaf 1800379039) (.leaf 1761556029)) (.branch 44 (.leaf 1723790012) (.leaf 1687042077))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1651275149) (.branch 47 (.leaf 1616453893) (.leaf 1582544613))) (.branch 50 (.branch 49 (.leaf 1549515169) (.leaf 1517334884)) (.branch 51 (.leaf 1485974475) (.leaf 1455405971)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1425602648) (.leaf 1396538960)) (.branch 55 (.leaf 1368190481) (.leaf 1340533840))) (.branch 58 (.branch 57 (.leaf 1313546675) (.leaf 1287207574)) (.branch 59 (.leaf 1261496029) (.leaf 1236392391))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1211877824) (.branch 62 (.leaf 1187934269) (.leaf 1164544397))) (.branch 65 (.branch 64 (.leaf 1141691581) (.leaf 1119359857)) (.branch 66 (.leaf 1097533894) (.leaf 1076198959)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1055340893) (.leaf 1034946081)) (.branch 70 (.leaf 1015001426) (.leaf 995494325))) (.branch 73 (.branch 72 (.leaf 976412645) (.leaf 957744703)) (.branch 74 (.leaf 939479242) (.leaf 921605414))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 904112760) (.branch 77 (.leaf 886991194) (.leaf 870230982))) (.branch 80 (.branch 79 (.leaf 853822733) (.leaf 837757376)) (.branch 81 (.leaf 822026152) (.leaf 806620597)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 791532531) (.leaf 776754045)) (.branch 85 (.leaf 762277489) (.leaf 748095461))) (.branch 88 (.branch 87 (.leaf 734200797) (.leaf 720586562)) (.branch 89 (.leaf 707246040) (.leaf 694172722)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 681360302) (.branch 92 (.leaf 668802667) (.leaf 656493888))) (.branch 95 (.branch 94 (.leaf 644428215) (.leaf 632600068)) (.branch 96 (.leaf 621004032) (.leaf 609634848)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 598487412) (.leaf 587556763)) (.branch 100 (.leaf 576838081) (.leaf 566326682))) (.branch 103 (.branch 102 (.leaf 556018013) (.leaf 545907645)) (.branch 104 (.leaf 535991270) (.leaf 526264696))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 516723847) (.leaf 507364750)) (.branch 108 (.leaf 498183541) (.leaf 489176455))) (.branch 111 (.branch 110 (.leaf 480339825) (.leaf 471670078)) (.branch 112 (.leaf 463163732) (.leaf 454817394)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 446627754) (.leaf 438591588)) (.branch 116 (.leaf 430705747) (.leaf 422967162))) (.branch 119 (.branch 118 (.leaf 415372838) (.leaf 407919853)) (.branch 120 (.leaf 400605354) (.leaf 393426556)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 291).prefactor = (18724574776919/4000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 291).cutoff/(generalMeanRows 291).c)).2 =
    (438727649027743/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 291).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 291).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 291).q*(generalMeanRows 291).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 291).q*(generalMeanRows 291).cutoff/2-2 = (1055/483:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable127.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 291).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 291

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 291).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 291).criticalRate j.val*(generalMeanRows 291).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 291).c*(generalMeanRows 291).criticalPoint j.val)).2-
      (generalMeanRows 291).J/2-(generalMeanRows 291).error (generalMeanGrid j.val)+
      (generalMeanRows 291).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 291).c)).2-
      (generalMeanRows 291).J/2-(generalMeanRows 291).error 4 := by
  have he : (generalMeanRows 291).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 291) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 291)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0291

/-! Kernel-checked entropy margins for general spectral rectangle 292. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0292
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5296879549) (.branch 2 (.leaf 5128166728) (.leaf 4967017283))) (.branch 5 (.branch 4 (.leaf 4812988629) (.leaf 4665669954)) (.branch 6 (.leaf 4524679439) (.leaf 4389661783)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4260285978) (.leaf 4136243320)) (.branch 10 (.leaf 4017245610) (.leaf 3903023531))) (.branch 13 (.branch 12 (.leaf 3793325184) (.leaf 3687914755)) (.branch 14 (.leaf 3586571305) (.leaf 3489087666))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3395269441) (.branch 17 (.leaf 3304934080) (.leaf 3217910041))) (.branch 20 (.branch 19 (.leaf 3134036018) (.leaf 3053160234)) (.branch 21 (.leaf 2975139784) (.leaf 2899840045)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2827134113) (.leaf 2756902297)) (.branch 25 (.leaf 2689031648) (.leaf 2623415519))) (.branch 28 (.branch 27 (.leaf 2559953163) (.leaf 2498549357)) (.branch 29 (.leaf 2439114057) (.leaf 2381562070)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2325812756) (.branch 32 (.leaf 2271789752) (.leaf 2219420706))) (.branch 35 (.branch 34 (.leaf 2168637039) (.leaf 2119373716)) (.branch 36 (.leaf 2071569038) (.leaf 2025164445)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1980104329) (.leaf 1936335865)) (.branch 40 (.leaf 1893808850) (.leaf 1852475553))) (.branch 43 (.branch 42 (.leaf 1812290573) (.leaf 1773210705)) (.branch 44 (.leaf 1735194824) (.leaf 1698203759))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1662200193) (.branch 47 (.leaf 1627148555) (.leaf 1593014927))) (.branch 50 (.branch 49 (.leaf 1559766955) (.leaf 1527373762)) (.branch 51 (.leaf 1495805869) (.leaf 1465035120)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1435034614) (.leaf 1405778638)) (.branch 55 (.leaf 1377242601) (.leaf 1349402980))) (.branch 58 (.branch 57 (.leaf 1322237265) (.leaf 1295723900)) (.branch 59 (.leaf 1269842245) (.leaf 1244572518))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1219895760) (.branch 62 (.leaf 1195793791) (.leaf 1172249169))) (.branch 65 (.branch 64 (.leaf 1149245156) (.leaf 1126765683)) (.branch 66 (.leaf 1104795316) (.leaf 1083319226)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1062323161) (.leaf 1041793414)) (.branch 70 (.leaf 1021716803) (.leaf 1002080640))) (.branch 73 (.branch 72 (.leaf 982872714) (.leaf 964081262)) (.branch 74 (.leaf 945694954) (.leaf 927702871))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 910094484) (.branch 77 (.leaf 892859639) (.leaf 875988540))) (.branch 80 (.branch 79 (.leaf 859471731) (.leaf 843300084)) (.branch 81 (.leaf 827464780) (.leaf 811957300)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 796769410) (.leaf 781893147)) (.branch 85 (.leaf 767320812) (.leaf 753044954))) (.branch 88 (.branch 87 (.leaf 739058362) (.leaf 725354054)) (.branch 89 (.leaf 711925268) (.leaf 698765456)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 685868267) (.branch 92 (.leaf 673227549) (.leaf 660837334))) (.branch 95 (.branch 94 (.leaf 648691833) (.leaf 636785429)) (.branch 96 (.leaf 625112672) (.leaf 613668269)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 602447080) (.leaf 591444112)) (.branch 100 (.leaf 580654514) (.leaf 570073571))) (.branch 103 (.branch 102 (.leaf 559696698) (.leaf 549519438)) (.branch 104 (.leaf 539537455) (.leaf 529746530))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 520142557) (.leaf 510721539)) (.branch 108 (.leaf 501479586) (.leaf 492412908))) (.branch 111 (.branch 110 (.leaf 483517814) (.leaf 474790706)) (.branch 112 (.leaf 466228081) (.leaf 457826523)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 449582700) (.leaf 441493365)) (.branch 116 (.leaf 433555350) (.leaf 425765566))) (.branch 119 (.branch 118 (.leaf 418120997) (.leaf 410618702)) (.branch 120 (.leaf 403255809) (.leaf 396029515)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 292).prefactor = (2356057364292943/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 292).cutoff/(generalMeanRows 292).c)).2 =
    (438727649027743/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 292).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 292).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 292).q*(generalMeanRows 292).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 292).q*(generalMeanRows 292).cutoff/2-2 = (1055/483:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable127.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 292).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 292

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 292).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 292).criticalRate j.val*(generalMeanRows 292).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 292).c*(generalMeanRows 292).criticalPoint j.val)).2-
      (generalMeanRows 292).J/2-(generalMeanRows 292).error (generalMeanGrid j.val)+
      (generalMeanRows 292).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 292).c)).2-
      (generalMeanRows 292).J/2-(generalMeanRows 292).error 4 := by
  have he : (generalMeanRows 292).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 292) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 292)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0292

/-! Kernel-checked entropy margins for general spectral rectangle 293. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0293
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5534503540) (.branch 2 (.leaf 5358160127) (.leaf 5189766574))) (.branch 5 (.branch 4 (.leaf 5028856093) (.leaf 4874995419)) (.branch 6 (.leaf 4727781891) (.leaf 4586840828)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4451823193) (.leaf 4322403488)) (.branch 10 (.leaf 4198277858) (.leaf 4079162381))) (.branch 13 (.branch 12 (.leaf 3964791521) (.leaf 3854916718)) (.branch 14 (.leaf 3749305117) (.leaf 3647738406))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3550011748) (.branch 17 (.leaf 3455932817) (.leaf 3365320908))) (.branch 20 (.branch 19 (.leaf 3278006125) (.leaf 3193828628)) (.branch 21 (.leaf 3112637952) (.leaf 3034292366)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2958658295) (.leaf 2885609779)) (.branch 25 (.leaf 2815027973) (.leaf 2746800688))) (.branch 28 (.branch 27 (.leaf 2680821962) (.leaf 2616991666)) (.branch 29 (.leaf 2555215136) (.leaf 2495402830)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2437470013) (.branch 32 (.leaf 2381336460) (.leaf 2326926183))) (.branch 35 (.branch 34 (.leaf 2274167174) (.leaf 2222991167)) (.branch 36 (.leaf 2173333414) (.leaf 2125132476)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2078330034) (.leaf 2032870701)) (.branch 40 (.leaf 1988701856) (.leaf 1945773485))) (.branch 43 (.branch 42 (.leaf 1904038031) (.leaf 1863450252)) (.branch 44 (.leaf 1823967099) (.leaf 1785547582))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1748152664) (.branch 47 (.leaf 1711745151) (.leaf 1676289587))) (.branch 50 (.branch 49 (.leaf 1641752163) (.leaf 1608100626)) (.branch 51 (.leaf 1575304198) (.leaf 1543333490)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1512160435) (.leaf 1481758215)) (.branch 55 (.leaf 1452101194) (.leaf 1423164859))) (.branch 58 (.branch 57 (.leaf 1394925758) (.leaf 1367361448)) (.branch 59 (.leaf 1340450444) (.leaf 1314172165))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1288506893) (.branch 62 (.leaf 1263435727) (.leaf 1238940542))) (.branch 65 (.branch 64 (.leaf 1215003953) (.leaf 1191609274)) (.branch 66 (.leaf 1168740486) (.leaf 1146382205)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1124519650) (.leaf 1103138612)) (.branch 70 (.leaf 1082225431) (.leaf 1061766965))) (.branch 73 (.branch 72 (.leaf 1041750571) (.leaf 1022164074)) (.branch 74 (.leaf 1002995752) (.leaf 984234313))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 965868871) (.branch 77 (.leaf 947888934) (.leaf 930284380))) (.branch 80 (.branch 79 (.leaf 913045447) (.leaf 896162710)) (.branch 81 (.leaf 879627069) (.leaf 863429735)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 847562218) (.leaf 832016308)) (.branch 85 (.leaf 816784071) (.leaf 801857830))) (.branch 88 (.branch 87 (.leaf 787230159) (.leaf 772893868)) (.branch 89 (.leaf 758841998) (.leaf 745067808)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 731564767) (.branch 92 (.leaf 718326546) (.leaf 705347008))) (.branch 95 (.branch 94 (.leaf 692620203) (.leaf 680140357)) (.branch 96 (.leaf 667901871) (.leaf 655899305)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 644127382) (.leaf 632580973)) (.branch 100 (.leaf 621255098) (.leaf 610144916))) (.branch 103 (.branch 102 (.leaf 599245722) (.leaf 588552941)) (.branch 104 (.leaf 578062123) (.leaf 567768940))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 557669180) (.leaf 547758743)) (.branch 108 (.leaf 538033639) (.leaf 528489982))) (.branch 111 (.branch 110 (.leaf 519123985) (.leaf 509931961)) (.branch 112 (.leaf 500910316) (.leaf 492055547)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 483364241) (.leaf 474833066)) (.branch 116 (.leaf 466458776) (.leaf 458238204))) (.branch 119 (.branch 118 (.leaf 450168257) (.leaf 442245920)) (.branch 120 (.leaf 434468249) (.leaf 426832369)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 293).prefactor = (1226642807504379/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 293).cutoff/(generalMeanRows 293).c)).2 =
    (442471253950209/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 293).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 293).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 293).q*(generalMeanRows 293).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    have hcontinuation : (generalMeanRows 293).q*(generalMeanRows 293).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 293).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 293

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 293).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 293).criticalRate j.val*(generalMeanRows 293).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 293).c*(generalMeanRows 293).criticalPoint j.val)).2-
      (generalMeanRows 293).J/2-(generalMeanRows 293).error (generalMeanGrid j.val)+
      (generalMeanRows 293).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 293).c)).2-
      (generalMeanRows 293).J/2-(generalMeanRows 293).error 4 := by
  have he : (generalMeanRows 293).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 293) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 293)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0293

/-! Kernel-checked entropy margins for general spectral rectangle 294. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0294
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5571764406) (.branch 2 (.leaf 5394233767) (.leaf 5224706510))) (.branch 5 (.branch 4 (.leaf 5062712704) (.leaf 4907816168)) (.branch 6 (.leaf 4759611529) (.leaf 4617721585)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4481794948) (.leaf 4351503929)) (.branch 10 (.leaf 4226542628) (.leaf 4106625210))) (.branch 13 (.branch 12 (.leaf 3991484351) (.leaf 3880869820)) (.branch 14 (.leaf 3774547193) (.leaf 3672296687))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3573912087) (.branch 17 (.leaf 3479199772) (.leaf 3387977822))) (.branch 20 (.branch 19 (.leaf 3300075195) (.leaf 3215330976)) (.branch 21 (.leaf 3133593686) (.leaf 3054720641)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2978577366) (.leaf 2905037053)) (.branch 25 (.leaf 2833980058) (.leaf 2765293434))) (.branch 28 (.branch 27 (.leaf 2698870509) (.leaf 2634610478)) (.branch 29 (.leaf 2572418039) (.leaf 2512203049)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2453880201) (.branch 32 (.leaf 2397368730) (.leaf 2342592138))) (.branch 35 (.branch 34 (.leaf 2289477931) (.leaf 2237957383)) (.branch 36 (.leaf 2187965311) (.leaf 2139439862)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2092322324) (.leaf 2046556937)) (.branch 40 (.leaf 2002090727) (.leaf 1958873342))) (.branch 43 (.branch 42 (.leaf 1916856905) (.leaf 1875995871)) (.branch 44 (.leaf 1836246898) (.leaf 1797568723))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1759922046) (.branch 47 (.leaf 1723269420) (.leaf 1687575152))) (.branch 50 (.branch 49 (.leaf 1652805206) (.leaf 1618927112)) (.branch 51 (.leaf 1585909882) (.leaf 1553723933)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1522341007) (.leaf 1491734104)) (.branch 55 (.leaf 1461877419) (.leaf 1432746270))) (.branch 58 (.branch 57 (.leaf 1404317050) (.leaf 1376567165)) (.branch 59 (.leaf 1349474983) (.leaf 1323019787))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1297181724) (.branch 62 (.leaf 1271941767) (.leaf 1247281669))) (.branch 65 (.branch 64 (.leaf 1223183928) (.leaf 1199631745)) (.branch 66 (.leaf 1176608994) (.leaf 1154100186)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1132090442) (.leaf 1110565457)) (.branch 70 (.leaf 1089511478) (.leaf 1068915277))) (.branch 73 (.branch 72 (.leaf 1048764123) (.leaf 1029045761)) (.branch 74 (.leaf 1009748389) (.leaf 990860638))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 972371552) (.branch 77 (.leaf 954270565) (.leaf 936547490))) (.branch 80 (.branch 79 (.leaf 919192496) (.leaf 902196096)) (.branch 81 (.leaf 885549129) (.leaf 869242748)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 853268403) (.leaf 837617831)) (.branch 85 (.leaf 822283044) (.leaf 807256312))) (.branch 88 (.branch 87 (.leaf 792530160) (.leaf 778097351)) (.branch 89 (.leaf 763950877) (.leaf 750083953)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 736490003) (.branch 92 (.leaf 723162656) (.leaf 710095734))) (.branch 95 (.branch 94 (.leaf 697283246) (.leaf 684719380)) (.branch 96 (.leaf 672398498) (.leaf 660315126)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 648463949) (.leaf 636839804)) (.branch 100 (.leaf 625437678) (.leaf 614252697))) (.branch 103 (.branch 102 (.leaf 603280124) (.leaf 592515354)) (.branch 104 (.leaf 581953907) (.leaf 571591426))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 561423669) (.leaf 551446511)) (.branch 108 (.leaf 541655933) (.leaf 532048023))) (.branch 111 (.branch 110 (.leaf 522618970) (.leaf 513365061)) (.branch 112 (.leaf 504282678) (.leaf 495368295)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 486618475) (.leaf 478029865)) (.branch 116 (.leaf 469599195) (.leaf 461323277))) (.branch 119 (.branch 118 (.leaf 453199000) (.leaf 445223326)) (.branch 120 (.leaf 437393292) (.leaf 429706005)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 294).prefactor = (4939604562166251/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 294).cutoff/(generalMeanRows 294).c)).2 =
    (442471253950209/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 294).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 294).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 294).q*(generalMeanRows 294).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    have hcontinuation : (generalMeanRows 294).q*(generalMeanRows 294).cutoff/2-2 = (98/45:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable092.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 294).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 294

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 294).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 294).criticalRate j.val*(generalMeanRows 294).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 294).c*(generalMeanRows 294).criticalPoint j.val)).2-
      (generalMeanRows 294).J/2-(generalMeanRows 294).error (generalMeanGrid j.val)+
      (generalMeanRows 294).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 294).c)).2-
      (generalMeanRows 294).J/2-(generalMeanRows 294).error 4 := by
  have he : (generalMeanRows 294).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 294) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 294)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0294

/-! Kernel-checked entropy margins for general spectral rectangle 295. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0295
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5327305011) (.branch 2 (.leaf 5149353583) (.leaf 4979468672))) (.branch 5 (.branch 4 (.leaf 4817180759) (.leaf 4662053849)) (.branch 6 (.leaf 4513682551) (.leaf 4371689463)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4235722829) (.leaf 4105454447)) (.branch 10 (.leaf 3980577766) (.leaf 3860806185))) (.branch 13 (.branch 12 (.leaf 3745871507) (.leaf 3635522533)) (.branch 14 (.leaf 3529523793) (.leaf 3427654380))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3329706898) (.branch 17 (.leaf 3235486488) (.leaf 3144809947))) (.branch 20 (.branch 19 (.leaf 3057504911) (.leaf 2973409112)) (.branch 21 (.leaf 2892369691) (.leaf 2814242566)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2738891848) (.leaf 2666189305)) (.branch 25 (.leaf 2596013860) (.leaf 2528251136))) (.branch 28 (.branch 27 (.leaf 2462793027) (.leaf 2399537303)) (.branch 29 (.leaf 2338387242) (.leaf 2279251289)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2222042742) (.branch 32 (.leaf 2166679451) (.leaf 2113083551))) (.branch 35 (.branch 34 (.leaf 2061181197) (.leaf 2010902333)) (.branch 36 (.leaf 1962180464) (.leaf 1914952451)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1869158314) (.leaf 1824741051)) (.branch 40 (.leaf 1781646467) (.leaf 1739823016))) (.branch 43 (.branch 42 (.leaf 1699221651) (.leaf 1659795683)) (.branch 44 (.leaf 1621500651) (.leaf 1584294200))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1548135961) (.branch 47 (.leaf 1512987449) (.leaf 1478811956))) (.branch 50 (.branch 49 (.leaf 1445574456) (.leaf 1413241517)) (.branch 51 (.leaf 1381781215) (.leaf 1351163054)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1321357891) (.leaf 1292337866)) (.branch 55 (.leaf 1264076337) (.leaf 1236547813))) (.branch 58 (.branch 57 (.leaf 1209727898) (.leaf 1183593235)) (.branch 59 (.leaf 1158121453) (.leaf 1133291118))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1109081684) (.branch 62 (.leaf 1085473453) (.leaf 1062447529))) (.branch 65 (.branch 64 (.leaf 1039985780) (.leaf 1018070802)) (.branch 66 (.leaf 996685883) (.leaf 975814968)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 955442631) (.leaf 935554041)) (.branch 70 (.leaf 916134938) (.leaf 897171604))) (.branch 73 (.branch 72 (.leaf 878650836) (.leaf 860559927)) (.branch 74 (.leaf 842886638) (.leaf 825619181))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 808746195) (.branch 77 (.leaf 792256729) (.leaf 776140222))) (.branch 80 (.branch 79 (.leaf 760386489) (.leaf 744985699)) (.branch 81 (.leaf 729928364) (.leaf 715205324)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 700807728) (.leaf 686727027)) (.branch 85 (.leaf 672954958) (.leaf 659483531))) (.branch 88 (.branch 87 (.leaf 646305020) (.leaf 633411950)) (.branch 89 (.leaf 620797089) (.leaf 608453434)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 596374207) (.branch 92 (.leaf 584552842) (.leaf 572982976))) (.branch 95 (.branch 94 (.leaf 561658446) (.leaf 550573275)) (.branch 96 (.leaf 539721668) (.leaf 529098006)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 518696835) (.leaf 508512865)) (.branch 100 (.leaf 498540960) (.leaf 488776133))) (.branch 103 (.branch 102 (.leaf 479213542) (.leaf 469848482)) (.branch 104 (.leaf 460676384) (.leaf 451692805))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 442893427) (.leaf 434274051)) (.branch 108 (.leaf 425830597) (.leaf 417559090))) (.branch 111 (.branch 110 (.leaf 409455669) (.leaf 401516572)) (.branch 112 (.leaf 393738139) (.leaf 386116808)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 378649108) (.leaf 371331662)) (.branch 116 (.leaf 364161177) (.leaf 357134447))) (.branch 119 (.branch 118 (.leaf 350248346) (.leaf 343499830)) (.branch 120 (.leaf 336885929) (.leaf 330403749)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 295).prefactor = (2472521418539241/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 295).cutoff/(generalMeanRows 295).c)).2 =
    (1030340617313/2500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 295).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 295).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 295).q*(generalMeanRows 295).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 295).q*(generalMeanRows 295).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable118.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 295).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 295

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 295).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 295).criticalRate j.val*(generalMeanRows 295).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 295).c*(generalMeanRows 295).criticalPoint j.val)).2-
      (generalMeanRows 295).J/2-(generalMeanRows 295).error (generalMeanGrid j.val)+
      (generalMeanRows 295).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 295).c)).2-
      (generalMeanRows 295).J/2-(generalMeanRows 295).error 4 := by
  have he : (generalMeanRows 295).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 295) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 295)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0295

/-! Kernel-checked entropy margins for general spectral rectangle 296. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0296
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5458490010) (.branch 2 (.leaf 5278930833) (.leaf 5107484093))) (.branch 5 (.branch 4 (.leaf 4943677079) (.leaf 4787070868)) (.branch 6 (.leaf 4637257372) (.leaf 4493856705)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4356514829) (.leaf 4224901432)) (.branch 10 (.leaf 4098708024) (.leaf 3977646214))) (.branch 13 (.branch 12 (.leaf 3861446152) (.leaf 3749855116)) (.branch 14 (.leaf 3642636230) (.leaf 3539567291))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3440439704) (.branch 17 (.leaf 3345057505) (.leaf 3253236471))) (.branch 20 (.branch 19 (.leaf 3164803298) (.leaf 3079594849)) (.branch 21 (.leaf 2997457465) (.leaf 2918246325)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2841824859) (.leaf 2768064206)) (.branch 25 (.leaf 2696842713) (.leaf 2628045471))) (.branch 28 (.branch 27 (.leaf 2561563883) (.leaf 2497295267)) (.branch 29 (.leaf 2435142488) (.leaf 2375013611)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2316821581) (.branch 32 (.leaf 2260483930) (.leaf 2205922497))) (.branch 35 (.branch 34 (.leaf 2153063168) (.leaf 2101835640)) (.branch 36 (.leaf 2052173193) (.leaf 2004012479)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1957293332) (.leaf 1911958576)) (.branch 40 (.leaf 1867953861) (.leaf 1825227498))) (.branch 43 (.branch 42 (.leaf 1783730310) (.leaf 1743415491)) (.branch 44 (.leaf 1704238473) (.leaf 1666156804))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1629130030) (.branch 47 (.leaf 1593119585) (.leaf 1558088689))) (.branch 50 (.branch 49 (.leaf 1524002255) (.leaf 1490826791)) (.branch 51 (.leaf 1458530322) (.leaf 1427082306)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1396453560) (.leaf 1366616185)) (.branch 55 (.leaf 1337543505) (.leaf 1309210002))) (.branch 58 (.branch 57 (.leaf 1281591252) (.leaf 1254663874)) (.branch 59 (.leaf 1228405478) (.leaf 1202794609))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1177810707) (.branch 62 (.leaf 1153434055) (.leaf 1129645746))) (.branch 65 (.branch 64 (.leaf 1106427636) (.leaf 1083762308)) (.branch 66 (.leaf 1061633039) (.leaf 1040023767)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1018919055) (.leaf 998304064)) (.branch 70 (.leaf 978164525) (.leaf 958486712))) (.branch 73 (.branch 72 (.leaf 939257414) (.leaf 920463916)) (.branch 74 (.leaf 902093971) (.leaf 884135781))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 866577977) (.branch 77 (.leaf 849409599) (.leaf 832620078))) (.branch 80 (.branch 79 (.leaf 816199216) (.leaf 800137175)) (.branch 81 (.leaf 784424454) (.leaf 769051881)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 754010595) (.leaf 739292034)) (.branch 85 (.leaf 724887921) (.leaf 710790252))) (.branch 88 (.branch 87 (.leaf 696991286) (.leaf 683483535)) (.branch 89 (.leaf 670259748) (.leaf 657312907)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 644636217) (.branch 92 (.leaf 632223092) (.leaf 620067153))) (.branch 95 (.branch 94 (.leaf 608162215) (.leaf 596502282)) (.branch 96 (.leaf 585081539) (.leaf 573894343)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 562935220) (.leaf 552198857)) (.branch 100 (.leaf 541680093) (.leaf 531373918))) (.branch 103 (.branch 102 (.leaf 521275465) (.leaf 511380004)) (.branch 104 (.leaf 501682938) (.leaf 492179800))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 482866243) (.leaf 473738042)) (.branch 108 (.leaf 464791087) (.leaf 456021375))) (.branch 111 (.branch 110 (.leaf 447425015) (.leaf 438998216)) (.branch 112 (.leaf 430737288) (.leaf 422638637)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 414698763) (.leaf 406914254)) (.branch 116 (.leaf 399281788) (.leaf 391798125))) (.branch 119 (.branch 118 (.leaf 384460107) (.leaf 377264657)) (.branch 120 (.leaf 370208771) (.leaf 363289521)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 296).prefactor = (497886845382619/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 296).cutoff/(generalMeanRows 296).c)).2 =
    (210084209311233/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 296).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 296).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 296).q*(generalMeanRows 296).c/2-2 = (91/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable102.value]
    have hcontinuation : (generalMeanRows 296).q*(generalMeanRows 296).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable118.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 296).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 296

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 296).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 296).criticalRate j.val*(generalMeanRows 296).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 296).c*(generalMeanRows 296).criticalPoint j.val)).2-
      (generalMeanRows 296).J/2-(generalMeanRows 296).error (generalMeanGrid j.val)+
      (generalMeanRows 296).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 296).c)).2-
      (generalMeanRows 296).J/2-(generalMeanRows 296).error 4 := by
  have he : (generalMeanRows 296).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 296) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 296)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0296

/-! Kernel-checked entropy margins for general spectral rectangle 297. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0297
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5176750275) (.branch 2 (.leaf 4987362966) (.leaf 4806746194))) (.branch 5 (.branch 4 (.leaf 4634394504) (.leaf 4469838181)) (.branch 6 (.leaf 4312640126) (.leaf 4162393086)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4018717161) (.leaf 3881257573)) (.branch 10 (.leaf 3749682656) (.leaf 3623682042))) (.branch 13 (.branch 12 (.leaf 3502965020) (.leaf 3387259045)) (.branch 14 (.leaf 3276308390) (.leaf 3169872910))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3067726922) (.branch 17 (.leaf 2969658175) (.leaf 2875466910))) (.branch 20 (.branch 19 (.leaf 2784965001) (.leaf 2697975158)) (.branch 21 (.leaf 2614330202) (.leaf 2533872392)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2456452804) (.leaf 2381930763)) (.branch 25 (.leaf 2310173312) (.leaf 2241054724))) (.branch 28 (.branch 27 (.leaf 2174456044) (.leaf 2110264674)) (.branch 29 (.leaf 2048373977) (.leaf 1988682919)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1931095727) (.branch 32 (.leaf 1875521572) (.leaf 1821874285))) (.branch 35 (.branch 34 (.leaf 1770072072) (.leaf 1720037269)) (.branch 36 (.leaf 1671696094) (.leaf 1624978434)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1579817627) (.leaf 1536150274)) (.branch 40 (.leaf 1493916052) (.leaf 1453057546))) (.branch 43 (.branch 42 (.leaf 1413520086) (.leaf 1375251598)) (.branch 44 (.leaf 1338202460) (.leaf 1302325375))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1267575239) (.branch 47 (.leaf 1233909030) (.leaf 1201285694))) (.branch 50 (.branch 49 (.leaf 1169666043) (.leaf 1139012656)) (.branch 51 (.leaf 1109289789) (.leaf 1080463287)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1052500505) (.leaf 1025370225)) (.branch 55 (.leaf 999042590) (.leaf 973489034))) (.branch 58 (.branch 57 (.leaf 948682214) (.leaf 924595952)) (.branch 59 (.leaf 901205178) (.leaf 878485874))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 856415023) (.branch 62 (.leaf 834970558) (.leaf 814131323))) (.branch 65 (.branch 64 (.leaf 793877022) (.leaf 774188180)) (.branch 66 (.leaf 755046106) (.leaf 736432857)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 718331197) (.leaf 700724570)) (.branch 70 (.leaf 683597068) (.leaf 666933395))) (.branch 73 (.branch 72 (.leaf 650718850) (.leaf 634939288)) (.branch 74 (.leaf 619581104) (.leaf 604631205))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 590076987) (.branch 77 (.leaf 575906312) (.leaf 562107494))) (.branch 80 (.branch 79 (.leaf 548669269) (.leaf 535580787)) (.branch 81 (.leaf 522831587) (.leaf 510411583)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 498311046) (.leaf 486520594)) (.branch 85 (.leaf 475031171) (.leaf 463834038))) (.branch 88 (.branch 87 (.leaf 452920756) (.leaf 442283177)) (.branch 89 (.leaf 431913431) (.leaf 421803914)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 411947277) (.branch 92 (.leaf 402336417) (.leaf 392964467))) (.branch 95 (.branch 94 (.leaf 383824784) (.leaf 374910945)) (.branch 96 (.leaf 366216734) (.leaf 357736136)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 349463329) (.leaf 341392676)) (.branch 100 (.leaf 333518719) (.leaf 325836171))) (.branch 103 (.branch 102 (.leaf 318339910) (.leaf 311024975)) (.branch 104 (.leaf 303886555) (.leaf 296919988))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 290120755) (.leaf 283484472)) (.branch 108 (.leaf 277006889) (.leaf 270683880))) (.branch 111 (.branch 110 (.leaf 264511444) (.leaf 258485700)) (.branch 112 (.leaf 252602876) (.leaf 246859316)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 241251466) (.leaf 235775877)) (.branch 116 (.leaf 230429198) (.leaf 225208175))) (.branch 119 (.branch 118 (.leaf 220109645) (.leaf 215130536)) (.branch 120 (.leaf 210267861) (.leaf 205518718)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 297).prefactor = (5272375110640663/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 297).cutoff/(generalMeanRows 297).c)).2 =
    (353640040243591/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 297).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 297).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 297).q*(generalMeanRows 297).c/2-2 = (22/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable099.value]
    have hcontinuation : (generalMeanRows 297).q*(generalMeanRows 297).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 297).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 297

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 297).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 297).criticalRate j.val*(generalMeanRows 297).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 297).c*(generalMeanRows 297).criticalPoint j.val)).2-
      (generalMeanRows 297).J/2-(generalMeanRows 297).error (generalMeanGrid j.val)+
      (generalMeanRows 297).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 297).c)).2-
      (generalMeanRows 297).J/2-(generalMeanRows 297).error 4 := by
  have he : (generalMeanRows 297).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 297) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 297)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0297

/-! Kernel-checked entropy margins for general spectral rectangle 298. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0298
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5302873758) (.branch 2 (.leaf 5111462019) (.leaf 4928878193))) (.branch 5 (.branch 4 (.leaf 4754613380) (.leaf 4588194684)) (.branch 6 (.leaf 4429182079) (.leaf 4277165608)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4131762874) (.leaf 3992616791)) (.branch 10 (.leaf 3859393558) (.leaf 3731780831))) (.branch 13 (.branch 12 (.leaf 3609486065) (.leaf 3492235020)) (.branch 14 (.leaf 3379770392) (.leaf 3271850576))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3168248532) (.branch 17 (.leaf 3068750747) (.leaf 2973156292))) (.branch 20 (.branch 19 (.leaf 2881275951) (.leaf 2792931418)) (.branch 21 (.leaf 2707954572) (.leaf 2626186792)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2547478337) (.leaf 2471687766)) (.branch 25 (.leaf 2398681413) (.leaf 2328332884))) (.branch 28 (.branch 27 (.leaf 2260522606) (.leaf 2195137402)) (.branch 29 (.leaf 2132070093) (.leaf 2071219139)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2012488292) (.branch 32 (.leaf 1955786284) (.leaf 1901026527))) (.branch 35 (.branch 34 (.leaf 1848126840) (.leaf 1797009192)) (.branch 36 (.leaf 1747599461) (.leaf 1699827209)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1653625473) (.leaf 1608930568)) (.branch 40 (.leaf 1565681904) (.leaf 1523821810))) (.branch 43 (.branch 42 (.leaf 1483295379) (.leaf 1444050309)) (.branch 44 (.leaf 1406036767) (.leaf 1369207249))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1333516461) (.branch 47 (.leaf 1298921198) (.leaf 1265380231))) (.branch 50 (.branch 49 (.leaf 1232854207) (.leaf 1201305548)) (.branch 51 (.leaf 1170698356) (.leaf 1140998335)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1112172697) (.leaf 1084190093)) (.branch 55 (.leaf 1057020538) (.leaf 1030635342))) (.branch 58 (.branch 57 (.leaf 1005007042) (.leaf 980109346)) (.branch 59 (.leaf 955917072) (.leaf 932406093))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 909553287) (.branch 62 (.leaf 887336487) (.leaf 865734433))) (.branch 65 (.branch 64 (.leaf 844726735) (.leaf 824293821)) (.branch 66 (.leaf 804416909) (.leaf 785077962)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 766259655) (.leaf 747945346)) (.branch 70 (.leaf 730119037) (.leaf 712765351))) (.branch 73 (.branch 72 (.leaf 695869498) (.leaf 679417253)) (.branch 74 (.leaf 663394928) (.leaf 647789349))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 632587831) (.branch 77 (.leaf 617778159) (.leaf 603348564))) (.branch 80 (.branch 79 (.leaf 589287707) (.leaf 575584660)) (.branch 81 (.leaf 562228883) (.leaf 549210215)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 536518852) (.leaf 524145334)) (.branch 85 (.leaf 512080532) (.leaf 500315631))) (.branch 88 (.branch 87 (.leaf 488842118) (.leaf 477651771)) (.branch 89 (.leaf 466736646) (.leaf 456089066)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 445701609) (.branch 92 (.leaf 435567099) (.leaf 425678596))) (.branch 95 (.branch 94 (.leaf 416029386) (.leaf 406612973)) (.branch 96 (.leaf 397423070) (.leaf 388453591)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 379698642) (.leaf 371152515)) (.branch 100 (.leaf 362809683) (.leaf 354664788))) (.branch 103 (.branch 102 (.leaf 346712639) (.leaf 338948203)) (.branch 104 (.leaf 331366601) (.leaf 323963104))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 316733120) (.leaf 309672200)) (.branch 108 (.leaf 302776024) (.leaf 296040400))) (.branch 111 (.branch 110 (.leaf 289461259) (.leaf 283034650)) (.branch 112 (.leaf 276756739) (.leaf 270623800)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 264632215) (.leaf 258778468)) (.branch 116 (.leaf 253059143) (.leaf 247470921))) (.branch 119 (.branch 118 (.leaf 242010574) (.leaf 236674967)) (.branch 120 (.leaf 231461048) (.leaf 226365853)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 298).prefactor = (5310201629961279/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 298).cutoff/(generalMeanRows 298).c)).2 =
    (361483217704619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 298).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 298).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 298).q*(generalMeanRows 298).c/2-2 = (343/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable096.value]
    have hcontinuation : (generalMeanRows 298).q*(generalMeanRows 298).cutoff/2-2 = (578/275:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable129.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 298).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 298

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 298).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 298).criticalRate j.val*(generalMeanRows 298).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 298).c*(generalMeanRows 298).criticalPoint j.val)).2-
      (generalMeanRows 298).J/2-(generalMeanRows 298).error (generalMeanGrid j.val)+
      (generalMeanRows 298).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 298).c)).2-
      (generalMeanRows 298).J/2-(generalMeanRows 298).error 4 := by
  have he : (generalMeanRows 298).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 298) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 298)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0298

/-! Kernel-checked entropy margins for general spectral rectangle 299. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0299
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5593441419) (.branch 2 (.leaf 5412303368) (.leaf 5239323480))) (.branch 5 (.branch 4 (.leaf 5074025803) (.leaf 4915968427)) (.branch 6 (.leaf 4764740522) (.leaf 4619959678)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4481269529) (.leaf 4348337622)) (.branch 10 (.leaf 4220853489) (.leaf 4098526920))) (.branch 13 (.branch 12 (.leaf 3981086383) (.leaf 3868277608)) (.branch 14 (.leaf 3759862288) (.leaf 3655616901))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3555331636) (.branch 17 (.leaf 3458809406) (.leaf 3365864953))) (.branch 20 (.branch 19 (.leaf 3276324017) (.leaf 3190022581)) (.branch 21 (.leaf 3106806175) (.leaf 3026529229)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2949054486) (.leaf 2874252449)) (.branch 25 (.leaf 2802000882) (.leaf 2732184340))) (.branch 28 (.branch 27 (.leaf 2664693731) (.leaf 2599425923)) (.branch 29 (.leaf 2536283363) (.leaf 2475173733)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2416009633) (.branch 32 (.leaf 2358708273) (.leaf 2303191198))) (.branch 35 (.branch 34 (.leaf 2249384029) (.leaf 2197216220)) (.branch 36 (.leaf 2146620826) (.leaf 2097534301)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2049896292) (.leaf 2003649459)) (.branch 40 (.leaf 1958739301) (.leaf 1915113992))) (.branch 43 (.branch 42 (.leaf 1872724233) (.leaf 1831523108)) (.branch 44 (.leaf 1791465950) (.leaf 1752510218))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1714615379) (.branch 47 (.leaf 1677742796) (.leaf 1641855628))) (.branch 50 (.branch 49 (.leaf 1606918732) (.leaf 1572898568)) (.branch 51 (.leaf 1539763120) (.leaf 1507481807)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1476025416) (.leaf 1445366020)) (.branch 55 (.leaf 1415476921) (.leaf 1386332579))) (.branch 58 (.branch 57 (.leaf 1357908557) (.leaf 1330181460)) (.branch 59 (.leaf 1303128885) (.leaf 1276729372))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1250962351) (.branch 62 (.leaf 1225808104) (.leaf 1201247719))) (.branch 65 (.branch 64 (.leaf 1177263050) (.leaf 1153836680)) (.branch 66 (.leaf 1130951887) (.leaf 1108592607)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1086743407) (.leaf 1065389449)) (.branch 70 (.leaf 1044516466) (.leaf 1024110733))) (.branch 73 (.branch 72 (.leaf 1004159044) (.leaf 984648683)) (.branch 74 (.leaf 965567407) (.leaf 946903420))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 928645354) (.branch 77 (.leaf 910782249) (.leaf 893303538))) (.branch 80 (.branch 79 (.leaf 876199022) (.leaf 859458862)) (.branch 81 (.leaf 843073558) (.leaf 827033935)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 811331129) (.leaf 795956575)) (.branch 85 (.leaf 780901992) (.leaf 766159372))) (.branch 88 (.branch 87 (.leaf 751720970) (.leaf 737579288)) (.branch 89 (.leaf 723727071) (.leaf 710157293)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 696863149) (.branch 92 (.leaf 683838045) (.leaf 671075590))) (.branch 95 (.branch 94 (.leaf 658569589) (.leaf 646314034)) (.branch 96 (.leaf 634303097) (.leaf 622531123)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 610992622) (.leaf 599682266)) (.branch 100 (.leaf 588594879) (.leaf 577725435))) (.branch 103 (.branch 102 (.leaf 567069048) (.leaf 556620970)) (.branch 104 (.leaf 546376587) (.leaf 536331410))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 526481074) (.leaf 516821332)) (.branch 108 (.leaf 507348052) (.leaf 498057211))) (.branch 111 (.branch 110 (.leaf 488944893) (.leaf 480007284)) (.branch 112 (.leaf 471240671) (.leaf 462641434)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 454206048) (.leaf 445931077)) (.branch 116 (.leaf 437813171) (.leaf 429849064))) (.branch 119 (.branch 118 (.leaf 422035572) (.leaf 414369587)) (.branch 120 (.leaf 406848080) (.leaf 399468093)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 299).prefactor = (5012925448215309/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 299).cutoff/(generalMeanRows 299).c)).2 =
    (107066407213771/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 299).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 299).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 299).q*(generalMeanRows 299).c/2-2 = (353/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable084.value]
    have hcontinuation : (generalMeanRows 299).q*(generalMeanRows 299).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable118.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 299).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 299

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 299).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 299).criticalRate j.val*(generalMeanRows 299).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 299).c*(generalMeanRows 299).criticalPoint j.val)).2-
      (generalMeanRows 299).J/2-(generalMeanRows 299).error (generalMeanGrid j.val)+
      (generalMeanRows 299).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 299).c)).2-
      (generalMeanRows 299).J/2-(generalMeanRows 299).error 4 := by
  have he : (generalMeanRows 299).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 299) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 299)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0299

/-! Kernel-checked entropy margins for general spectral rectangle 300. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0300
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5732276970) (.branch 2 (.leaf 5549591870) (.leaf 5375110502))) (.branch 5 (.branch 4 (.leaf 5208353609) (.leaf 5048876246)) (.branch 6 (.leaf 4896264788) (.leaf 4750134254)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4610125910) (.leaf 4475905119)) (.branch 10 (.leaf 4347159403) (.leaf 4223596696))) (.branch 13 (.branch 12 (.leaf 4104943756) (.leaf 3990944735)) (.branch 14 (.leaf 3881359871) (.leaf 3775964298))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3674546968) (.branch 17 (.leaf 3576909653) (.leaf 3482866039))) (.branch 20 (.branch 19 (.leaf 3392240898) (.leaf 3304869318)) (.branch 21 (.leaf 3220596004) (.leaf 3139274627)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3060767232) (.leaf 2984943681)) (.branch 25 (.leaf 2911681147) (.leaf 2840863640))) (.branch 28 (.branch 27 (.leaf 2772381574) (.leaf 2706131357)) (.branch 29 (.leaf 2642015018) (.leaf 2579939858)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2519818125) (.branch 32 (.leaf 2461566710) (.leaf 2405106867))) (.branch 35 (.branch 34 (.leaf 2350363950) (.leaf 2297267172)) (.branch 36 (.leaf 2245749370) (.leaf 2195746799)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2147198926) (.leaf 2100048250)) (.branch 40 (.leaf 2054240124) (.leaf 2009722593))) (.branch 43 (.branch 42 (.leaf 1966446239) (.leaf 1924364044)) (.branch 44 (.leaf 1883431248) (.leaf 1843605229))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1804845382) (.branch 47 (.leaf 1767113007) (.leaf 1730371211))) (.branch 50 (.branch 49 (.leaf 1694584803) (.leaf 1659720203)) (.branch 51 (.leaf 1625745362) (.leaf 1592629672)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1560343895) (.leaf 1528860090)) (.branch 55 (.leaf 1498151543) (.leaf 1468192705))) (.branch 58 (.branch 57 (.leaf 1438959132) (.leaf 1410427427)) (.branch 59 (.leaf 1382575186) (.leaf 1355380949))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1328824153) (.branch 62 (.leaf 1302885084) (.leaf 1277544836))) (.branch 65 (.branch 64 (.leaf 1252785274) (.leaf 1228588989)) (.branch 66 (.leaf 1204939269) (.leaf 1181820064)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1159215950) (.leaf 1137112102)) (.branch 70 (.leaf 1115494267) (.leaf 1094348731))) (.branch 73 (.branch 72 (.leaf 1073662300) (.leaf 1053422273)) (.branch 74 (.leaf 1033616417) (.leaf 1014232949))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 995260512) (.branch 77 (.leaf 976688158) (.leaf 958505329))) (.branch 80 (.branch 79 (.leaf 940701839) (.leaf 923267856)) (.branch 81 (.leaf 906193889) (.leaf 889470772)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 873089648) (.leaf 857041958)) (.branch 85 (.leaf 841319428) (.leaf 825914053))) (.branch 88 (.branch 87 (.leaf 810818092) (.leaf 796024052)) (.branch 89 (.leaf 781524679) (.leaf 767312948)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 753382054) (.branch 92 (.leaf 739725403) (.leaf 726336603))) (.branch 95 (.branch 94 (.leaf 713209457) (.leaf 700337953)) (.branch 96 (.leaf 687716258) (.leaf 675338713)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 663199821) (.leaf 651294249)) (.branch 100 (.leaf 639616811) (.leaf 628162473))) (.branch 103 (.branch 102 (.leaf 616926339) (.leaf 605903653)) (.branch 104 (.leaf 595089787) (.leaf 584480241))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 574070638) (.leaf 563856716)) (.branch 108 (.leaf 553834329) (.leaf 543999439))) (.branch 111 (.branch 110 (.leaf 534348114) (.leaf 524876523)) (.branch 112 (.leaf 515580936) (.leaf 506457716)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 497503318) (.leaf 488714287)) (.branch 116 (.leaf 480087253) (.leaf 471618930))) (.branch 119 (.branch 118 (.leaf 463306111) (.leaf 455145669)) (.branch 120 (.leaf 447134550) (.leaf 439269776)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 300).prefactor = (5047215402940221/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 300).cutoff/(generalMeanRows 300).c)).2 =
    (87285787898849/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 300).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 300).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 300).q*(generalMeanRows 300).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    have hcontinuation : (generalMeanRows 300).q*(generalMeanRows 300).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable118.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 300).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 300

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 300).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 300).criticalRate j.val*(generalMeanRows 300).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 300).c*(generalMeanRows 300).criticalPoint j.val)).2-
      (generalMeanRows 300).J/2-(generalMeanRows 300).error (generalMeanGrid j.val)+
      (generalMeanRows 300).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 300).c)).2-
      (generalMeanRows 300).J/2-(generalMeanRows 300).error 4 := by
  have he : (generalMeanRows 300).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 300) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 300)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0300

/-! Kernel-checked entropy margins for general spectral rectangle 301. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0301
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5049621314) (.branch 2 (.leaf 4870956045) (.leaf 4700478420))) (.branch 5 (.branch 4 (.leaf 4537715635) (.leaf 4382228427)) (.branch 6 (.leaf 4233608151) (.leaf 4091474171)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3955471520) (.leaf 3825268802)) (.branch 10 (.leaf 3700556304) (.leaf 3581044290))) (.branch 13 (.branch 12 (.leaf 3466461458) (.leaf 3356553540)) (.branch 14 (.leaf 3251082032) (.leaf 3149823035))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3052566198) (.branch 17 (.leaf 2959113753) (.leaf 2869279630))) (.branch 20 (.branch 19 (.leaf 2782888648) (.leaf 2699775770)) (.branch 21 (.leaf 2619785415) (.leaf 2542770832)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2468593513) (.leaf 2397122659)) (.branch 25 (.leaf 2328234683) (.leaf 2261812750))) (.branch 28 (.branch 27 (.leaf 2197746348) (.leaf 2135930898)) (.branch 29 (.leaf 2076267382) (.leaf 2018662008)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1963025885) (.branch 32 (.leaf 1909274736) (.leaf 1857328618))) (.branch 35 (.branch 34 (.leaf 1807111666) (.leaf 1758551854)) (.branch 36 (.leaf 1711580775) (.leaf 1666133427)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1622148021) (.leaf 1579565797)) (.branch 40 (.leaf 1538330855) (.leaf 1498389991))) (.branch 43 (.branch 42 (.leaf 1459692554) (.leaf 1422190296)) (.branch 44 (.leaf 1385837248) (.leaf 1350589592))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1316405545) (.branch 47 (.leaf 1283245249) (.leaf 1251070674))) (.branch 50 (.branch 49 (.leaf 1219845511) (.leaf 1189535090)) (.branch 51 (.leaf 1160106290) (.leaf 1131527461)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1103768345) (.leaf 1076800007)) (.branch 55 (.leaf 1050594766) (.leaf 1025126132))) (.branch 58 (.branch 57 (.leaf 1000368747) (.leaf 976298326)) (.branch 59 (.leaf 952891607) (.leaf 930126295))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 907981022) (.branch 62 (.leaf 886435295) (.leaf 865469457))) (.branch 65 (.branch 64 (.leaf 845064645) (.leaf 825202754)) (.branch 66 (.leaf 805866399) (.leaf 787038882)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 768704160) (.leaf 750846811)) (.branch 70 (.leaf 733452012) (.leaf 716505503))) (.branch 73 (.branch 72 (.leaf 699993569) (.leaf 683903011)) (.branch 74 (.leaf 668221120) (.leaf 652935663))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 638034854) (.branch 77 (.leaf 623507338) (.leaf 609342171))) (.branch 80 (.branch 79 (.leaf 595528803) (.leaf 582057059)) (.branch 81 (.leaf 568917124) (.leaf 556099529)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 543595133) (.leaf 531395111)) (.branch 85 (.leaf 519490940) (.leaf 507874390))) (.branch 88 (.branch 87 (.leaf 496537504) (.leaf 485472596)) (.branch 89 (.leaf 474672232) (.leaf 464129226)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 453836625) (.branch 92 (.leaf 443787704) (.leaf 433975953))) (.branch 95 (.branch 94 (.leaf 424395072) (.leaf 415038960)) (.branch 96 (.leaf 405901709) (.leaf 396977595)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 388261074) (.leaf 379746772)) (.branch 100 (.leaf 371429479) (.leaf 363304144))) (.branch 103 (.branch 102 (.leaf 355365870) (.leaf 347609905)) (.branch 104 (.leaf 340031640) (.leaf 332626601))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 325390447) (.leaf 318318964)) (.branch 108 (.leaf 311408058) (.leaf 304653756))) (.branch 111 (.branch 110 (.leaf 298052198) (.leaf 291599632)) (.branch 112 (.leaf 285292414) (.leaf 279127003)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 273099954) (.leaf 267207922)) (.branch 116 (.leaf 261447650) (.leaf 255815974))) (.branch 119 (.branch 118 (.leaf 250309815) (.leaf 244926176)) (.branch 120 (.leaf 239662144) (.leaf 234514881)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 301).prefactor = (2492423833136257/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 301).cutoff/(generalMeanRows 301).c)).2 =
    (374631555805619/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 301).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 301).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 301).q*(generalMeanRows 301).c/2-2 = (419/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable106.value]
    have hcontinuation : (generalMeanRows 301).q*(generalMeanRows 301).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable119.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 301).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 301

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 301).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 301).criticalRate j.val*(generalMeanRows 301).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 301).c*(generalMeanRows 301).criticalPoint j.val)).2-
      (generalMeanRows 301).J/2-(generalMeanRows 301).error (generalMeanGrid j.val)+
      (generalMeanRows 301).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 301).c)).2-
      (generalMeanRows 301).J/2-(generalMeanRows 301).error 4 := by
  have he : (generalMeanRows 301).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 301) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 301)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0301

/-! Kernel-checked entropy margins for general spectral rectangle 302. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0302
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5172050294) (.branch 2 (.leaf 4991594452) (.leaf 4819375981))) (.branch 5 (.branch 4 (.leaf 4654918938) (.leaf 4497781177)) (.branch 6 (.leaf 4347551398) (.leaf 4203846517)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4066309310) (.leaf 3934606302)) (.branch 10 (.leaf 3808425857) (.leaf 3687476464))) (.branch 13 (.branch 12 (.leaf 3571485180) (.leaf 3460196218)) (.branch 14 (.leaf 3353369672) (.leaf 3250780342))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3152216674) (.branch 17 (.leaf 3057479787) (.leaf 2966382578))) (.branch 20 (.branch 19 (.leaf 2878748911) (.leaf 2794412859)) (.branch 21 (.leaf 2713218023) (.leaf 2635016886)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2559670235) (.leaf 2487046614)) (.branch 25 (.leaf 2417021828) (.leaf 2349478474))) (.branch 28 (.branch 27 (.leaf 2284305519) (.leaf 2221397894)) (.branch 29 (.leaf 2160656131) (.leaf 2101986013)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2045298262) (.branch 32 (.leaf 1990508236) (.leaf 1937535653))) (.branch 35 (.branch 34 (.leaf 1886304335) (.leaf 1836741963)) (.branch 36 (.leaf 1788779856) (.leaf 1742352758)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1697398644) (.leaf 1653858533)) (.branch 40 (.leaf 1611676318) (.leaf 1570798604))) (.branch 43 (.branch 42 (.leaf 1531174556) (.leaf 1492755760)) (.branch 44 (.leaf 1455496088) (.leaf 1419351573))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1384280294) (.branch 47 (.leaf 1350242262) (.leaf 1317199321))) (.branch 50 (.branch 49 (.leaf 1285115048) (.leaf 1253954662)) (.branch 51 (.leaf 1223684939) (.leaf 1194274128)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1165691878) (.leaf 1137909165)) (.branch 55 (.leaf 1110898222) (.leaf 1084632478))) (.branch 58 (.branch 57 (.leaf 1059086497) (.leaf 1034235918)) (.branch 59 (.leaf 1010057408) (.leaf 986528601))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 963628063) (.branch 62 (.leaf 941335233) (.leaf 919630393))) (.branch 65 (.branch 64 (.leaf 898494617) (.leaf 877909739)) (.branch 66 (.leaf 857858316) (.leaf 838323592)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 819289465) (.leaf 800740459)) (.branch 70 (.leaf 782661695) (.leaf 765038859))) (.branch 73 (.branch 72 (.leaf 747858180) (.leaf 731106407)) (.branch 74 (.leaf 714770779) (.leaf 698839007))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 683299255) (.branch 77 (.leaf 668140116) (.leaf 653350592))) (.branch 80 (.branch 79 (.leaf 638920082) (.leaf 624838360)) (.branch 81 (.leaf 611095558) (.leaf 597682155)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 584588958) (.leaf 571807091)) (.branch 85 (.leaf 559327980) (.leaf 547143341))) (.branch 88 (.branch 87 (.leaf 535245166) (.leaf 523625717)) (.branch 89 (.leaf 512277507) (.leaf 501193298)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 490366085) (.branch 92 (.leaf 479789090) (.leaf 469455750))) (.branch 95 (.branch 94 (.leaf 459359712) (.leaf 449494823)) (.branch 96 (.leaf 439855121) (.leaf 430434831)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 421228353) (.leaf 412230261)) (.branch 100 (.leaf 403435291) (.leaf 394838340))) (.branch 103 (.branch 102 (.leaf 386434455) (.leaf 378218832)) (.branch 104 (.leaf 370186807) (.leaf 362333855))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 354655579) (.leaf 347147711)) (.branch 108 (.leaf 339806106) (.leaf 332626734))) (.branch 111 (.branch 110 (.leaf 325605682) (.leaf 318739145)) (.branch 112 (.leaf 312023426) (.leaf 305454928)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 299030155) (.leaf 292745707)) (.branch 116 (.leaf 286598275) (.leaf 280584639))) (.branch 119 (.branch 118 (.leaf 274701669) (.leaf 268946316)) (.branch 120 (.leaf 263315611) (.leaf 257806666)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 302).prefactor = (2509748702951903/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 302).cutoff/(generalMeanRows 302).c)).2 =
    (15296547849907/40000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 302).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 302).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 302).q*(generalMeanRows 302).c/2-2 = (102/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable107.value]
    have hcontinuation : (generalMeanRows 302).q*(generalMeanRows 302).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable119.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 302).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 302

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 302).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 302).criticalRate j.val*(generalMeanRows 302).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 302).c*(generalMeanRows 302).criticalPoint j.val)).2-
      (generalMeanRows 302).J/2-(generalMeanRows 302).error (generalMeanGrid j.val)+
      (generalMeanRows 302).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 302).c)).2-
      (generalMeanRows 302).J/2-(generalMeanRows 302).error 4 := by
  have he : (generalMeanRows 302).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 302) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 302)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0302

/-! Kernel-checked entropy margins for general spectral rectangle 303. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0303
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4878708219) (.branch 2 (.leaf 4699189420) (.leaf 4527967028))) (.branch 5 (.branch 4 (.leaf 4364564650) (.leaf 4208539511)) (.branch 6 (.leaf 4059479524) (.leaf 3917000675)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3780744687) (.leaf 3650376919)) (.branch 10 (.leaf 3525584475) (.leaf 3406074499))) (.branch 13 (.branch 12 (.leaf 3291572632) (.leaf 3181821610)) (.branch 14 (.leaf 3076579996) (.leaf 2975621020))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2878731522) (.branch 17 (.leaf 2785710987) (.leaf 2696370661))) (.branch 20 (.branch 19 (.leaf 2610532741) (.leaf 2528029628)) (.branch 21 (.leaf 2448703243) (.leaf 2372404399)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2298992211) (.leaf 2228333568)) (.branch 25 (.leaf 2160302628) (.leaf 2094780362))) (.branch 28 (.branch 27 (.leaf 2031654127) (.leaf 1970817269)) (.branch 29 (.leaf 1912168755) (.leaf 1855612834)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1801058717) (.branch 32 (.leaf 1748420282) (.leaf 1697615799))) (.branch 35 (.branch 34 (.leaf 1648567668) (.leaf 1601202188)) (.branch 36 (.leaf 1555449322) (.leaf 1511242496)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1468518397) (.leaf 1427216796)) (.branch 40 (.leaf 1387280367) (.leaf 1348654533))) (.branch 43 (.branch 42 (.leaf 1311287315) (.leaf 1275129183)) (.branch 44 (.leaf 1240132934) (.leaf 1206253557))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1173448120) (.branch 47 (.leaf 1141675661) (.leaf 1110897081))) (.branch 50 (.branch 49 (.leaf 1081075049) (.leaf 1052173908)) (.branch 51 (.leaf 1024159590) (.leaf 996999533)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 970662604) (.leaf 945119030)) (.branch 55 (.leaf 920340322) (.leaf 896299221))) (.branch 58 (.branch 57 (.leaf 872969627) (.leaf 850326547)) (.branch 59 (.leaf 828346041) (.leaf 807005166))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 786281933) (.branch 62 (.leaf 766155257) (.leaf 746604916))) (.branch 65 (.branch 64 (.leaf 727611509) (.leaf 709156416)) (.branch 66 (.leaf 691221763) (.leaf 673790387)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 656845802) (.leaf 640372167)) (.branch 70 (.leaf 624354258) (.leaf 608777439))) (.branch 73 (.branch 72 (.leaf 593627637) (.leaf 578891312)) (.branch 74 (.leaf 564555439) (.leaf 550607480))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 537035368) (.branch 77 (.leaf 523827478) (.leaf 510972618))) (.branch 80 (.branch 79 (.leaf 498459999) (.leaf 486279229)) (.branch 81 (.leaf 474420287) (.leaf 462873511)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 451629583) (.leaf 440679513)) (.branch 85 (.leaf 430014627) (.leaf 419626552))) (.branch 88 (.branch 87 (.leaf 409507205) (.leaf 399648780)) (.branch 89 (.leaf 390043739) (.leaf 380684798)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 371564918) (.branch 92 (.leaf 362677296) (.leaf 354015356))) (.branch 95 (.branch 94 (.leaf 345572737) (.leaf 337343288)) (.branch 96 (.leaf 329321059) (.leaf 321500291)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 313875412) (.leaf 306441028)) (.branch 100 (.leaf 299191915) (.leaf 292123015))) (.branch 103 (.branch 102 (.leaf 285229430) (.leaf 278506412)) (.branch 104 (.leaf 271949364) (.leaf 265553828))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 259315483) (.leaf 253230142)) (.branch 108 (.leaf 247293741) (.leaf 241502343))) (.branch 111 (.branch 110 (.leaf 235852125) (.leaf 230339381)) (.branch 112 (.leaf 224960514) (.leaf 219712032)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 214590546) (.leaf 209592766)) (.branch 116 (.leaf 204715499) (.leaf 199955643))) (.branch 119 (.branch 118 (.leaf 195310183) (.leaf 190776194)) (.branch 120 (.leaf 186350832) (.leaf 182031335)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 303).prefactor = (5026062098367719/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 303).cutoff/(generalMeanRows 303).c)).2 =
    (345671870594417/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 303).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 303).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 303).q*(generalMeanRows 303).c/2-2 = (113/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable124.value]
    have hcontinuation : (generalMeanRows 303).q*(generalMeanRows 303).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 303).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 303

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 303).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 303).criticalRate j.val*(generalMeanRows 303).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 303).c*(generalMeanRows 303).criticalPoint j.val)).2-
      (generalMeanRows 303).J/2-(generalMeanRows 303).error (generalMeanGrid j.val)+
      (generalMeanRows 303).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 303).c)).2-
      (generalMeanRows 303).J/2-(generalMeanRows 303).error 4 := by
  have he : (generalMeanRows 303).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 303) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 303)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0303

/-! Kernel-checked entropy margins for general spectral rectangle 304. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0304
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4995609714) (.branch 2 (.leaf 4814170599) (.leaf 4641081156))) (.branch 5 (.branch 4 (.leaf 4475861862) (.leaf 4318067053)) (.branch 6 (.leaf 4167281982) (.leaf 4023120182)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3885221110) (.leaf 3753248028)) (.branch 10 (.leaf 3626886105) (.leaf 3505840688))) (.branch 13 (.branch 12 (.leaf 3389835757) (.leaf 3278612508)) (.branch 14 (.leaf 3171928072) (.leaf 3069554353))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2971276959) (.branch 17 (.leaf 2876894227) (.leaf 2786216340))) (.branch 20 (.branch 19 (.leaf 2699064502) (.leaf 2615270190)) (.branch 21 (.leaf 2534674467) (.leaf 2457127343)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2382487186) (.leaf 2310620187)) (.branch 25 (.leaf 2241399854) (.leaf 2174706548))) (.branch 28 (.branch 27 (.leaf 2110427056) (.leaf 2048454194)) (.branch 29 (.leaf 1988686429) (.leaf 1931027544)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1875386313) (.branch 32 (.leaf 1821676202) (.leaf 1769815096))) (.branch 35 (.branch 34 (.leaf 1719725033) (.leaf 1671331970)) (.branch 36 (.leaf 1624565550) (.leaf 1579358897)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1535648413) (.leaf 1493373596)) (.branch 40 (.leaf 1452476869) (.leaf 1412903413))) (.branch 43 (.branch 42 (.leaf 1374601019) (.leaf 1337519942)) (.branch 44 (.leaf 1301612771) (.leaf 1266834299))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1233141408) (.branch 47 (.leaf 1200492957) (.leaf 1168849678))) (.branch 50 (.branch 49 (.leaf 1138174075) (.leaf 1108430335)) (.branch 51 (.leaf 1079584240) (.leaf 1051603084)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1024455595) (.leaf 998111864)) (.branch 55 (.leaf 972543277) (.leaf 947722445))) (.branch 58 (.branch 57 (.leaf 923623149) (.leaf 900220278)) (.branch 59 (.leaf 877489775) (.leaf 855408589))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 833954621) (.branch 62 (.leaf 813106680) (.leaf 792844439))) (.branch 65 (.branch 64 (.leaf 773148397) (.leaf 753999834)) (.branch 66 (.leaf 735380778) (.leaf 717273972)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 699662833) (.leaf 682531428)) (.branch 70 (.leaf 665864443) (.leaf 649647152))) (.branch 73 (.branch 72 (.leaf 633865390) (.leaf 618505532)) (.branch 74 (.leaf 603554465) (.leaf 588999567))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 574828682) (.branch 77 (.leaf 561030104) (.leaf 547592555))) (.branch 80 (.branch 79 (.leaf 534505167) (.leaf 521757462)) (.branch 81 (.leaf 509339339) (.leaf 497241056)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 485453213) (.leaf 473966742)) (.branch 85 (.leaf 462772888) (.leaf 451863200))) (.branch 88 (.branch 87 (.leaf 441229517) (.leaf 430863955)) (.branch 89 (.leaf 420758899) (.leaf 410906986)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 401301104) (.branch 92 (.leaf 391934371) (.leaf 382800137))) (.branch 95 (.branch 94 (.leaf 373891965) (.leaf 365203629)) (.branch 96 (.leaf 356729105) (.leaf 348462559)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 340398347) (.leaf 332531000)) (.branch 100 (.leaf 324855222) (.leaf 317365883))) (.branch 103 (.branch 102 (.leaf 310058011) (.leaf 302926790)) (.branch 104 (.leaf 295967548) (.leaf 289175758))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 282547028) (.leaf 276077102)) (.branch 108 (.leaf 269761846) (.leaf 263597253))) (.branch 111 (.branch 110 (.leaf 257579433) (.leaf 251704610)) (.branch 112 (.leaf 245969120) (.leaf 240369404)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 234902006) (.leaf 229563570)) (.branch 116 (.leaf 224350836) (.leaf 219260637))) (.branch 119 (.branch 118 (.leaf 214289894) (.leaf 209435616)) (.branch 120 (.leaf 204694896) (.leaf 200064908)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 304).prefactor = (5061569805991533/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 304).cutoff/(generalMeanRows 304).c)).2 =
    (70655293995927/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 304).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 304).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 304).q*(generalMeanRows 304).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 304).q*(generalMeanRows 304).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 304).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 304

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 304).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 304).criticalRate j.val*(generalMeanRows 304).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 304).c*(generalMeanRows 304).criticalPoint j.val)).2-
      (generalMeanRows 304).J/2-(generalMeanRows 304).error (generalMeanGrid j.val)+
      (generalMeanRows 304).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 304).c)).2-
      (generalMeanRows 304).J/2-(generalMeanRows 304).error 4 := by
  have he : (generalMeanRows 304).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 304) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 304)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0304

/-! Kernel-checked entropy margins for general spectral rectangle 305. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0305
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5390005209) (.branch 2 (.leaf 5207296541) (.leaf 5032866332))) (.branch 5 (.branch 4 (.leaf 4866235552) (.leaf 4706959244)) (.branch 6 (.leaf 4554623552) (.leaf 4408843065)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4269258447) (.leaf 4135534296)) (.branch 10 (.leaf 4007357230) (.leaf 3884434148))) (.branch 13 (.branch 12 (.leaf 3766490666) (.leaf 3653269690)) (.branch 14 (.leaf 3544530127) (.leaf 3440045705))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3339603900) (.branch 17 (.leaf 3243004956) (.leaf 3150060982))) (.branch 20 (.branch 19 (.leaf 3060595130) (.leaf 2974440840)) (.branch 21 (.leaf 2891441140) (.leaf 2811448006)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2734321772) (.leaf 2659930582)) (.branch 25 (.leaf 2588149884) (.leaf 2518861966))) (.branch 28 (.branch 27 (.leaf 2451955521) (.leaf 2387325244)) (.branch 29 (.leaf 2324871462) (.leaf 2264499787)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2206120791) (.branch 32 (.leaf 2149649709) (.leaf 2095006161))) (.branch 35 (.branch 34 (.leaf 2042113886) (.leaf 1990900504)) (.branch 36 (.leaf 1941297288) (.leaf 1893238952)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1846663451) (.leaf 1801511797)) (.branch 40 (.leaf 1757727888) (.leaf 1715258342))) (.branch 43 (.branch 42 (.leaf 1674052345) (.leaf 1634061511)) (.branch 44 (.leaf 1595239746) (.leaf 1557543121))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1520929759) (.branch 47 (.leaf 1485359718) (.leaf 1450794893))) (.branch 50 (.branch 49 (.leaf 1417198912) (.leaf 1384537048)) (.branch 51 (.leaf 1352776133) (.leaf 1321884472)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1291831769) (.leaf 1262589058)) (.branch 55 (.leaf 1234128626) (.leaf 1206423958))) (.branch 58 (.branch 57 (.leaf 1179449670) (.leaf 1153181457)) (.branch 59 (.leaf 1127596033) (.leaf 1102671084))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1078385221) (.branch 62 (.leaf 1054717931) (.leaf 1031649535))) (.branch 65 (.branch 64 (.leaf 1009161150) (.leaf 987234648)) (.branch 66 (.leaf 965852620) (.leaf 944998342)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 924655743) (.leaf 904809374)) (.branch 70 (.leaf 885444379) (.leaf 866546466))) (.branch 73 (.branch 72 (.leaf 848101884) (.leaf 830097393)) (.branch 74 (.leaf 812520248) (.leaf 795358169))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 778599325) (.branch 77 (.leaf 762232314) (.leaf 746246139))) (.branch 80 (.branch 79 (.leaf 730630196) (.leaf 715374254)) (.branch 81 (.leaf 700468439) (.leaf 685903219)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 671669387) (.leaf 657758052)) (.branch 85 (.leaf 644160620) (.leaf 630868788))) (.branch 88 (.branch 87 (.leaf 617874524) (.leaf 605170064)) (.branch 89 (.leaf 592747893) (.leaf 580600742)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 568721573) (.branch 92 (.leaf 557103573) (.leaf 545740142))) (.branch 95 (.branch 94 (.leaf 534624888) (.leaf 523751615)) (.branch 96 (.leaf 513114320) (.leaf 502707180)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 492524550) (.leaf 482560954)) (.branch 100 (.leaf 472811078) (.leaf 463269766))) (.branch 103 (.branch 102 (.leaf 453932012) (.leaf 444792956)) (.branch 104 (.leaf 435847877) (.leaf 427092192))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 418521444) (.leaf 410131304)) (.branch 108 (.leaf 401917564) (.leaf 393876132))) (.branch 111 (.branch 110 (.leaf 386003030) (.leaf 378294387)) (.branch 112 (.leaf 370746439) (.leaf 363355523)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 356118072) (.leaf 349030618)) (.branch 116 (.leaf 342089780) (.leaf 335292271))) (.branch 119 (.branch 118 (.leaf 328634884) (.leaf 322114501)) (.branch 120 (.leaf 315728078) (.leaf 309472655)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 305).prefactor = (315899249769793/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 305).cutoff/(generalMeanRows 305).c)).2 =
    (398162053215813/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 305).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 305).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 305).q*(generalMeanRows 305).c/2-2 = (193/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable071.value]
    have hcontinuation : (generalMeanRows 305).q*(generalMeanRows 305).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable119.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 305).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 305

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 305).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 305).criticalRate j.val*(generalMeanRows 305).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 305).c*(generalMeanRows 305).criticalPoint j.val)).2-
      (generalMeanRows 305).J/2-(generalMeanRows 305).error (generalMeanGrid j.val)+
      (generalMeanRows 305).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 305).c)).2-
      (generalMeanRows 305).J/2-(generalMeanRows 305).error 4 := by
  have he : (generalMeanRows 305).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 305) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 305)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0305

/-! Kernel-checked entropy margins for general spectral rectangle 306. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0306
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5522297726) (.branch 2 (.leaf 5337873823) (.leaf 5161776987))) (.branch 5 (.branch 4 (.leaf 4993524924) (.leaf 4832669673)) (.branch 6 (.leaf 4678794616) (.leaf 4531511799)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4390459538) (.leaf 4255300270)) (.branch 10 (.leaf 4125718618) (.leaf 4001419638))) (.branch 13 (.branch 12 (.leaf 3882127247) (.leaf 3767582781)) (.branch 14 (.leaf 3657543695) (.leaf 3551782377))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3450085065) (.branch 17 (.leaf 3352250856) (.leaf 3258090801))) (.branch 20 (.branch 19 (.leaf 3167427075) (.leaf 3080092212)) (.branch 21 (.leaf 2995928405) (.leaf 2914786857)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2836527188) (.leaf 2761016882)) (.branch 25 (.leaf 2688130777) (.leaf 2617750599))) (.branch 28 (.branch 27 (.leaf 2549764521) (.leaf 2484066757)) (.branch 29 (.leaf 2420557191) (.leaf 2359141026)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2299728458) (.branch 32 (.leaf 2242234374) (.leaf 2186578071))) (.branch 35 (.branch 34 (.leaf 2132682994) (.leaf 2080476492)) (.branch 36 (.leaf 2029889586) (.leaf 1980856759)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1933315753) (.leaf 1887207386)) (.branch 40 (.leaf 1842475375) (.leaf 1799066173))) (.branch 43 (.branch 42 (.leaf 1756928814) (.leaf 1716014773)) (.branch 44 (.leaf 1676277826) (.leaf 1637673929))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1600161093) (.branch 47 (.leaf 1563699280) (.leaf 1528250290))) (.branch 50 (.branch 49 (.leaf 1493777670) (.leaf 1460246614)) (.branch 51 (.leaf 1427623883) (.leaf 1395877716)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1364977758) (.leaf 1334894985)) (.branch 55 (.leaf 1305601634) (.leaf 1277071143))) (.branch 58 (.branch 57 (.leaf 1249278083) (.leaf 1222198106)) (.branch 59 (.leaf 1195807889) (.leaf 1170085083))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1145008264) (.branch 62 (.leaf 1120556886) (.leaf 1096711243))) (.branch 65 (.branch 64 (.leaf 1073452421) (.leaf 1050762264)) (.branch 66 (.leaf 1028623338) (.leaf 1007018895)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 985932837) (.leaf 965349693)) (.branch 70 (.leaf 945254582) (.leaf 925633190))) (.branch 73 (.branch 72 (.leaf 906471743) (.leaf 887756979)) (.branch 74 (.leaf 869476129) (.leaf 851616893))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 834167417) (.branch 77 (.leaf 817116273) (.leaf 800452446))) (.branch 80 (.branch 79 (.leaf 784165307) (.leaf 768244601)) (.branch 81 (.leaf 752680430) (.leaf 737463239)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 722583796) (.leaf 708033186)) (.branch 85 (.leaf 693802790) (.leaf 679884277))) (.branch 88 (.branch 87 (.leaf 666269592) (.leaf 652950940)) (.branch 89 (.leaf 639920782) (.leaf 627171821)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 614696989) (.branch 92 (.leaf 602489445) (.leaf 590542560))) (.branch 95 (.branch 94 (.leaf 578849911) (.leaf 567405273)) (.branch 96 (.leaf 556202609) (.leaf 545236069)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 534499972) (.leaf 523988812)) (.branch 100 (.leaf 513697240) (.leaf 503620068))) (.branch 103 (.branch 102 (.leaf 493752256) (.leaf 484088908)) (.branch 104 (.leaf 474625270) (.leaf 465356721))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 456278771) (.leaf 447387054)) (.branch 108 (.leaf 438677325) (.leaf 430145456))) (.branch 111 (.branch 110 (.leaf 421787430) (.leaf 413599339)) (.branch 112 (.leaf 405577381) (.leaf 397717855)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 390017156) (.leaf 382471775)) (.branch 116 (.leaf 375078294) (.leaf 367833385))) (.branch 119 (.branch 118 (.leaf 360733803) (.leaf 353776387)) (.branch 120 (.leaf 346958057) (.leaf 340275809)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 306).prefactor = (5089521111668017/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 306).cutoff/(generalMeanRows 306).c)).2 =
    (406130222864989/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 306).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 306).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 306).q*(generalMeanRows 306).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 306).q*(generalMeanRows 306).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable119.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 306).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 306

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 306).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 306).criticalRate j.val*(generalMeanRows 306).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 306).c*(generalMeanRows 306).criticalPoint j.val)).2-
      (generalMeanRows 306).J/2-(generalMeanRows 306).error (generalMeanGrid j.val)+
      (generalMeanRows 306).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 306).c)).2-
      (generalMeanRows 306).J/2-(generalMeanRows 306).error 4 := by
  have he : (generalMeanRows 306).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 306) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 306)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0306

/-! Kernel-checked entropy margins for general spectral rectangle 307. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0307
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5115817784) (.branch 2 (.leaf 4932470021) (.leaf 4757524888))) (.branch 5 (.branch 4 (.leaf 4590499684) (.leaf 4430945823)) (.branch 6 (.leaf 4278445862) (.leaf 4132610848)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3993077944) (.leaf 3859508294)) (.branch 10 (.leaf 3731585103) (.leaf 3609011908))) (.branch 13 (.branch 12 (.leaf 3491511008) (.leaf 3378822043)) (.branch 14 (.leaf 3270700703) (.leaf 3166917552))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3067256957) (.branch 17 (.leaf 2971516103) (.leaf 2879504100))) (.branch 20 (.branch 19 (.leaf 2791041157) (.leaf 2705957826)) (.branch 21 (.leaf 2624094307) (.leaf 2545299808)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2469431952) (.leaf 2396356233)) (.branch 25 (.leaf 2325945509) (.leaf 2258079538))) (.branch 28 (.branch 27 (.leaf 2192644543) (.leaf 2129532809)) (.branch 29 (.leaf 2068642316) (.leaf 2009876383)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1953143353) (.branch 32 (.leaf 1898356292) (.leaf 1845432705))) (.branch 35 (.branch 34 (.leaf 1794294278) (.leaf 1744866635)) (.branch 36 (.leaf 1697079109) (.leaf 1650864528)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1606159022) (.leaf 1562901829)) (.branch 40 (.leaf 1521035127) (.leaf 1480503866))) (.branch 43 (.branch 42 (.leaf 1441255621) (.leaf 1403240440)) (.branch 44 (.leaf 1366410716) (.leaf 1330721060))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1296128176) (.branch 47 (.leaf 1262590758) (.leaf 1230069377))) (.branch 50 (.branch 49 (.leaf 1198526387) (.leaf 1167925830)) (.branch 51 (.leaf 1138233350) (.leaf 1109416106)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1081442700) (.leaf 1054283102)) (.branch 55 (.leaf 1027908577) (.leaf 1002291625))) (.branch 58 (.branch 57 (.leaf 977405914) (.leaf 953226228)) (.branch 59 (.leaf 929728408) (.leaf 906889301))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 884686709) (.branch 62 (.leaf 863099347) (.leaf 842106797))) (.branch 65 (.branch 64 (.leaf 821689464) (.leaf 801828541)) (.branch 66 (.leaf 782505969) (.leaf 763704403)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 745407178) (.leaf 727598278)) (.branch 70 (.leaf 710262307) (.leaf 693384457))) (.branch 73 (.branch 72 (.leaf 676950487) (.leaf 660946691)) (.branch 74 (.leaf 645359879) (.leaf 630177350))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 615386875) (.branch 77 (.leaf 600976671) (.leaf 586935386))) (.branch 80 (.branch 79 (.leaf 573252075) (.leaf 559916189)) (.branch 81 (.leaf 546917552) (.leaf 534246349)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 521893108) (.leaf 509848688)) (.branch 85 (.leaf 498104262) (.leaf 486651310))) (.branch 88 (.branch 87 (.leaf 475481596) (.leaf 464587168)) (.branch 89 (.leaf 453960339) (.leaf 443593676)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 433479996) (.branch 92 (.leaf 423612348) (.leaf 413984012))) (.branch 95 (.branch 94 (.leaf 404588483) (.leaf 395419464)) (.branch 96 (.leaf 386470863) (.leaf 377736778)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 369211496) (.leaf 360889479)) (.branch 100 (.leaf 352765365) (.leaf 344833956))) (.branch 103 (.branch 102 (.leaf 337090212) (.leaf 329529249)) (.branch 104 (.leaf 322146331) (.leaf 314936862))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 307896386) (.leaf 301020578)) (.branch 108 (.leaf 294305241) (.leaf 287746302))) (.branch 111 (.branch 110 (.leaf 281339806) (.leaf 275081913)) (.branch 112 (.leaf 268968893) (.leaf 262997124)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 257163087) (.leaf 251463362)) (.branch 116 (.leaf 245894625) (.leaf 240453647))) (.branch 119 (.branch 118 (.leaf 235137288) (.leaf 229942494)) (.branch 120 (.leaf 224866296) (.leaf 219905808)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 307).prefactor = (5097328365530033/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 307).cutoff/(generalMeanRows 307).c)).2 =
    (90234835681301/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 307).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 307).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 307).q*(generalMeanRows 307).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 307).q*(generalMeanRows 307).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 307).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 307

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 307).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 307).criticalRate j.val*(generalMeanRows 307).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 307).c*(generalMeanRows 307).criticalPoint j.val)).2-
      (generalMeanRows 307).J/2-(generalMeanRows 307).error (generalMeanGrid j.val)+
      (generalMeanRows 307).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 307).c)).2-
      (generalMeanRows 307).J/2-(generalMeanRows 307).error 4 := by
  have he : (generalMeanRows 307).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 307) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 307)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0307

/-! Kernel-checked entropy margins for general spectral rectangle 308. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0308
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5328919137) (.branch 2 (.leaf 5143110603) (.leaf 4965750045))) (.branch 5 (.branch 4 (.leaf 4796351701) (.leaf 4634464200)) (.branch 6 (.leaf 4479667566) (.leaf 4331570536)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4189808170) (.leaf 4054039697)) (.branch 10 (.leaf 3923946579) (.leaf 3799230765))) (.branch 13 (.branch 12 (.leaf 3679613107) (.leaf 3564831932)) (.branch 14 (.leaf 3454641735) (.leaf 3348811993))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3247126087) (.branch 17 (.leaf 3149380307) (.leaf 3055382953))) (.branch 20 (.branch 19 (.leaf 2964953499) (.leaf 2877921834)) (.branch 21 (.leaf 2794127558) (.leaf 2713419338)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2635654311) (.leaf 2560697533)) (.branch 25 (.leaf 2488421471) (.leaf 2418705530))) (.branch 28 (.branch 27 (.leaf 2351435621) (.leaf 2286503751)) (.branch 29 (.leaf 2223807648) (.leaf 2163250414)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2104740199) (.branch 32 (.leaf 2048189897) (.leaf 1993516864))) (.branch 35 (.branch 34 (.leaf 1940642656) (.leaf 1889492785)) (.branch 36 (.leaf 1839996487) (.leaf 1792086506)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1745698902) (.leaf 1700772853)) (.branch 40 (.leaf 1657250487) (.leaf 1615076715))) (.branch 43 (.branch 42 (.leaf 1574199075) (.leaf 1534567593)) (.branch 44 (.leaf 1496134639) (.leaf 1458854808))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1422684793) (.branch 47 (.leaf 1387583280) (.leaf 1353510834))) (.branch 50 (.branch 49 (.leaf 1320429808) (.leaf 1288304242)) (.branch 51 (.leaf 1257099779) (.leaf 1226783582)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1197324254) (.leaf 1168691765)) (.branch 55 (.leaf 1140857384) (.leaf 1113793609))) (.branch 58 (.branch 57 (.leaf 1087474113) (.leaf 1061873675)) (.branch 59 (.leaf 1036968136) (.leaf 1012734339))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 989150083) (.branch 62 (.leaf 966194074) (.leaf 943845887))) (.branch 65 (.branch 64 (.leaf 922085916) (.leaf 900895342)) (.branch 66 (.leaf 880256092) (.leaf 860150803)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 840562791) (.leaf 821476021)) (.branch 70 (.leaf 802875071) (.leaf 784745109))) (.branch 73 (.branch 72 (.leaf 767071863) (.leaf 749841599)) (.branch 74 (.leaf 733041092) (.leaf 716657608))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 700678879) (.branch 77 (.leaf 685093082) (.leaf 669888823))) (.branch 80 (.branch 79 (.leaf 655055113) (.leaf 640581355)) (.branch 81 (.leaf 626457325) (.leaf 612673157)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 599219327) (.leaf 586086637)) (.branch 85 (.leaf 573266205) (.leaf 560749449))) (.branch 88 (.branch 87 (.leaf 548528075) (.leaf 536594066)) (.branch 89 (.leaf 524939671) (.leaf 513557393)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 502439978) (.branch 92 (.leaf 491580409) (.leaf 480971891))) (.branch 95 (.branch 94 (.leaf 470607847) (.leaf 460481909)) (.branch 96 (.leaf 450587908) (.leaf 440919865)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 431471988) (.leaf 422238663)) (.branch 100 (.leaf 413214445) (.leaf 404394056))) (.branch 103 (.branch 102 (.leaf 395772373) (.leaf 387344430)) (.branch 104 (.leaf 379105404) (.leaf 371050617))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 363175526) (.leaf 355475718)) (.branch 108 (.leaf 347946911) (.leaf 340584943))) (.branch 111 (.branch 110 (.leaf 333385770) (.leaf 326345462)) (.branch 112 (.leaf 319460202) (.leaf 312726275)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 306140074) (.leaf 299698086)) (.branch 116 (.leaf 293396897) (.leaf 287233187))) (.branch 119 (.branch 118 (.leaf 281203722) (.leaf 275305359)) (.branch 120 (.leaf 269535035) (.leaf 263889773)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 308).prefactor = (5133339549181071/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 308).cutoff/(generalMeanRows 308).c)).2 =
    (37644352926117/100000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 308).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 308).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 308).q*(generalMeanRows 308).c/2-2 = (102/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable107.value]
    have hcontinuation : (generalMeanRows 308).q*(generalMeanRows 308).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 308).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 308

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 308).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 308).criticalRate j.val*(generalMeanRows 308).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 308).c*(generalMeanRows 308).criticalPoint j.val)).2-
      (generalMeanRows 308).J/2-(generalMeanRows 308).error (generalMeanGrid j.val)+
      (generalMeanRows 308).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 308).c)).2-
      (generalMeanRows 308).J/2-(generalMeanRows 308).error 4 := by
  have he : (generalMeanRows 308).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 308) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 308)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0308

/-! Kernel-checked entropy margins for general spectral rectangle 309. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0309
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5810966264) (.branch 2 (.leaf 5625773372) (.leaf 5448896827))) (.branch 5 (.branch 4 (.leaf 5279850794) (.leaf 5118184220)) (.branch 6 (.leaf 4963477803) (.leaf 4815341275)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4673410980) (.leaf 4537347686)) (.branch 10 (.leaf 4406834626) (.leaf 4281575723))) (.branch 13 (.branch 12 (.leaf 4161293986) (.leaf 4045730054)) (.branch 14 (.leaf 3934640874) (.leaf 3827798494))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3724988967) (.branch 17 (.leaf 3626011344) (.leaf 3530676755))) (.branch 20 (.branch 19 (.leaf 3438807566) (.leaf 3350236601)) (.branch 21 (.leaf 3264806433) (.leaf 3182368725)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3102783627) (.leaf 3025919216)) (.branch 25 (.leaf 2951650977) (.leaf 2879861329))) (.branch 28 (.branch 27 (.leaf 2810439182) (.leaf 2743279521)) (.branch 29 (.leaf 2678283031) (.leaf 2615355740)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2554408692) (.branch 32 (.leaf 2495357636) (.leaf 2438122745))) (.branch 35 (.branch 34 (.leaf 2382628351) (.leaf 2328802691)) (.branch 36 (.leaf 2276577684) (.leaf 2225888706)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2176674397) (.leaf 2128876465)) (.branch 40 (.leaf 2082439512) (.leaf 2037310871))) (.branch 43 (.branch 42 (.leaf 1993440445) (.leaf 1950780571)) (.branch 44 (.leaf 1909285874) (.leaf 1868913147))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1829621227) (.branch 47 (.leaf 1791370885) (.leaf 1754124720))) (.branch 50 (.branch 49 (.leaf 1717847056) (.leaf 1682503856)) (.branch 51 (.leaf 1648062629) (.leaf 1614492346)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1581763369) (.leaf 1549847373)) (.branch 55 (.leaf 1518717277) (.leaf 1488347183))) (.branch 58 (.branch 57 (.leaf 1458712309) (.leaf 1429788937)) (.branch 59 (.leaf 1401554357) (.leaf 1373986814))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1347065462) (.branch 62 (.leaf 1320770317) (.leaf 1295082213))) (.branch 65 (.branch 64 (.leaf 1269982766) (.leaf 1245454329)) (.branch 66 (.leaf 1221479960) (.leaf 1198043388)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1175128978) (.leaf 1152721702)) (.branch 70 (.leaf 1130807110) (.leaf 1109371300))) (.branch 73 (.branch 72 (.leaf 1088400899) (.leaf 1067883028)) (.branch 74 (.leaf 1047805289) (.leaf 1028155736))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1008922857) (.branch 77 (.leaf 990095553) (.leaf 971663121))) (.branch 80 (.branch 79 (.leaf 953615235) (.leaf 935941929)) (.branch 81 (.leaf 918633581) (.leaf 901680899)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 885074904) (.leaf 868806921)) (.branch 85 (.leaf 852868561) (.leaf 837251711))) (.branch 88 (.branch 87 (.leaf 821948521) (.leaf 806951397)) (.branch 89 (.leaf 792252985) (.leaf 777846164)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 763724035) (.branch 92 (.leaf 749879914) (.leaf 736307321))) (.branch 95 (.branch 94 (.leaf 722999973) (.leaf 709951776)) (.branch 96 (.leaf 697156818) (.leaf 684609361)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 672303835) (.leaf 660234829)) (.branch 100 (.leaf 648397091) (.leaf 636785514))) (.branch 103 (.branch 102 (.leaf 625395138) (.leaf 614221138)) (.branch 104 (.leaf 603258826) (.leaf 592503639))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 581951138) (.leaf 571597006)) (.branch 108 (.leaf 561437038) (.leaf 551467140))) (.branch 111 (.branch 110 (.leaf 541683327) (.leaf 532081716)) (.branch 112 (.leaf 522658525) (.leaf 513410067)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 504332748) (.leaf 495423067)) (.branch 116 (.leaf 486677606) (.leaf 478093035))) (.branch 119 (.branch 118 (.leaf 469666102) (.leaf 461393638)) (.branch 120 (.leaf 453272548) (.leaf 445299810)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 309).prefactor = (5116500578379481/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 309).cutoff/(generalMeanRows 309).c)).2 =
    (87285787898849/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 309).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 309).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 309).q*(generalMeanRows 309).c/2-2 = (171/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable097.value]
    have hcontinuation : (generalMeanRows 309).q*(generalMeanRows 309).cutoff/2-2 = (536/249:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable118.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 309).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 309

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 309).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 309).criticalRate j.val*(generalMeanRows 309).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 309).c*(generalMeanRows 309).criticalPoint j.val)).2-
      (generalMeanRows 309).J/2-(generalMeanRows 309).error (generalMeanGrid j.val)+
      (generalMeanRows 309).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 309).c)).2-
      (generalMeanRows 309).J/2-(generalMeanRows 309).error 4 := by
  have he : (generalMeanRows 309).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 309) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 309)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0309

/-! Kernel-checked entropy margins for general spectral rectangle 310. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0310
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5647408067) (.branch 2 (.leaf 5446531584) (.leaf 5254843833))) (.branch 5 (.branch 4 (.leaf 5071817479) (.leaf 4896962427)) (.branch 6 (.leaf 4729822568) (.leaf 4569972886)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4417016867) (.leaf 4270584171)) (.branch 10 (.leaf 4130328537) (.leaf 3995925895))) (.branch 13 (.branch 12 (.leaf 3867072655) (.leaf 3743484160)) (.branch 14 (.leaf 3624893274) (.leaf 3511049103))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3401715821) (.branch 17 (.leaf 3296671605) (.leaf 3195707656))) (.branch 20 (.branch 19 (.leaf 3098627296) (.leaf 3005245151)) (.branch 21 (.leaf 2915386384) (.leaf 2828886005)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2745588220) (.leaf 2665345835)) (.branch 25 (.leaf 2588019713) (.leaf 2513478255))) (.branch 28 (.branch 27 (.leaf 2441596935) (.leaf 2372257857)) (.branch 29 (.leaf 2305349348) (.leaf 2240765586)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2178406238) (.branch 32 (.leaf 2118176140) (.leaf 2059984988))) (.branch 35 (.branch 34 (.leaf 2003747054) (.leaf 1949380919)) (.branch 36 (.leaf 1896809225) (.leaf 1845958444)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1796758657) (.leaf 1749143355)) (.branch 40 (.leaf 1703049247) (.leaf 1658416077))) (.branch 43 (.branch 42 (.leaf 1615186465) (.leaf 1573305742)) (.branch 44 (.leaf 1532721807) (.leaf 1493384988))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1455247910) (.branch 47 (.leaf 1418265375) (.leaf 1382394244))) (.branch 50 (.branch 49 (.leaf 1347593331) (.leaf 1313823302)) (.branch 51 (.leaf 1281046575) (.leaf 1249227235)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1218330943) (.leaf 1188324860)) (.branch 55 (.leaf 1159177569) (.leaf 1130859004))) (.branch 58 (.branch 57 (.leaf 1103340383) (.leaf 1076594144)) (.branch 59 (.leaf 1050593883) (.leaf 1025314299))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1000731141) (.branch 62 (.leaf 976821156) (.leaf 953562038))) (.branch 65 (.branch 64 (.leaf 930932388) (.leaf 908911668)) (.branch 66 (.leaf 887480160) (.leaf 866618927)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 846309777) (.leaf 826535232)) (.branch 70 (.leaf 807278487) (.leaf 788523387))) (.branch 73 (.branch 72 (.leaf 770254393) (.leaf 752456555)) (.branch 74 (.leaf 735115485) (.leaf 718217333))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 701748762) (.branch 77 (.leaf 685696927) (.leaf 670049450))) (.branch 80 (.branch 79 (.leaf 654794403) (.leaf 639920286)) (.branch 81 (.leaf 625416010) (.leaf 611270879)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 597474573) (.leaf 584017133)) (.branch 85 (.leaf 570888944) (.leaf 558080723))) (.branch 88 (.branch 87 (.leaf 545583501) (.leaf 533388617)) (.branch 89 (.leaf 521487699) (.leaf 509872653)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 498535657) (.branch 92 (.leaf 487469145) (.leaf 476665796))) (.branch 95 (.branch 94 (.leaf 466118528) (.leaf 455820489)) (.branch 96 (.leaf 445765044) (.leaf 435945768)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 426356440) (.leaf 416991033)) (.branch 100 (.leaf 407843708) (.leaf 398908805))) (.branch 103 (.branch 102 (.leaf 390180839) (.leaf 381654492)) (.branch 104 (.leaf 373324606) (.leaf 365186177))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 357234354) (.leaf 349464425)) (.branch 108 (.leaf 341871821) (.leaf 334452105))) (.branch 111 (.branch 110 (.leaf 327200968) (.leaf 320114227)) (.branch 112 (.leaf 313187820) (.leaf 306417798)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 299800328) (.leaf 293331681)) (.branch 116 (.leaf 287008234) (.leaf 280826468))) (.branch 119 (.branch 118 (.leaf 274782957) (.leaf 268874372)) (.branch 120 (.leaf 263097474) (.leaf 257449113)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 310).prefactor = (1103169000447277/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 310).cutoff/(generalMeanRows 310).c)).2 =
    (363346082755771/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 310).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 310).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 310).q*(generalMeanRows 310).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 310).q*(generalMeanRows 310).cutoff/2-2 = (862/415:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable117.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 310).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 310

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 310).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 310).criticalRate j.val*(generalMeanRows 310).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 310).c*(generalMeanRows 310).criticalPoint j.val)).2-
      (generalMeanRows 310).J/2-(generalMeanRows 310).error (generalMeanGrid j.val)+
      (generalMeanRows 310).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 310).c)).2-
      (generalMeanRows 310).J/2-(generalMeanRows 310).error 4 := by
  have he : (generalMeanRows 310).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 310) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 310)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0310

/-! Kernel-checked entropy margins for general spectral rectangle 311. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0311
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5758357757) (.branch 2 (.leaf 5571881357) (.leaf 5393770481))) (.branch 5 (.branch 4 (.leaf 5223539512) (.leaf 5060737464)) (.branch 6 (.leaf 4904944967) (.leaf 4755771557)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4612853272) (.leaf 4475850472)) (.branch 10 (.leaf 4344445894) (.leaf 4218342880))) (.branch 13 (.branch 12 (.leaf 4097263791) (.leaf 3980948553)) (.branch 14 (.leaf 3869153345) (.leaf 3761649400))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3658221914) (.branch 17 (.leaf 3558669045) (.leaf 3462801003))) (.branch 20 (.branch 19 (.leaf 3370439205) (.leaf 3281415512)) (.branch 21 (.leaf 3195571514) (.leaf 3112757881)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3032833762) (.leaf 2955666226)) (.branch 25 (.leaf 2881129753) (.leaf 2809105754))) (.branch 28 (.branch 27 (.leaf 2739482133) (.leaf 2672152878)) (.branch 29 (.leaf 2607017682) (.leaf 2543981589)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2482954671) (.branch 32 (.leaf 2423851716) (.leaf 2366591950))) (.branch 35 (.branch 34 (.leaf 2311098771) (.leaf 2257299497)) (.branch 36 (.leaf 2205125144) (.leaf 2154510202)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2105392440) (.leaf 2057712714)) (.branch 40 (.leaf 2011414792) (.leaf 1966445190))) (.branch 43 (.branch 42 (.leaf 1922753014) (.leaf 1880289819)) (.branch 44 (.leaf 1839009472) (.leaf 1798868021))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1759823582) (.branch 47 (.leaf 1721836220) (.leaf 1684867846))) (.branch 50 (.branch 49 (.leaf 1648882119) (.leaf 1613844350)) (.branch 51 (.leaf 1579721416) (.leaf 1546481676)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1514094896) (.leaf 1482532171)) (.branch 55 (.leaf 1451765860) (.leaf 1421769519))) (.branch 58 (.branch 57 (.leaf 1392517840) (.leaf 1363986592)) (.branch 59 (.leaf 1336152570) (.leaf 1308993539))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1282488188) (.branch 62 (.leaf 1256616084) (.leaf 1231357627))) (.branch 65 (.branch 64 (.leaf 1206694011) (.leaf 1182607184)) (.branch 66 (.leaf 1159079811) (.leaf 1136095241)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1113637474) (.leaf 1091691127)) (.branch 70 (.leaf 1070241410) (.leaf 1049274093))) (.branch 73 (.branch 72 (.leaf 1028775482) (.leaf 1008732396)) (.branch 74 (.leaf 989132141) (.leaf 969962485))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 951211645) (.branch 77 (.leaf 932868258) (.leaf 914921367))) (.branch 80 (.branch 79 (.leaf 897360403) (.leaf 880175165)) (.branch 81 (.leaf 863355807) (.leaf 846892818)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 830777014) (.leaf 814999517)) (.branch 85 (.leaf 799551748) (.leaf 784425409))) (.branch 88 (.branch 87 (.leaf 769612475) (.leaf 755105182)) (.branch 89 (.leaf 740896013) (.leaf 726977693)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 713343173) (.branch 92 (.leaf 699985628) (.leaf 686898440))) (.branch 95 (.branch 94 (.leaf 674075198) (.leaf 661509683)) (.branch 96 (.leaf 649195864) (.leaf 637127889)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 625300080) (.leaf 613706924)) (.branch 100 (.leaf 602343070) (.leaf 591203318))) (.branch 103 (.branch 102 (.leaf 580282619) (.leaf 569576065)) (.branch 104 (.leaf 559078885) (.leaf 548786441))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 538694224) (.leaf 528797846)) (.branch 108 (.leaf 519093039) (.leaf 509575647))) (.branch 111 (.branch 110 (.leaf 500241629) (.leaf 491087047)) (.branch 112 (.leaf 482108067) (.leaf 473300955)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 464662074) (.leaf 456187877)) (.branch 116 (.leaf 447874910) (.leaf 439719804))) (.branch 119 (.branch 118 (.leaf 431719276) (.leaf 423870124)) (.branch 120 (.leaf 416169222) (.leaf 408613524)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 311).prefactor = (2562449218875857/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 311).cutoff/(generalMeanRows 311).c)).2 =
    (211129802397437/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 311).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 311).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 311).q*(generalMeanRows 311).c/2-2 = (353/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable084.value]
    have hcontinuation : (generalMeanRows 311).q*(generalMeanRows 311).cutoff/2-2 = (1066/501:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable119.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 311).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 311

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 311).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 311).criticalRate j.val*(generalMeanRows 311).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 311).c*(generalMeanRows 311).criticalPoint j.val)).2-
      (generalMeanRows 311).J/2-(generalMeanRows 311).error (generalMeanGrid j.val)+
      (generalMeanRows 311).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 311).c)).2-
      (generalMeanRows 311).J/2-(generalMeanRows 311).error 4 := by
  have he : (generalMeanRows 311).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 311) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 311)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0311

/-! Kernel-checked entropy margins for general spectral rectangle 312. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0312
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5064346758) (.branch 2 (.leaf 4892852933) (.leaf 4729179293))) (.branch 5 (.branch 4 (.leaf 4572868086) (.leaf 4423494398)) (.branch 6 (.leaf 4280663287) (.leaf 4144007220)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4013183781) (.leaf 3887873603)) (.branch 10 (.leaf 3767778517) (.leaf 3652619876))) (.branch 13 (.branch 12 (.leaf 3542137030) (.leaf 3436085959)) (.branch 14 (.leaf 3334238016) (.leaf 3236378788))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3142307058) (.branch 17 (.leaf 3051833856) (.leaf 2964781587))) (.branch 20 (.branch 19 (.leaf 2880983232) (.leaf 2800281621)) (.branch 21 (.leaf 2722528752) (.leaf 2647585179)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2575319433) (.leaf 2505607499)) (.branch 25 (.leaf 2438332328) (.leaf 2373383381))) (.branch 28 (.branch 27 (.leaf 2310656219) (.leaf 2250052108)) (.branch 29 (.leaf 2191477665) (.leaf 2134844524)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2080069021) (.branch 32 (.leaf 2027071912) (.leaf 1975778100))) (.branch 35 (.branch 34 (.leaf 1926116387) (.leaf 1878019240)) (.branch 36 (.leaf 1831422574) (.leaf 1786265547)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1742490373) (.leaf 1700042144)) (.branch 40 (.leaf 1658868664) (.leaf 1618920291))) (.branch 43 (.branch 42 (.leaf 1580149797) (.leaf 1542512229)) (.branch 44 (.leaf 1505964782) (.leaf 1470466677))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1435979055) (.branch 47 (.leaf 1402464865) (.leaf 1369888770))) (.branch 50 (.branch 49 (.leaf 1338217052) (.leaf 1307417525)) (.branch 51 (.leaf 1277459452) (.leaf 1248313473)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1219951526) (.leaf 1192346781)) (.branch 55 (.leaf 1165473579) (.leaf 1139307365))) (.branch 58 (.branch 57 (.leaf 1113824639) (.leaf 1089002895)) (.branch 59 (.leaf 1064820575) (.leaf 1041257019))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1018292421) (.branch 62 (.leaf 995907786) (.leaf 974084890))) (.branch 65 (.branch 64 (.leaf 952806242) (.leaf 932055050)) (.branch 66 (.leaf 911815182) (.leaf 892071141)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 872808030) (.leaf 854011524)) (.branch 70 (.leaf 835667846) (.leaf 817763738))) (.branch 73 (.branch 72 (.leaf 800286436) (.leaf 783223653)) (.branch 74 (.leaf 766563551) (.leaf 750294723))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 734406173) (.branch 77 (.leaf 718887300) (.leaf 703727877))) (.branch 80 (.branch 79 (.leaf 688918035) (.leaf 674448249)) (.branch 81 (.leaf 660309322) (.leaf 646492372)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 632988816) (.leaf 619790359)) (.branch 85 (.leaf 606888982) (.leaf 594276930))) (.branch 88 (.branch 87 (.leaf 581946701) (.leaf 569891035)) (.branch 89 (.leaf 558102905) (.leaf 546575509)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 535302256) (.branch 92 (.leaf 524276764) (.leaf 513492847))) (.branch 95 (.branch 94 (.leaf 502944507) (.leaf 492625933)) (.branch 96 (.leaf 482531485) (.leaf 472655695)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 462993254) (.leaf 453539013)) (.branch 100 (.leaf 444287970) (.leaf 435235269))) (.branch 103 (.branch 102 (.leaf 426376196) (.leaf 417706167)) (.branch 104 (.leaf 409220730) (.leaf 400915559))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 392786446) (.leaf 384829301)) (.branch 108 (.leaf 377040147) (.leaf 369415113))) (.branch 111 (.branch 110 (.leaf 361950434) (.leaf 354642446)) (.branch 112 (.leaf 347487583) (.leaf 340482375)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 333623439) (.leaf 326907484)) (.branch 116 (.leaf 320331305) (.leaf 313891776))) (.branch 119 (.branch 118 (.leaf 307585855) (.leaf 301410576)) (.branch 120 (.leaf 295363047) (.leaf 289440451)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 312).prefactor = (2431632069524463/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 312).cutoff/(generalMeanRows 312).c)).2 =
    (206661346723247/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 312).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 312).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 312).q*(generalMeanRows 312).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 312).q*(generalMeanRows 312).cutoff/2-2 = (8486/3841:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable131.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 312).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 312

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 312).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 312).criticalRate j.val*(generalMeanRows 312).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 312).c*(generalMeanRows 312).criticalPoint j.val)).2-
      (generalMeanRows 312).J/2-(generalMeanRows 312).error (generalMeanGrid j.val)+
      (generalMeanRows 312).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 312).c)).2-
      (generalMeanRows 312).J/2-(generalMeanRows 312).error 4 := by
  have he : (generalMeanRows 312).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 312) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 312)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0312

/-! Kernel-checked entropy margins for general spectral rectangle 313. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0313
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5458757422) (.branch 2 (.leaf 5271101860) (.leaf 5091946005))) (.branch 5 (.branch 4 (.leaf 4920800798) (.leaf 4757211838)) (.branch 6 (.leaf 4600756354) (.leaf 4451040511)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4307696994) (.leaf 4170382840)) (.branch 10 (.leaf 4038777489) (.leaf 3912581017))) (.branch 13 (.branch 12 (.leaf 3791512549) (.leaf 3675308811)) (.branch 14 (.leaf 3563722817) (.leaf 3456522675))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3353490496) (.branch 17 (.leaf 3254421396) (.leaf 3159122582))) (.branch 20 (.branch 19 (.leaf 3067412522) (.leaf 2979120167)) (.branch 21 (.leaf 2894084251) (.leaf 2812152635)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2733181710) (.leaf 2657035840)) (.branch 25 (.leaf 2583586849) (.leaf 2512713548))) (.branch 28 (.branch 27 (.leaf 2444301291) (.leaf 2378241574)) (.branch 29 (.leaf 2314431649) (.leaf 2252774175)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2193176890) (.branch 32 (.leaf 2135552307) (.leaf 2079817427))) (.branch 35 (.branch 34 (.leaf 2025893478) (.leaf 1973705664)) (.branch 36 (.leaf 1923182935) (.leaf 1874257774)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1826865991) (.leaf 1780946537)) (.branch 40 (.leaf 1736441326) (.leaf 1693295068))) (.branch 43 (.branch 42 (.leaf 1651455118) (.leaf 1610871326)) (.branch 44 (.leaf 1571495903) (.leaf 1533283291))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1496190042) (.branch 47 (.leaf 1460174709) (.leaf 1425197734))) (.branch 50 (.branch 49 (.leaf 1391221352) (.leaf 1358209493)) (.branch 51 (.leaf 1326127699) (.leaf 1294943033)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1264624007) (.leaf 1235140503)) (.branch 55 (.leaf 1206463708) (.leaf 1178566042))) (.branch 58 (.branch 57 (.leaf 1151421100) (.leaf 1125003594)) (.branch 59 (.leaf 1099289292) (.leaf 1074254974))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1049878374) (.branch 62 (.leaf 1026138139) (.leaf 1003013782))) (.branch 65 (.branch 64 (.leaf 980485643) (.leaf 958534845)) (.branch 66 (.leaf 937143262) (.leaf 916293477)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 895968757) (.leaf 876153012)) (.branch 70 (.leaf 856830772) (.leaf 837987156))) (.branch 73 (.branch 72 (.leaf 819607844) (.leaf 801679052)) (.branch 74 (.leaf 784187509) (.leaf 767120433))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 750465508) (.branch 77 (.leaf 734210866) (.leaf 718345064))) (.branch 80 (.branch 79 (.leaf 702857069) (.leaf 687736236)) (.branch 81 (.leaf 672972295) (.leaf 658555333)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 644475779) (.leaf 630724389)) (.branch 85 (.leaf 617292234) (.leaf 604170685))) (.branch 88 (.branch 87 (.leaf 591351401) (.leaf 578826319)) (.branch 89 (.leaf 566587639) (.leaf 554627816)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 542939549) (.branch 92 (.leaf 531515773) (.leaf 520349645))) (.branch 95 (.branch 94 (.leaf 509434540) (.leaf 498764040)) (.branch 96 (.leaf 488331928) (.leaf 478132176)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 468158943) (.leaf 458406565)) (.branch 100 (.leaf 448869548) (.leaf 439542564))) (.branch 103 (.branch 102 (.leaf 430420440) (.leaf 421498160)) (.branch 104 (.leaf 412770852) (.leaf 404233785))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 395882367) (.leaf 387712136)) (.branch 108 (.leaf 379718756) (.leaf 371898016))) (.branch 111 (.branch 110 (.leaf 364245821) (.leaf 356758192)) (.branch 112 (.leaf 349431257) (.leaf 342261254)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 335244521) (.leaf 328377496)) (.branch 116 (.leaf 321656716) (.leaf 315078806))) (.branch 119 (.branch 118 (.leaf 308640483) (.leaf 302338553)) (.branch 120 (.leaf 296169902) (.leaf 290131500)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 313).prefactor = (646200642707821/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 313).cutoff/(generalMeanRows 313).c)).2 =
    (96071676680549/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 313).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 313).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 313).q*(generalMeanRows 313).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 313).q*(generalMeanRows 313).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 313).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 313

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 313).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 313).criticalRate j.val*(generalMeanRows 313).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 313).c*(generalMeanRows 313).criticalPoint j.val)).2-
      (generalMeanRows 313).J/2-(generalMeanRows 313).error (generalMeanGrid j.val)+
      (generalMeanRows 313).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 313).c)).2-
      (generalMeanRows 313).J/2-(generalMeanRows 313).error 4 := by
  have he : (generalMeanRows 313).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 313) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 313)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0313

/-! Kernel-checked entropy margins for general spectral rectangle 314. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0314
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5689486783) (.branch 2 (.leaf 5499544717) (.leaf 5318144732))) (.branch 5 (.branch 4 (.leaf 5144794500) (.leaf 4979036638)) (.branch 6 (.leaf 4820445664) (.leaf 4668625274)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4523205903) (.leaf 4383842543)) (.branch 10 (.leaf 4250212768) (.leaf 4122014963))) (.branch 13 (.branch 12 (.leaf 3998966713) (.leaf 3880803346)) (.branch 14 (.leaf 3767276609) (.leaf 3658153460))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3553214970) (.branch 17 (.leaf 3452255316) (.leaf 3355080860))) (.branch 20 (.branch 19 (.leaf 3261509303) (.leaf 3171368913)) (.branch 21 (.leaf 3084497809) (.leaf 3000743305)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2919961301) (.leaf 2842015728)) (.branch 25 (.leaf 2766778028) (.leaf 2694126672))) (.branch 28 (.branch 27 (.leaf 2623946724) (.leaf 2556129419)) (.branch 29 (.leaf 2490571791) (.leaf 2427176309)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2365850553) (.branch 32 (.leaf 2306506904) (.leaf 2249062254))) (.branch 35 (.branch 34 (.leaf 2193437746) (.leaf 2139558518)) (.branch 36 (.leaf 2087353473) (.leaf 2036755062)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1987699077) (.leaf 1940124467)) (.branch 40 (.leaf 1893973152) (.leaf 1849189864))) (.branch 43 (.branch 42 (.leaf 1805721982) (.leaf 1763519393)) (.branch 44 (.leaf 1722534350) (.leaf 1682721344))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1644036982) (.branch 47 (.leaf 1606439874) (.leaf 1569890524))) (.branch 50 (.branch 49 (.leaf 1534351233) (.leaf 1499785998)) (.branch 51 (.leaf 1466160428) (.leaf 1433441660)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1401598274) (.leaf 1370600225)) (.branch 55 (.leaf 1340418771) (.leaf 1311026402))) (.branch 58 (.branch 57 (.leaf 1282396785) (.leaf 1254504699)) (.branch 59 (.leaf 1227325982) (.leaf 1200837477))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1175016985) (.branch 62 (.leaf 1149843215) (.leaf 1125295740))) (.branch 65 (.branch 64 (.leaf 1101354957) (.leaf 1078002045)) (.branch 66 (.leaf 1055218929) (.leaf 1032988246)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1011293307) (.leaf 990118067)) (.branch 70 (.leaf 969447099) (.leaf 949265560))) (.branch 73 (.branch 72 (.leaf 929559164) (.leaf 910314162)) (.branch 74 (.leaf 891517311) (.leaf 873155856))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 855217504) (.branch 77 (.leaf 837690408) (.leaf 820563142))) (.branch 80 (.branch 79 (.leaf 803824687) (.leaf 787464411)) (.branch 81 (.leaf 771472051) (.leaf 755837699)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 740551787) (.leaf 725605071)) (.branch 85 (.leaf 710988619) (.leaf 696693795))) (.branch 88 (.branch 87 (.leaf 682712251) (.leaf 669035911)) (.branch 89 (.leaf 655656962) (.leaf 642567841)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 629761231) (.branch 92 (.leaf 617230041) (.leaf 604967408))) (.branch 95 (.branch 94 (.leaf 592966679) (.leaf 581221409)) (.branch 96 (.leaf 569725347) (.leaf 558472435)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 547456796) (.leaf 536672728)) (.branch 100 (.leaf 526114700) (.leaf 515777340))) (.branch 103 (.branch 102 (.leaf 505655436) (.leaf 495743925)) (.branch 104 (.leaf 486037888) (.leaf 476532549))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 467223264) (.leaf 458105519)) (.branch 108 (.leaf 449174929) (.leaf 440427225))) (.branch 111 (.branch 110 (.leaf 431858259) (.leaf 423463993)) (.branch 112 (.leaf 415240499) (.leaf 407183954)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 399290638) (.leaf 391556926)) (.branch 116 (.leaf 383979291) (.leaf 376554296))) (.branch 119 (.branch 118 (.leaf 369278595) (.leaf 362148925)) (.branch 120 (.leaf 355162108) (.leaf 348315046)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 314).prefactor = (5206126940300977/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 314).cutoff/(generalMeanRows 314).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 314).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 314).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 314).q*(generalMeanRows 314).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 314).q*(generalMeanRows 314).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 314).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 314

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 314).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 314).criticalRate j.val*(generalMeanRows 314).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 314).c*(generalMeanRows 314).criticalPoint j.val)).2-
      (generalMeanRows 314).J/2-(generalMeanRows 314).error (generalMeanGrid j.val)+
      (generalMeanRows 314).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 314).c)).2-
      (generalMeanRows 314).J/2-(generalMeanRows 314).error 4 := by
  have he : (generalMeanRows 314).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 314) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 314)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0314

/-! Kernel-checked entropy margins for general spectral rectangle 315. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0315
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5770159978) (.branch 2 (.leaf 5577524657) (.leaf 5393552540))) (.branch 5 (.branch 4 (.leaf 5217744314) (.leaf 5049636115)) (.branch 6 (.leaf 4888796425) (.leaf 4734823321)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4587341999) (.leaf 4446002557)) (.branch 10 (.leaf 4310478000) (.leaf 4180462434))) (.branch 13 (.branch 12 (.leaf 4055669440) (.leaf 3935830594)) (.branch 14 (.leaf 3820694122) (.leaf 3710023679))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3603597230) (.branch 17 (.leaf 3501206034) (.leaf 3402653708))) (.branch 20 (.branch 19 (.leaf 3307755367) (.leaf 3216336846)) (.branch 21 (.leaf 3128233967) (.leaf 3043291878)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2961364439) (.leaf 2882313649)) (.branch 25 (.leaf 2806009127) (.leaf 2732327623))) (.branch 28 (.branch 27 (.leaf 2661152569) (.leaf 2592373659)) (.branch 29 (.leaf 2525886467) (.leaf 2461592078)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2399396764) (.branch 32 (.leaf 2339211660) (.leaf 2280952483))) (.branch 35 (.branch 34 (.leaf 2224539256) (.leaf 2169896056)) (.branch 36 (.leaf 2116950778) (.leaf 2065634914)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2015883348) (.leaf 1967634161)) (.branch 40 (.leaf 1920828451) (.leaf 1875410164))) (.branch 43 (.branch 42 (.leaf 1831325936) (.leaf 1788524942)) (.branch 44 (.leaf 1746958758) (.leaf 1706581230))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1667348349) (.branch 47 (.leaf 1629218138) (.leaf 1592150543))) (.branch 50 (.branch 49 (.leaf 1556107328) (.leaf 1521051980)) (.branch 51 (.leaf 1486949622) (.leaf 1453766923)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1421472019) (.leaf 1390034438)) (.branch 55 (.leaf 1359425030) (.leaf 1329615897))) (.branch 58 (.branch 57 (.leaf 1300580331) (.leaf 1272292753)) (.branch 59 (.leaf 1244728660) (.leaf 1217864566))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1191677956) (.branch 62 (.leaf 1166147239) (.leaf 1141251696))) (.branch 65 (.branch 64 (.leaf 1116971448) (.leaf 1093287407)) (.branch 66 (.leaf 1070181242) (.leaf 1047635343)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1025632783) (.leaf 1004157293)) (.branch 70 (.leaf 983193224) (.leaf 962725523))) (.branch 73 (.branch 72 (.leaf 942739704) (.leaf 923221820)) (.branch 74 (.leaf 904158442) (.leaf 885536633))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 867343928) (.branch 77 (.leaf 849568309) (.leaf 832198190))) (.branch 80 (.branch 79 (.leaf 815222395) (.leaf 798630140)) (.branch 81 (.leaf 782411019) (.leaf 766554982)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 751052326) (.leaf 735893676)) (.branch 85 (.leaf 721069972) (.leaf 706572457))) (.branch 88 (.branch 87 (.leaf 692392664) (.leaf 678522402)) (.branch 89 (.leaf 664953748) (.leaf 651679032)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 638690832) (.branch 92 (.leaf 625981959) (.leaf 613545450))) (.branch 95 (.branch 94 (.leaf 601374558) (.leaf 589462747)) (.branch 96 (.leaf 577803679) (.leaf 566391208)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 555219374) (.leaf 544282396)) (.branch 100 (.leaf 533574661) (.leaf 523090725))) (.branch 103 (.branch 102 (.leaf 512825299) (.leaf 502773249)) (.branch 104 (.leaf 492929587) (.leaf 483289468))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 473848183) (.leaf 464601155)) (.branch 108 (.leaf 455543935) (.leaf 446672194))) (.branch 111 (.branch 110 (.leaf 437981726) (.leaf 429468434)) (.branch 112 (.leaf 421128337) (.leaf 412957556)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 404952317) (.leaf 397108946)) (.branch 116 (.leaf 389423866) (.leaf 381893589))) (.branch 119 (.branch 118 (.leaf 374514723) (.leaf 367283959)) (.branch 120 (.leaf 360198074) (.leaf 353253925)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 315).prefactor = (2639973204466037/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 315).cutoff/(generalMeanRows 315).c)).2 =
    (50020006984811/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 315).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 315).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 315).q*(generalMeanRows 315).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 315).q*(generalMeanRows 315).cutoff/2-2 = (265/126:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable030.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 315).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 315

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 315).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 315).criticalRate j.val*(generalMeanRows 315).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 315).c*(generalMeanRows 315).criticalPoint j.val)).2-
      (generalMeanRows 315).J/2-(generalMeanRows 315).error (generalMeanGrid j.val)+
      (generalMeanRows 315).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 315).c)).2-
      (generalMeanRows 315).J/2-(generalMeanRows 315).error 4 := by
  have he : (generalMeanRows 315).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 315) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 315)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0315

/-! Kernel-checked entropy margins for general spectral rectangle 316. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0316
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5031926832) (.branch 2 (.leaf 4859017793) (.leaf 4694051499))) (.branch 5 (.branch 4 (.leaf 4536561158) (.leaf 4386113538)) (.branch 6 (.leaf 4242306042) (.leaf 4104764087)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3973138755) (.leaf 3847104685)) (.branch 10 (.leaf 3726358175) (.leaf 3610615467))) (.branch 13 (.branch 12 (.leaf 3499611190) (.leaf 3393096957)) (.branch 14 (.leaf 3290840083) (.leaf 3192622417))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3098239280) (.branch 17 (.leaf 3007498494) (.leaf 2920219490))) (.branch 20 (.branch 19 (.leaf 2836232492) (.leaf 2755377769)) (.branch 21 (.leaf 2677504944) (.leaf 2602472364)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2530146508) (.leaf 2460401453)) (.branch 25 (.leaf 2393118374) (.leaf 2328185082))) (.branch 28 (.branch 27 (.leaf 2265495598) (.leaf 2204949754)) (.branch 29 (.leaf 2146452831) (.leaf 2089915214)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2035252076) (.branch 32 (.leaf 1982383086) (.leaf 1931232129))) (.branch 35 (.branch 34 (.leaf 1881727059) (.leaf 1833799452)) (.branch 36 (.leaf 1787384391) (.leaf 1742420254)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1698848525) (.leaf 1656613609)) (.branch 40 (.leaf 1615662665) (.leaf 1575945449))) (.branch 43 (.branch 42 (.leaf 1537414162) (.leaf 1500023318)) (.branch 44 (.leaf 1463729606) (.leaf 1428491776))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1394270520) (.branch 47 (.leaf 1361028366) (.leaf 1328729578))) (.branch 50 (.branch 49 (.leaf 1297340063) (.leaf 1266827280)) (.branch 51 (.leaf 1237160156) (.leaf 1208309011)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1180245482) (.leaf 1152942454)) (.branch 55 (.leaf 1126373996) (.leaf 1100515298))) (.branch 58 (.branch 57 (.leaf 1075342613) (.leaf 1050833203)) (.branch 59 (.leaf 1026965290) (.leaf 1003718003))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 981071337) (.branch 62 (.leaf 959006106) (.leaf 937503903))) (.branch 65 (.branch 64 (.leaf 916547066) (.leaf 896118634)) (.branch 66 (.leaf 876202322) (.leaf 856782479)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 837844065) (.leaf 819372619)) (.branch 70 (.leaf 801354229) (.leaf 783775514))) (.branch 73 (.branch 72 (.leaf 766623589) (.leaf 749886052)) (.branch 74 (.leaf 733550955) (.leaf 717606785))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 702042447) (.branch 77 (.leaf 686847241) (.leaf 672010848))) (.branch 80 (.branch 79 (.leaf 657523311) (.leaf 643375021)) (.branch 81 (.leaf 629556700) (.leaf 616059387)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 602874425) (.leaf 589993449)) (.branch 85 (.leaf 577408370) (.leaf 565111370))) (.branch 88 (.branch 87 (.leaf 553094884) (.leaf 541351592)) (.branch 89 (.leaf 529874411) (.leaf 518656484)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 507691169) (.branch 92 (.leaf 496972033) (.leaf 486492844))) (.branch 95 (.branch 94 (.leaf 476247561) (.leaf 466230326)) (.branch 96 (.leaf 456435462) (.leaf 446857460)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 437490976) (.leaf 428330825)) (.branch 100 (.leaf 419371973) (.leaf 410609532))) (.branch 103 (.branch 102 (.leaf 402038758) (.leaf 393655041)) (.branch 104 (.leaf 385453901) (.leaf 377430988))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 369582071) (.leaf 361903039)) (.branch 108 (.leaf 354389892) (.leaf 347038743))) (.branch 111 (.branch 110 (.leaf 339845808) (.leaf 332807409)) (.branch 112 (.leaf 325919962) (.leaf 319179984)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 312584082) (.leaf 306128951)) (.branch 116 (.leaf 299811375) (.leaf 293628222))) (.branch 119 (.branch 118 (.leaf 287576439) (.leaf 281653054)) (.branch 120 (.leaf 275855169) (.leaf 270179961)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 316).prefactor = (2475240021787913/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 316).cutoff/(generalMeanRows 316).c)).2 =
    (12863636621361/31250000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 316).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 316).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 316).q*(generalMeanRows 316).c/2-2 = (3223/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable132.value]
    have hcontinuation : (generalMeanRows 316).q*(generalMeanRows 316).cutoff/2-2 = (4266/1909:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable133.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 316).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 316

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 316).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 316).criticalRate j.val*(generalMeanRows 316).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 316).c*(generalMeanRows 316).criticalPoint j.val)).2-
      (generalMeanRows 316).J/2-(generalMeanRows 316).error (generalMeanGrid j.val)+
      (generalMeanRows 316).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 316).c)).2-
      (generalMeanRows 316).J/2-(generalMeanRows 316).error 4 := by
  have he : (generalMeanRows 316).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 316) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 316)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0316

/-! Kernel-checked entropy margins for general spectral rectangle 317. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0317
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5152838728) (.branch 2 (.leaf 4978361518) (.leaf 4811869063))) (.branch 5 (.branch 4 (.leaf 4652891691) (.leaf 4500993533)) (.branch 6 (.leaf 4355769572) (.leaf 4216843000)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4083862858) (.leaf 3956501909)) (.branch 10 (.leaf 3834454726) (.leaf 3717435964))) (.branch 13 (.branch 12 (.leaf 3605178793) (.leaf 3497433484)) (.branch 14 (.leaf 3393966115) (.leaf 3294557399))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3199001612) (.branch 17 (.leaf 3107105613) (.leaf 3018687946))) (.branch 20 (.branch 19 (.leaf 2933578023) (.leaf 2851615360)) (.branch 21 (.leaf 2772648894) (.leaf 2696536335)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2623143581) (.leaf 2552344174)) (.branch 25 (.leaf 2484018795) (.leaf 2418054805))) (.branch 28 (.branch 27 (.leaf 2354345808) (.leaf 2292791258)) (.branch 29 (.leaf 2233296086) (.leaf 2175770355)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2120128947) (.branch 32 (.leaf 2066291259) (.leaf 2014180934))) (.branch 35 (.branch 34 (.leaf 1963725597) (.leaf 1914856620)) (.branch 36 (.leaf 1867508896) (.leaf 1821620633)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1777133155) (.leaf 1733990725)) (.branch 40 (.leaf 1692140371) (.leaf 1651531727))) (.branch 43 (.branch 42 (.leaf 1612116887) (.leaf 1573850264)) (.branch 44 (.leaf 1536688457) (.leaf 1500590131))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1465515904) (.branch 47 (.leaf 1431428234) (.leaf 1398291322))) (.branch 50 (.branch 49 (.leaf 1366071016) (.leaf 1334734722)) (.branch 51 (.leaf 1304251318) (.leaf 1274591080)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1245725603) (.leaf 1217627734)) (.branch 55 (.leaf 1190271505) (.leaf 1163632073))) (.branch 58 (.branch 57 (.leaf 1137685661) (.leaf 1112409501)) (.branch 59 (.leaf 1087781786) (.leaf 1063781622))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1040388974) (.branch 62 (.leaf 1017584635) (.leaf 995350175))) (.branch 65 (.branch 64 (.leaf 973667906) (.leaf 952520848)) (.branch 66 (.leaf 931892691) (.leaf 911767763)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 892131002) (.leaf 872967925)) (.branch 70 (.leaf 854264599) (.leaf 836007619))) (.branch 73 (.branch 72 (.leaf 818184080) (.leaf 800781555)) (.branch 74 (.leaf 783788073) (.leaf 767192098))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 750982511) (.branch 77 (.leaf 735148588) (.leaf 719679985))) (.branch 80 (.branch 79 (.leaf 704566718) (.leaf 689799153)) (.branch 81 (.leaf 675367983) (.leaf 661264222)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 647479184) (.leaf 634004475)) (.branch 85 (.leaf 620831978) (.leaf 607953843))) (.branch 88 (.branch 87 (.leaf 595362474) (.leaf 583050522)) (.branch 89 (.leaf 571010872) (.leaf 559236631)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 547721128) (.branch 92 (.leaf 536457894) (.leaf 525440662))) (.branch 95 (.branch 94 (.leaf 514663356) (.leaf 504120085)) (.branch 96 (.leaf 493805134) (.leaf 483712957)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 473838173) (.leaf 464175560)) (.branch 100 (.leaf 454720044) (.leaf 445466701))) (.branch 103 (.branch 102 (.leaf 436410746) (.leaf 427547530)) (.branch 104 (.leaf 418872533) (.leaf 410381364))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 402069752) (.leaf 393933543)) (.branch 108 (.leaf 385968699) (.leaf 378171288))) (.branch 111 (.branch 110 (.leaf 370537486) (.leaf 363063571)) (.branch 112 (.leaf 355745918) (.leaf 348580999)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 341565378) (.leaf 334695709)) (.branch 116 (.leaf 327968731) (.leaf 321381267))) (.branch 119 (.branch 118 (.leaf 314930222) (.leaf 308612579)) (.branch 120 (.leaf 302425397) (.leaf 296365807)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 317).prefactor = (199288964093019/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 317).cutoff/(generalMeanRows 317).c)).2 =
    (83865743501341/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 317).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 317).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 317).q*(generalMeanRows 317).c/2-2 = (3137/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable130.value]
    have hcontinuation : (generalMeanRows 317).q*(generalMeanRows 317).cutoff/2-2 = (4266/1909:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable133.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 317).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 317

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 317).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 317).criticalRate j.val*(generalMeanRows 317).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 317).c*(generalMeanRows 317).criticalPoint j.val)).2-
      (generalMeanRows 317).J/2-(generalMeanRows 317).error (generalMeanGrid j.val)+
      (generalMeanRows 317).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 317).c)).2-
      (generalMeanRows 317).J/2-(generalMeanRows 317).error 4 := by
  have he : (generalMeanRows 317).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 317) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 317)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0317

/-! Kernel-checked entropy margins for general spectral rectangle 318. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0318
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6094005125) (.branch 2 (.leaf 5886463822) (.leaf 5688270389))) (.branch 5 (.branch 4 (.leaf 5498889976) (.leaf 5317825487)) (.branch 6 (.leaf 5144614289) (.leaf 4978825272)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4820056220) (.leaf 4667931452)) (.branch 10 (.leaf 4522099697) (.leaf 4382232179))) (.branch 13 (.branch 12 (.leaf 4248020888) (.leaf 4119176999)) (.branch 14 (.leaf 3995429457) (.leaf 3876523670))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3762220322) (.branch 17 (.leaf 3652294297) (.leaf 3546533680))) (.branch 20 (.branch 19 (.leaf 3444738852) (.leaf 3346721651)) (.branch 21 (.leaf 3252304606) (.leaf 3161320226)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3073610350) (.leaf 2989025542)) (.branch 25 (.leaf 2907424534) (.leaf 2828673707))) (.branch 28 (.branch 27 (.leaf 2752646616) (.leaf 2679223542)) (.branch 29 (.leaf 2608291084) (.leaf 2539741769)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2473473701) (.branch 32 (.leaf 2409390226) (.leaf 2347399624))) (.branch 35 (.branch 34 (.leaf 2287414814) (.leaf 2229353094)) (.branch 36 (.leaf 2173135881) (.leaf 2118688477)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2065939850) (.leaf 2014822430)) (.branch 40 (.leaf 1965271907) (.leaf 1917227061))) (.branch 43 (.branch 42 (.leaf 1870629584) (.leaf 1825423922)) (.branch 44 (.leaf 1781557129) (.leaf 1738978721))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1697640550) (.branch 47 (.leaf 1657496674) (.leaf 1618503243))) (.branch 50 (.branch 49 (.leaf 1580618389) (.leaf 1543802122)) (.branch 51 (.leaf 1508016232) (.leaf 1473224198)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1439391103) (.leaf 1406483547)) (.branch 55 (.leaf 1374469576) (.leaf 1343318605))) (.branch 58 (.branch 57 (.leaf 1313001353) (.leaf 1283489774)) (.branch 59 (.leaf 1254757001) (.leaf 1226777281))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1199525930) (.branch 62 (.leaf 1172979271) (.leaf 1147114593))) (.branch 65 (.branch 64 (.leaf 1121910100) (.leaf 1097344870)) (.branch 66 (.leaf 1073398813) (.leaf 1050052630)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1027287778) (.leaf 1005086434)) (.branch 70 (.leaf 983431460) (.leaf 962306376))) (.branch 73 (.branch 72 (.leaf 941695324) (.leaf 921583044)) (.branch 74 (.leaf 901954846) (.leaf 882796581))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 864094624) (.branch 77 (.leaf 845835843) (.leaf 828007582))) (.branch 80 (.branch 79 (.leaf 810597639) (.leaf 793594245)) (.branch 81 (.leaf 776986048) (.leaf 760762091)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 744911799) (.leaf 729424962)) (.branch 85 (.leaf 714291716) (.leaf 699502534))) (.branch 88 (.branch 87 (.leaf 685048208) (.leaf 670919837)) (.branch 89 (.leaf 657108814) (.leaf 643606817)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 630405792) (.branch 92 (.leaf 617497946) (.leaf 604875737))) (.branch 95 (.branch 94 (.leaf 592531860) (.leaf 580459242)) (.branch 96 (.leaf 568651033) (.leaf 557100593)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 545801486) (.leaf 534747476)) (.branch 100 (.leaf 523932514) (.leaf 513350732))) (.branch 103 (.branch 102 (.leaf 502996440) (.leaf 492864114)) (.branch 104 (.leaf 482948395) (.leaf 473244077))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 463746109) (.leaf 454449583)) (.branch 108 (.leaf 445349731) (.leaf 436441920))) (.branch 111 (.branch 110 (.leaf 427721650) (.leaf 419184543)) (.branch 112 (.leaf 410826345) (.leaf 402642919)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 394630240) (.leaf 386784395)) (.branch 116 (.leaf 379101573) (.leaf 371578068))) (.branch 119 (.branch 118 (.leaf 364210271) (.leaf 356994671)) (.branch 120 (.leaf 349927847) (.leaf 343006469)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 318).prefactor = (561069098345191/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 318).cutoff/(generalMeanRows 318).c)).2 =
    (190718805137309/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 318).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 318).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 318).q*(generalMeanRows 318).c/2-2 = (307/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable081.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 318).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 318

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 318).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 318).criticalRate j.val*(generalMeanRows 318).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 318).c*(generalMeanRows 318).criticalPoint j.val)).2-
      (generalMeanRows 318).J/2-(generalMeanRows 318).error (generalMeanGrid j.val)+
      (generalMeanRows 318).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 318).c)).2-
      (generalMeanRows 318).J/2-(generalMeanRows 318).error 4 := by
  have he : (generalMeanRows 318).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 318) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 318)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0318

/-! Kernel-checked entropy margins for general spectral rectangle 319. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0319
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5021632663) (.branch 2 (.leaf 4846591799) (.leaf 4679594064))) (.branch 5 (.branch 4 (.leaf 4520169390) (.leaf 4367881370)) (.branch 6 (.leaf 4222324314) (.leaf 4083120632)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3949918480) (.leaf 3822389647)) (.branch 10 (.leaf 3700227653) (.leaf 3583146033))) (.branch 13 (.branch 12 (.leaf 3470876782) (.leaf 3363168944)) (.branch 14 (.leaf 3259787331) (.leaf 3160511356))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3065133969) (.branch 17 (.leaf 2973460681) (.leaf 2885308675))) (.branch 20 (.branch 19 (.leaf 2800505990) (.leaf 2718890766)) (.branch 21 (.leaf 2640310562) (.leaf 2564621712)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2491688745) (.leaf 2421383842)) (.branch 25 (.leaf 2353586337) (.leaf 2288182257))) (.branch 28 (.branch 27 (.leaf 2225063887) (.leaf 2164129381)) (.branch 29 (.leaf 2105282391) (.leaf 2048431722)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1993491020) (.branch 32 (.leaf 1940378470) (.leaf 1889016526))) (.branch 35 (.branch 34 (.leaf 1839331652) (.leaf 1791254084)) (.branch 36 (.leaf 1744717603) (.leaf 1699659336)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1656019550) (.leaf 1613741478)) (.branch 40 (.leaf 1572771148) (.leaf 1533057220))) (.branch 43 (.branch 42 (.leaf 1494550840) (.leaf 1457205502)) (.branch 44 (.leaf 1420976913) (.leaf 1385822873))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1351703158) (.branch 47 (.leaf 1318579416) (.leaf 1286415060))) (.branch 50 (.branch 49 (.leaf 1255175178) (.leaf 1224826437)) (.branch 51 (.leaf 1195337008) (.leaf 1166676477)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1138815777) (.leaf 1111727115)) (.branch 55 (.leaf 1085383907) (.leaf 1059760716))) (.branch 58 (.branch 57 (.leaf 1034833192) (.leaf 1010578018)) (.branch 59 (.leaf 986972856) (.leaf 963996302))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 941627835) (.branch 62 (.leaf 919847776) (.leaf 898637243))) (.branch 65 (.branch 64 (.leaf 877978118) (.leaf 857853006)) (.branch 66 (.leaf 838245200) (.leaf 819138648)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 800517925) (.leaf 782368200)) (.branch 70 (.leaf 764675209) (.leaf 747425230))) (.branch 73 (.branch 72 (.leaf 730605055) (.leaf 714201971)) (.branch 74 (.leaf 698203732) (.leaf 682598541))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 667375032) (.branch 77 (.leaf 652522244) (.leaf 638029611))) (.branch 80 (.branch 79 (.leaf 623886938) (.leaf 610084389)) (.branch 81 (.leaf 596612470) (.leaf 583462014)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 570624169) (.leaf 558090380)) (.branch 85 (.leaf 545852382) (.leaf 533902184))) (.branch 88 (.branch 87 (.leaf 522232062) (.leaf 510834541)) (.branch 89 (.leaf 499702393) (.leaf 488828621)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 478206452) (.branch 92 (.leaf 467829327) (.leaf 457690896))) (.branch 95 (.branch 94 (.leaf 447785005) (.leaf 438105692)) (.branch 96 (.leaf 428647177) (.leaf 419403857)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 410370300) (.leaf 401541234)) (.branch 100 (.leaf 392911547) (.leaf 384476277))) (.branch 103 (.branch 102 (.leaf 376230608) (.leaf 368169864)) (.branch 104 (.leaf 360289506) (.leaf 352585124))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 345052433) (.leaf 337687273)) (.branch 108 (.leaf 330485597) (.leaf 323443474))) (.branch 111 (.branch 110 (.leaf 316557083) (.leaf 309822704)) (.branch 112 (.leaf 303236725) (.leaf 296795628)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 290495992) (.leaf 284334488)) (.branch 116 (.leaf 278307877) (.leaf 272413005))) (.branch 119 (.branch 118 (.leaf 266646801) (.leaf 261006276)) (.branch 120 (.leaf 255488520) (.leaf 250090696)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 319).prefactor = (2495601788718903/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 319).cutoff/(generalMeanRows 319).c)).2 =
    (99499180742067/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 319).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 319).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 319).q*(generalMeanRows 319).c/2-2 = (3309/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable134.value]
    have hcontinuation : (generalMeanRows 319).q*(generalMeanRows 319).cutoff/2-2 = (8486/3841:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable131.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 319).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 319

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 319).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 319).criticalRate j.val*(generalMeanRows 319).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 319).c*(generalMeanRows 319).criticalPoint j.val)).2-
      (generalMeanRows 319).J/2-(generalMeanRows 319).error (generalMeanGrid j.val)+
      (generalMeanRows 319).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 319).c)).2-
      (generalMeanRows 319).J/2-(generalMeanRows 319).error 4 := by
  have he : (generalMeanRows 319).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 319) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 319)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0319

/-! Kernel-checked entropy margins for general spectral rectangle 320. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0320
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5895613769) (.branch 2 (.leaf 5686384360) (.leaf 5486644373))) (.branch 5 (.branch 4 (.leaf 5295854435) (.leaf 5113513057)) (.branch 6 (.leaf 4939153327) (.leaf 4772339966)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4612666688) (.leaf 4459753840)) (.branch 10 (.leaf 4313246271) (.leaf 4172811414))) (.branch 13 (.branch 12 (.leaf 4038137550) (.leaf 3908932235)) (.branch 14 (.leaf 3784920869) (.leaf 3665845398))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3551463124) (.branch 17 (.leaf 3441545621) (.leaf 3335877743))) (.branch 20 (.branch 19 (.leaf 3234256713) (.leaf 3136491287)) (.branch 21 (.leaf 3042400981) (.leaf 2951815369)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2864573420) (.leaf 2780522903)) (.branch 25 (.leaf 2699519823) (.leaf 2621427903))) (.branch 28 (.branch 27 (.leaf 2546118107) (.leaf 2473468195)) (.branch 29 (.leaf 2403362308) (.leaf 2335690585)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2270348802) (.branch 32 (.leaf 2207238044) (.leaf 2146264390))) (.branch 35 (.branch 34 (.leaf 2087338624) (.leaf 2030375964)) (.branch 36 (.leaf 1975295811) (.leaf 1922021510)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1870480129) (.leaf 1820602252)) (.branch 40 (.leaf 1772321784) (.leaf 1725575770))) (.branch 43 (.branch 42 (.leaf 1680304222) (.leaf 1636449960)) (.branch 44 (.leaf 1593958461) (.leaf 1552777718))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1512858104) (.branch 47 (.leaf 1474152250) (.leaf 1436614926))) (.branch 50 (.branch 49 (.leaf 1400202928) (.leaf 1364874976)) (.branch 51 (.leaf 1330591615) (.leaf 1297315121)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1265009415) (.leaf 1233639976)) (.branch 55 (.leaf 1203173770) (.leaf 1173579171))) (.branch 58 (.branch 57 (.leaf 1144825891) (.leaf 1116884920)) (.branch 59 (.leaf 1089728456) (.leaf 1063329852))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1037663559) (.branch 62 (.leaf 1012705072) (.leaf 988430881))) (.branch 65 (.branch 64 (.leaf 964818424) (.leaf 941846043)) (.branch 66 (.leaf 919492940) (.leaf 897739138)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 876565445) (.leaf 855953413)) (.branch 70 (.leaf 835885308) (.leaf 816344076))) (.branch 73 (.branch 72 (.leaf 797313315) (.leaf 778777239)) (.branch 74 (.leaf 760720658) (.leaf 743128947))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 725988024) (.branch 77 (.leaf 709284322) (.leaf 693004770))) (.branch 80 (.branch 79 (.leaf 677136773) (.leaf 661668186)) (.branch 81 (.leaf 646587298) (.leaf 631882816)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 617543842) (.leaf 603559859)) (.branch 85 (.leaf 589920718) (.leaf 576616617))) (.branch 88 (.branch 87 (.leaf 563638091) (.leaf 550975994)) (.branch 89 (.leaf 538621494) (.leaf 526566049)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 514801405) (.branch 92 (.leaf 503319580) (.leaf 492112853))) (.branch 95 (.branch 94 (.leaf 481173757) (.leaf 470495064)) (.branch 96 (.leaf 460069780) (.leaf 449891133)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 439952567) (.leaf 430247733)) (.branch 100 (.leaf 420770479) (.leaf 411514845))) (.branch 103 (.branch 102 (.leaf 402475056) (.leaf 393645512)) (.branch 104 (.leaf 385020786) (.leaf 376595614))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 368364890) (.leaf 360323663)) (.branch 108 (.leaf 352467125) (.leaf 344790615))) (.branch 111 (.branch 110 (.leaf 337289605) (.leaf 329959700)) (.branch 112 (.leaf 322796632) (.leaf 315796258)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 308954551) (.leaf 302267601)) (.branch 116 (.leaf 295731607) (.leaf 289342876))) (.branch 119 (.branch 118 (.leaf 283097817) (.leaf 276992940)) (.branch 120 (.leaf 271024852) (.leaf 265190253)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 320).prefactor = (1416855928530339/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 320).cutoff/(generalMeanRows 320).c)).2 =
    (70273978341811/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 320).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 320).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 320).q*(generalMeanRows 320).c/2-2 = (167/200:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable082.value]
    have hcontinuation : (generalMeanRows 320).q*(generalMeanRows 320).cutoff/2-2 = (71/35:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable023.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 320).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 320

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 320).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 320).criticalRate j.val*(generalMeanRows 320).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 320).c*(generalMeanRows 320).criticalPoint j.val)).2-
      (generalMeanRows 320).J/2-(generalMeanRows 320).error (generalMeanGrid j.val)+
      (generalMeanRows 320).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 320).c)).2-
      (generalMeanRows 320).J/2-(generalMeanRows 320).error 4 := by
  have he : (generalMeanRows 320).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 320) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 320)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0320

/-! Kernel-checked entropy margins for general spectral rectangle 321. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0321
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5221869338) (.branch 2 (.leaf 5049927699) (.leaf 4885770977))) (.branch 5 (.branch 4 (.leaf 4728942136) (.leaf 4579017037)) (.branch 6 (.leaf 4435601559) (.leaf 4298329033)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4166857939) (.leaf 4040869841)) (.branch 10 (.leaf 3920067520) (.leaf 3804173301))) (.branch 13 (.branch 12 (.leaf 3692927519) (.leaf 3586087151)) (.branch 14 (.leaf 3483424550) (.leaf 3384726313))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3289792227) (.branch 17 (.leaf 3198434325) (.leaf 3110476010))) (.branch 20 (.branch 19 (.leaf 3025751254) (.leaf 2944103868)) (.branch 21 (.leaf 2865386821) (.leaf 2789461623)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2716197747) (.leaf 2645472106)) (.branch 25 (.leaf 2577168560) (.leaf 2511177465))) (.branch 28 (.branch 27 (.leaf 2447395254) (.leaf 2385724051)) (.branch 29 (.leaf 2326071308) (.leaf 2268349475)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2212475684) (.branch 32 (.leaf 2158371465) (.leaf 2105962478))) (.branch 35 (.branch 34 (.leaf 2055178256) (.leaf 2005951980)) (.branch 36 (.leaf 1958220255) (.leaf 1911922912)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1867002815) (.leaf 1823405683)) (.branch 40 (.leaf 1781079931) (.leaf 1739976506))) (.branch 43 (.branch 42 (.leaf 1700048748) (.leaf 1661252253)) (.branch 44 (.leaf 1623544747) (.leaf 1586885961))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1551237528) (.branch 47 (.leaf 1516562871) (.leaf 1482827109))) (.branch 50 (.branch 49 (.leaf 1449996961) (.leaf 1418040663)) (.branch 51 (.leaf 1386927882) (.leaf 1356629644)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1327118259) (.leaf 1298367254)) (.branch 55 (.leaf 1270351307) (.leaf 1243046193))) (.branch 58 (.branch 57 (.leaf 1216428719) (.leaf 1190476678)) (.branch 59 (.leaf 1165168794) (.leaf 1140484678))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1116404779) (.branch 62 (.leaf 1092910348) (.leaf 1069983391))) (.branch 65 (.branch 64 (.leaf 1047606640) (.leaf 1025763509)) (.branch 66 (.leaf 1004438066) (.leaf 983614999)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 963279588) (.leaf 943417675)) (.branch 70 (.leaf 924015639) (.leaf 905060368))) (.branch 73 (.branch 72 (.leaf 886539239) (.leaf 868440092)) (.branch 74 (.leaf 850751210) (.leaf 833461298))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 816559468) (.branch 77 (.leaf 800035211) (.leaf 783878393))) (.branch 80 (.branch 79 (.leaf 768079226) (.leaf 752628262)) (.branch 81 (.leaf 737516372) (.leaf 722734737)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 708274830) (.leaf 694128408)) (.branch 85 (.leaf 680287496) (.leaf 666744379))) (.branch 88 (.branch 87 (.leaf 653491589) (.leaf 640521896)) (.branch 89 (.leaf 627828297) (.leaf 615404010)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 603242460) (.branch 92 (.leaf 591337276) (.leaf 579682277))) (.branch 95 (.branch 94 (.leaf 568271472) (.leaf 557099047)) (.branch 96 (.leaf 546159358) (.leaf 535446930)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 524956443) (.leaf 514682734)) (.branch 100 (.leaf 504620784) (.leaf 494765717))) (.branch 103 (.branch 102 (.leaf 485112795) (.leaf 475657412)) (.branch 104 (.leaf 466395086) (.leaf 457321460))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 448432296) (.leaf 439723468)) (.branch 108 (.leaf 431190963) (.leaf 422830871))) (.branch 111 (.branch 110 (.leaf 414639387) (.leaf 406612805)) (.branch 112 (.leaf 398747516) (.leaf 391040003)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 383486838) (.leaf 376084681)) (.branch 116 (.leaf 368830276) (.leaf 361720449))) (.branch 119 (.branch 118 (.leaf 354752105) (.leaf 347922224)) (.branch 120 (.leaf 341227862) (.leaf 334666145)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 321).prefactor = (1220979017071971/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 321).cutoff/(generalMeanRows 321).c)).2 =
    (85866286635753/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 321).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 321).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 321).q*(generalMeanRows 321).c/2-2 = (1203/1600:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable135.value]
    have hcontinuation : (generalMeanRows 321).q*(generalMeanRows 321).cutoff/2-2 = (421/189:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable136.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 321).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 321

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 321).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 321).criticalRate j.val*(generalMeanRows 321).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 321).c*(generalMeanRows 321).criticalPoint j.val)).2-
      (generalMeanRows 321).J/2-(generalMeanRows 321).error (generalMeanGrid j.val)+
      (generalMeanRows 321).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 321).c)).2-
      (generalMeanRows 321).J/2-(generalMeanRows 321).error 4 := by
  have he : (generalMeanRows 321).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 321) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 321)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0321

/-! Kernel-checked entropy margins for general spectral rectangle 322. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0322
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5021988035) (.branch 2 (.leaf 4849131324) (.leaf 4684187979))) (.branch 5 (.branch 4 (.leaf 4526694731) (.leaf 4376221553)) (.branch 6 (.leaf 4232368764) (.leaf 4094764431)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3963062045) (.leaf 3836938436)) (.branch 10 (.leaf 3716091886) (.leaf 3600240439))) (.branch 13 (.branch 12 (.leaf 3489120356) (.leaf 3382484728)) (.branch 14 (.leaf 3280102202) (.leaf 3181755834))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3087242029) (.branch 17 (.leaf 2996369584) (.leaf 2908958806))) (.branch 20 (.branch 19 (.leaf 2824840701) (.leaf 2743856237)) (.branch 21 (.leaf 2665855660) (.leaf 2590697864)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2518249816) (.leaf 2448386019)) (.branch 25 (.leaf 2380988020) (.leaf 2315943951))) (.branch 28 (.branch 27 (.leaf 2253148110) (.leaf 2192500567)) (.branch 29 (.leaf 2133906797) (.leaf 2077277350)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2022527530) (.branch 32 (.leaf 1969577109) (.leaf 1918350051))) (.branch 35 (.branch 34 (.leaf 1868774260) (.leaf 1820781347)) (.branch 36 (.leaf 1774306407) (.leaf 1729287815)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1685667034) (.leaf 1643388434)) (.branch 40 (.leaf 1602399130) (.leaf 1562648818))) (.branch 43 (.branch 42 (.leaf 1524089633) (.leaf 1486676011)) (.branch 44 (.leaf 1450364559) (.leaf 1415113933))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1380884729) (.branch 47 (.leaf 1347639374) (.leaf 1315342025))) (.branch 50 (.branch 49 (.leaf 1283958478) (.leaf 1253456079)) (.branch 51 (.leaf 1223803640) (.leaf 1194971363)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1166930766) (.leaf 1139654614)) (.branch 55 (.leaf 1113116853) (.leaf 1087292554))) (.branch 58 (.branch 57 (.leaf 1062157847) (.leaf 1037689875)) (.branch 59 (.leaf 1013866737) (.leaf 990667445))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 968071873) (.branch 62 (.leaf 946060718) (.leaf 924615458))) (.branch 65 (.branch 64 (.leaf 903718315) (.leaf 883352217)) (.branch 66 (.leaf 863500764) (.leaf 844148199)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 825279373) (.leaf 806879719)) (.branch 70 (.leaf 788935223) (.leaf 771432401))) (.branch 73 (.branch 72 (.leaf 754358270) (.leaf 737700331)) (.branch 74 (.leaf 721446540) (.leaf 705585292))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 690105403) (.branch 77 (.leaf 674996084) (.leaf 660246930))) (.branch 80 (.branch 79 (.leaf 645847902) (.leaf 631789308)) (.branch 81 (.leaf 618061791) (.leaf 604656314)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 591564146) (.leaf 578776849)) (.branch 85 (.leaf 566286265) (.leaf 554084505))) (.branch 88 (.branch 87 (.leaf 542163940) (.leaf 530517186)) (.branch 89 (.leaf 519137099) (.leaf 508016760)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 497149471) (.branch 92 (.leaf 486528742) (.leaf 476148287))) (.branch 95 (.branch 94 (.leaf 466002013) (.leaf 456084012)) (.branch 96 (.leaf 446388558) (.leaf 436910095)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 427643234) (.leaf 418582746)) (.branch 100 (.leaf 409723556) (.leaf 401060735))) (.branch 103 (.branch 102 (.leaf 392589501) (.leaf 384305206)) (.branch 104 (.leaf 376203336) (.leaf 368279504))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 360529447) (.leaf 352949024)) (.branch 108 (.leaf 345534203) (.leaf 338281069))) (.branch 111 (.branch 110 (.leaf 331185811) (.leaf 324244722)) (.branch 112 (.leaf 317454195) (.leaf 310810722)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 304310887) (.leaf 297951364)) (.branch 116 (.leaf 291728915) (.leaf 285640389))) (.branch 119 (.branch 118 (.leaf 279682713) (.leaf 273852898)) (.branch 120 (.leaf 268148029) (.leaf 262565267)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 322).prefactor = (4946643410390047/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 322).cutoff/(generalMeanRows 322).c)).2 =
    (203214834446041/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 322).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 322).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 322).q*(generalMeanRows 322).c/2-2 = (261/320:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable137.value]
    have hcontinuation : (generalMeanRows 322).q*(generalMeanRows 322).cutoff/2-2 = (421/189:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable136.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 322).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 322

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 322).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 322).criticalRate j.val*(generalMeanRows 322).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 322).c*(generalMeanRows 322).criticalPoint j.val)).2-
      (generalMeanRows 322).J/2-(generalMeanRows 322).error (generalMeanGrid j.val)+
      (generalMeanRows 322).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 322).c)).2-
      (generalMeanRows 322).J/2-(generalMeanRows 322).error 4 := by
  have he : (generalMeanRows 322).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 322) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 322)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0322

/-! Kernel-checked entropy margins for general spectral rectangle 323. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0323
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7000709966) (.branch 2 (.leaf 6803256498) (.leaf 6613947818))) (.branch 5 (.branch 4 (.leaf 6432343636) (.leaf 6258034066)) (.branch 6 (.leaf 6090636920) (.leaf 5929795305)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5775175487) (.leaf 5626464980)) (.branch 10 (.leaf 5483370835) (.leaf 5345618103))) (.branch 13 (.branch 12 (.leaf 5212948449) (.leaf 5085118899)) (.branch 14 (.leaf 4961900710) (.leaf 4843078336))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4728448495) (.branch 17 (.leaf 4617819313) (.leaf 4511009545))) (.branch 20 (.branch 19 (.leaf 4407847861) (.leaf 4308172185)) (.branch 21 (.leaf 4211829102) (.leaf 4118673296)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4028567042) (.leaf 3941379734)) (.branch 25 (.leaf 3856987449) (.leaf 3775272541))) (.branch 28 (.branch 27 (.leaf 3696123270) (.leaf 3619433448)) (.branch 29 (.leaf 3545102123) (.leaf 3473033273)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3403135527) (.branch 32 (.leaf 3335321904) (.leaf 3269509566))) (.branch 35 (.branch 34 (.leaf 3205619595) (.leaf 3143576775)) (.branch 36 (.leaf 3083309393) (.leaf 3024749055)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2967830504) (.leaf 2912491461)) (.branch 40 (.leaf 2858672467) (.leaf 2806316738))) (.branch 43 (.branch 42 (.leaf 2755370028) (.leaf 2705780500)) (.branch 44 (.leaf 2657498606) (.leaf 2610476968))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2564670277) (.branch 47 (.leaf 2520035184) (.leaf 2476530208))) (.branch 50 (.branch 49 (.leaf 2434115645) (.leaf 2392753481)) (.branch 51 (.leaf 2352407309) (.leaf 2313042256)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2274624908) (.leaf 2237123241)) (.branch 55 (.leaf 2200506556) (.leaf 2164745418))) (.branch 58 (.branch 57 (.leaf 2129811596) (.leaf 2095678008)) (.branch 59 (.leaf 2062318669) (.leaf 2029708640))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1997823979) (.branch 62 (.leaf 1966641700) (.leaf 1936139726))) (.branch 65 (.branch 64 (.leaf 1906296848) (.leaf 1877092692)) (.branch 66 (.leaf 1848507675) (.leaf 1820522974)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1793120490) (.leaf 1766282821)) (.branch 70 (.leaf 1739993225) (.leaf 1714235596))) (.branch 73 (.branch 72 (.leaf 1688994437) (.leaf 1664254830)) (.branch 74 (.leaf 1640002413) (.leaf 1616223358))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1592904346) (.branch 77 (.leaf 1570032546) (.leaf 1547595596))) (.branch 80 (.branch 79 (.leaf 1525581580) (.leaf 1503979012)) (.branch 81 (.leaf 1482776818) (.leaf 1461964318)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1441531209) (.leaf 1421467552)) (.branch 85 (.leaf 1401763755) (.leaf 1382410558))) (.branch 88 (.branch 87 (.leaf 1363399023) (.leaf 1344720516)) (.branch 89 (.leaf 1326366701) (.leaf 1308329521)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1290601193) (.branch 92 (.leaf 1273174193) (.leaf 1256041247))) (.branch 95 (.branch 94 (.leaf 1239195323) (.leaf 1222629616)) (.branch 96 (.leaf 1206337546) (.leaf 1190312745)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1174549049) (.leaf 1159040491)) (.branch 100 (.leaf 1143781294) (.leaf 1128765862))) (.branch 103 (.branch 102 (.leaf 1113988773) (.leaf 1099444776)) (.branch 104 (.leaf 1085128778) (.leaf 1071035844))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1057161189) (.leaf 1043500172)) (.branch 108 (.leaf 1030048290) (.leaf 1016801173))) (.branch 111 (.branch 110 (.leaf 1003754581) (.leaf 990904399)) (.branch 112 (.leaf 978246628) (.leaf 965777388)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 953492906) (.leaf 941389519)) (.branch 116 (.leaf 929463665) (.leaf 917711882))) (.branch 119 (.branch 118 (.leaf 906130804) (.leaf 894717156)) (.branch 120 (.leaf 883467754) (.leaf 872379500)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 323).prefactor = (4599540156782783/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 323).cutoff/(generalMeanRows 323).c)).2 =
    (19587159813917/50000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 323).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 323).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hcontinuation : (generalMeanRows 323).q*(generalMeanRows 323).cutoff/2-2 = (212/129:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable138.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 323).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 323

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 323).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 323).criticalRate j.val*(generalMeanRows 323).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 323).c*(generalMeanRows 323).criticalPoint j.val)).2-
      (generalMeanRows 323).J/2-(generalMeanRows 323).error (generalMeanGrid j.val)+
      (generalMeanRows 323).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 323).c)).2-
      (generalMeanRows 323).J/2-(generalMeanRows 323).error 4 := by
  have he : (generalMeanRows 323).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 323) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 323)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0323

/-! Kernel-checked entropy margins for general spectral rectangle 324. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0324
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7193800669) (.branch 2 (.leaf 6987222559) (.leaf 6789170115))) (.branch 5 (.branch 4 (.leaf 6599183202) (.leaf 6416833450)) (.branch 6 (.leaf 6241721423) (.leaf 6073474115)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5911742710) (.leaf 5756200592)) (.branch 10 (.leaf 5606541553) (.leaf 5462478188))) (.branch 13 (.branch 12 (.leaf 5323740448) (.leaf 5190074329)) (.branch 14 (.leaf 5061240693) (.leaf 4937014187))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4817182268) (.branch 17 (.leaf 4701544310) (.leaf 4589910788))) (.branch 20 (.branch 19 (.leaf 4482102532) (.leaf 4377950043)) (.branch 21 (.leaf 4277292862) (.leaf 4179978992)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4085864368) (.leaf 3994812355)) (.branch 25 (.leaf 3906693302) (.leaf 3821384115))) (.branch 28 (.branch 27 (.leaf 3738767864) (.leaf 3658733425)) (.branch 29 (.leaf 3581175138) (.leaf 3505992494)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3433089843) (.branch 32 (.leaf 3362376119) (.leaf 3293764588))) (.branch 35 (.branch 34 (.leaf 3227172606) (.leaf 3162521399)) (.branch 36 (.leaf 3099735852) (.leaf 3038744317)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2979478424) (.leaf 2921872914)) (.branch 40 (.leaf 2865865476) (.leaf 2811396591))) (.branch 43 (.branch 42 (.leaf 2758409395) (.leaf 2706849540)) (.branch 44 (.leaf 2656665070) (.leaf 2607806299))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2560225700) (.branch 47 (.leaf 2513877796) (.leaf 2468719065))) (.branch 50 (.branch 49 (.leaf 2424707839) (.leaf 2381804218)) (.branch 51 (.leaf 2339969984) (.leaf 2299168521)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2259364739) (.leaf 2220525002)) (.branch 55 (.leaf 2182617060) (.leaf 2145609983))) (.branch 58 (.branch 57 (.leaf 2109474104) (.leaf 2074180956)) (.branch 59 (.leaf 2039703219) (.leaf 2006014669))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1973090125) (.branch 62 (.leaf 1940905405) (.leaf 1909437281))) (.branch 65 (.branch 64 (.leaf 1878663434) (.leaf 1848562414)) (.branch 66 (.leaf 1819113606) (.leaf 1790297186)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1762094092) (.leaf 1734485988)) (.branch 70 (.leaf 1707455234) (.leaf 1680984853))) (.branch 73 (.branch 72 (.leaf 1655058508) (.leaf 1629660467)) (.branch 74 (.leaf 1604775584) (.leaf 1580389269))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1556487470) (.branch 77 (.leaf 1533056643) (.leaf 1510083737))) (.branch 80 (.branch 79 (.leaf 1487556171) (.leaf 1465461814)) (.branch 81 (.leaf 1443788966) (.leaf 1422526342)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1401663053) (.leaf 1381188592)) (.branch 85 (.leaf 1361092815) (.leaf 1341365930))) (.branch 88 (.branch 87 (.leaf 1321998480) (.leaf 1302981331)) (.branch 89 (.leaf 1284305658) (.leaf 1265962934)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1247944916) (.branch 92 (.leaf 1230243637) (.leaf 1212851390))) (.branch 95 (.branch 94 (.leaf 1195760723) (.leaf 1178964427)) (.branch 96 (.leaf 1162455526) (.leaf 1146227267)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1130273115) (.leaf 1114586740)) (.branch 100 (.leaf 1099162013) (.leaf 1083992995))) (.branch 103 (.branch 102 (.leaf 1069073934) (.leaf 1054399253)) (.branch 104 (.leaf 1039963547) (.leaf 1025761574))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 1011788253) (.leaf 998038651)) (.branch 108 (.leaf 984507986) (.leaf 971191613))) (.branch 111 (.branch 110 (.leaf 958085028) (.leaf 945183853)) (.branch 112 (.leaf 932483839) (.leaf 919980859)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 907670903) (.leaf 895550072)) (.branch 116 (.leaf 883614578) (.leaf 871860739))) (.branch 119 (.branch 118 (.leaf 860284973) (.leaf 848883795)) (.branch 120 (.leaf 837653818) (.leaf 826591742)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 324).prefactor = (601395770195373/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 324).cutoff/(generalMeanRows 324).c)).2 =
    (76328420058367/200000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 324).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 324).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 324).q*(generalMeanRows 324).c/2-2 = (39/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable085.value]
    have hcontinuation : (generalMeanRows 324).q*(generalMeanRows 324).cutoff/2-2 = (212/129:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable138.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 324).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 324

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 324).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 324).criticalRate j.val*(generalMeanRows 324).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 324).c*(generalMeanRows 324).criticalPoint j.val)).2-
      (generalMeanRows 324).J/2-(generalMeanRows 324).error (generalMeanGrid j.val)+
      (generalMeanRows 324).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 324).c)).2-
      (generalMeanRows 324).J/2-(generalMeanRows 324).error 4 := by
  have he : (generalMeanRows 324).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 324) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 324)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0324

/-! Kernel-checked entropy margins for general spectral rectangle 325. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0325
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 7393273135) (.branch 2 (.leaf 7177227756) (.leaf 6970107013))) (.branch 5 (.branch 4 (.leaf 6771429975) (.leaf 6580748896)) (.branch 6 (.leaf 6397646266) (.leaf 6221732184)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 6052642025) (.leaf 5890034355)) (.branch 10 (.leaf 5733589063) (.leaf 5583005680))) (.branch 13 (.branch 12 (.leaf 5438001871) (.leaf 5298312062)) (.branch 14 (.leaf 5163686209) (.leaf 5033888668))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4908697180) (.branch 17 (.leaf 4787901931) (.leaf 4671304706))) (.branch 20 (.branch 19 (.leaf 4558718107) (.leaf 4449964837)) (.branch 21 (.leaf 4344877046) (.leaf 4243295722)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 4145070135) (.leaf 4050057324)) (.branch 25 (.leaf 3958121618) (.leaf 3869134199))) (.branch 28 (.branch 27 (.leaf 3782972687) (.leaf 3699520768)) (.branch 29 (.leaf 3618667836) (.leaf 3540308666)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 3464343112) (.branch 32 (.leaf 3390675813) (.leaf 3319215937))) (.branch 35 (.branch 34 (.leaf 3249876924) (.leaf 3182576260)) (.branch 36 (.leaf 3117235252) (.leaf 3053778829)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2992135350) (.leaf 2932236419)) (.branch 40 (.leaf 2874016725) (.leaf 2817413875))) (.branch 43 (.branch 42 (.leaf 2762368249) (.leaf 2708822859)) (.branch 44 (.leaf 2656723214) (.leaf 2606017199))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2556654956) (.branch 47 (.leaf 2508588770) (.leaf 2461772969))) (.branch 50 (.branch 49 (.leaf 2416163819) (.leaf 2371719439)) (.branch 51 (.leaf 2328399702) (.leaf 2286166160)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 2244981959) (.leaf 2204811768)) (.branch 55 (.leaf 2165621704) (.leaf 2127379267))) (.branch 58 (.branch 57 (.leaf 2090053278) (.leaf 2053613812)) (.branch 59 (.leaf 2018032147) (.leaf 1983280707))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1949333008) (.branch 62 (.leaf 1916163613) (.leaf 1883748081))) (.branch 65 (.branch 64 (.leaf 1852062925) (.leaf 1821085570)) (.branch 66 (.leaf 1790794310) (.leaf 1761168275)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1732187387) (.leaf 1703832332)) (.branch 70 (.leaf 1676084525) (.leaf 1648926077))) (.branch 73 (.branch 72 (.leaf 1622339766) (.leaf 1596309009)) (.branch 74 (.leaf 1570817835) (.leaf 1545850858))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1521393253) (.branch 77 (.leaf 1497430732) (.leaf 1473949522))) (.branch 80 (.branch 79 (.leaf 1450936344) (.leaf 1428378390)) (.branch 81 (.leaf 1406263307) (.leaf 1384579177)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1363314498) (.leaf 1342458166)) (.branch 85 (.leaf 1321999464) (.leaf 1301928041))) (.branch 88 (.branch 87 (.leaf 1282233900) (.leaf 1262907383)) (.branch 89 (.leaf 1243939156) (.leaf 1225320200)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 1207041795) (.branch 92 (.leaf 1189095509) (.leaf 1171473188))) (.branch 95 (.branch 94 (.leaf 1154166941) (.leaf 1137169138)) (.branch 96 (.leaf 1120472390) (.leaf 1104069547)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 1087953685) (.leaf 1072118099)) (.branch 100 (.leaf 1056556295) (.leaf 1041261979))) (.branch 103 (.branch 102 (.leaf 1026229055) (.leaf 1011451610)) (.branch 104 (.leaf 996923914) (.leaf 982640410))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 968595707) (.leaf 954784577)) (.branch 108 (.leaf 941201945) (.leaf 927842885))) (.branch 111 (.branch 110 (.leaf 914702616) (.leaf 901776496)) (.branch 112 (.leaf 889060015) (.leaf 876548793)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 864238573) (.leaf 852125219)) (.branch 116 (.leaf 840204709) (.leaf 828473135))) (.branch 119 (.branch 118 (.leaf 816926694) (.leaf 805561688)) (.branch 120 (.leaf 794374518) (.leaf 783361683)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 325).prefactor = (5032529132294703/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 325).cutoff/(generalMeanRows 325).c)).2 =
    (185821008478627/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 325).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 325).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 325).q*(generalMeanRows 325).c/2-2 = (41/80:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable058.value]
    have hcontinuation : (generalMeanRows 325).q*(generalMeanRows 325).cutoff/2-2 = (212/129:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable138.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 325).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 325

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 325).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 325).criticalRate j.val*(generalMeanRows 325).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 325).c*(generalMeanRows 325).criticalPoint j.val)).2-
      (generalMeanRows 325).J/2-(generalMeanRows 325).error (generalMeanGrid j.val)+
      (generalMeanRows 325).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 325).c)).2-
      (generalMeanRows 325).J/2-(generalMeanRows 325).error 4 := by
  have he : (generalMeanRows 325).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 325) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 325)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0325

/-! Kernel-checked entropy margins for general spectral rectangle 326. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0326
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6328227032) (.branch 2 (.leaf 6107786905) (.leaf 5896755884))) (.branch 5 (.branch 4 (.leaf 5694631636) (.leaf 5500946264)) (.branch 6 (.leaf 5315263248) (.leaf 5137174720)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4966299043) (.leaf 4802278654)) (.branch 10 (.leaf 4644778122) (.leaf 4493482408))) (.branch 13 (.branch 12 (.leaf 4348095299) (.leaf 4208337989)) (.branch 14 (.leaf 4073947799) (.leaf 3944677010))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3820291806) (.branch 17 (.leaf 3700571304) (.leaf 3585306679))) (.branch 20 (.branch 19 (.leaf 3474300348) (.leaf 3367365236)) (.branch 21 (.leaf 3264324091) (.leaf 3165008860)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3069260111) (.leaf 2976926500)) (.branch 25 (.leaf 2887864280) (.leaf 2801936840))) (.branch 28 (.branch 27 (.leaf 2719014288) (.leaf 2638973054)) (.branch 29 (.leaf 2561695528) (.leaf 2487069716)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2414988930) (.branch 32 (.leaf 2345351486) (.leaf 2278060435))) (.branch 35 (.branch 34 (.leaf 2213023298) (.leaf 2150151832)) (.branch 36 (.leaf 2089361803) (.leaf 2030572769)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1973707890) (.leaf 1918693736)) (.branch 40 (.leaf 1865460114) (.leaf 1813939903))) (.branch 43 (.branch 42 (.leaf 1764068900) (.leaf 1715785676)) (.branch 44 (.leaf 1669031433) (.leaf 1623749883))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1579887118) (.branch 47 (.leaf 1537391499) (.leaf 1496213548))) (.branch 50 (.branch 49 (.leaf 1456305841) (.leaf 1417622914)) (.branch 51 (.leaf 1380121173) (.leaf 1343758801)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1308495679) (.leaf 1274293309)) (.branch 55 (.leaf 1241114738) (.leaf 1208924489))) (.branch 58 (.branch 57 (.leaf 1177688493) (.leaf 1147374027)) (.branch 59 (.leaf 1117949653) (.leaf 1089385162))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1061651520) (.branch 62 (.leaf 1034720814) (.leaf 1008566207))) (.branch 65 (.branch 64 (.leaf 983161888) (.leaf 958483031)) (.branch 66 (.leaf 934505748) (.leaf 911207054)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 888564826) (.leaf 866557766)) (.branch 70 (.leaf 845165368) (.leaf 824367886))) (.branch 73 (.branch 72 (.leaf 804146298) (.leaf 784482280)) (.branch 74 (.leaf 765358176) (.leaf 746756970))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 728662261) (.branch 77 (.leaf 711058236) (.leaf 693929649))) (.branch 80 (.branch 79 (.leaf 677261796) (.leaf 661040496)) (.branch 81 (.leaf 645252064) (.leaf 629883299)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 614921461) (.leaf 600354252)) (.branch 85 (.leaf 586169800) (.leaf 572356642))) (.branch 88 (.branch 87 (.leaf 558903709) (.leaf 545800311)) (.branch 89 (.leaf 533036119) (.leaf 520601155)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 508485777) (.branch 92 (.leaf 496680667) (.leaf 485176817))) (.branch 95 (.branch 94 (.leaf 473965519) (.leaf 463038353)) (.branch 96 (.leaf 452387178) (.leaf 442004117)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 431881552) (.leaf 422012112)) (.branch 100 (.leaf 412388666) (.leaf 403004311))) (.branch 103 (.branch 102 (.leaf 393852365) (.leaf 384926362)) (.branch 104 (.leaf 376220040) (.leaf 367727333))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 359442371) (.leaf 351359464)) (.branch 108 (.leaf 343473101) (.leaf 335777944))) (.branch 111 (.branch 110 (.leaf 328268818) (.leaf 320940709)) (.branch 112 (.leaf 313788756) (.leaf 306808248)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 299994615) (.leaf 293343428)) (.branch 116 (.leaf 286850390) (.leaf 280511334))) (.branch 119 (.branch 118 (.leaf 274322218) (.leaf 268279119)) (.branch 120 (.leaf 262378231) (.leaf 256615861)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 326).prefactor = (658009633655201/125000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 326).cutoff/(generalMeanRows 326).c)).2 =
    (64711630702977/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 326).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 326).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 326).q*(generalMeanRows 326).c/2-2 = (13/16:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable042.value]
    have hcontinuation : (generalMeanRows 326).q*(generalMeanRows 326).cutoff/2-2 = (212/129:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable138.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 326).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 326

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 326).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 326).criticalRate j.val*(generalMeanRows 326).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 326).c*(generalMeanRows 326).criticalPoint j.val)).2-
      (generalMeanRows 326).J/2-(generalMeanRows 326).error (generalMeanGrid j.val)+
      (generalMeanRows 326).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 326).c)).2-
      (generalMeanRows 326).J/2-(generalMeanRows 326).error 4 := by
  have he : (generalMeanRows 326).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 326) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 326)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0326

/-! Kernel-checked entropy margins for general spectral rectangle 327. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0327
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6597627299) (.branch 2 (.leaf 6394029168) (.leaf 6199027573))) (.branch 5 (.branch 4 (.leaf 6012153438) (.leaf 5832970136)) (.branch 6 (.leaf 5661070628) (.leaf 5496074913)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 5337627761) (.leaf 5185396676)) (.branch 10 (.leaf 5039070078) (.leaf 4898355660))) (.branch 13 (.branch 12 (.leaf 4762978912) (.leaf 4632681780)) (.branch 14 (.leaf 4507221452) (.leaf 4386369259))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4269909668) (.branch 17 (.leaf 4157639368) (.leaf 4049366428))) (.branch 20 (.branch 19 (.leaf 3944909535) (.leaf 3844097282)) (.branch 21 (.leaf 3746767529) (.leaf 3652766797)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3561949726) (.leaf 3474178563)) (.branch 25 (.leaf 3389322691) (.leaf 3307258195))) (.branch 28 (.branch 27 (.leaf 3227867460) (.leaf 3151038794)) (.branch 29 (.leaf 3076666079) (.leaf 3004648449)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2934889986) (.branch 32 (.leaf 2867299438) (.leaf 2801789961))) (.branch 35 (.branch 34 (.leaf 2738278864) (.leaf 2676687388)) (.branch 36 (.leaf 2616940488) (.leaf 2558966629)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2502697599) (.leaf 2448068335)) (.branch 40 (.leaf 2395016750) (.leaf 2343483584))) (.branch 43 (.branch 42 (.leaf 2293412251) (.leaf 2244748703)) (.branch 44 (.leaf 2197441302) (.leaf 2151440695))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2106699699) (.branch 47 (.leaf 2063173191) (.leaf 2020818009))) (.branch 50 (.branch 49 (.leaf 1979592849) (.leaf 1939458182)) (.branch 51 (.leaf 1900376157) (.leaf 1862310528)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1825226572) (.leaf 1789091018)) (.branch 55 (.leaf 1753871975) (.leaf 1719538872))) (.branch 58 (.branch 57 (.leaf 1686062388) (.leaf 1653414400)) (.branch 59 (.leaf 1621567923) (.leaf 1590497060))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1560176950) (.branch 62 (.leaf 1530583721) (.leaf 1501694443))) (.branch 65 (.branch 64 (.leaf 1473487091) (.leaf 1445940495)) (.branch 66 (.leaf 1419034311) (.leaf 1392748976)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1367065679) (.leaf 1341966325)) (.branch 70 (.leaf 1317433503) (.leaf 1293450457))) (.branch 73 (.branch 72 (.leaf 1270001057) (.leaf 1247069774)) (.branch 74 (.leaf 1224641649) (.leaf 1202702273))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1181237762) (.branch 77 (.leaf 1160234733) (.leaf 1139680286))) (.branch 80 (.branch 79 (.leaf 1119561980) (.leaf 1099867817)) (.branch 81 (.leaf 1080586220) (.leaf 1061706020)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1043216434) (.leaf 1025107052)) (.branch 85 (.leaf 1007367822) (.leaf 989989034))) (.branch 88 (.branch 87 (.leaf 972961306) (.leaf 956275573)) (.branch 89 (.leaf 939923072) (.leaf 923895328)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 908184149) (.branch 92 (.leaf 892781608) (.leaf 877680036))) (.branch 95 (.branch 94 (.leaf 862872011) (.leaf 848350349)) (.branch 96 (.leaf 834108093) (.leaf 820138507)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 806435065) (.leaf 792991443)) (.branch 100 (.leaf 779801514) (.leaf 766859338))) (.branch 103 (.branch 102 (.leaf 754159154) (.leaf 741695377)) (.branch 104 (.leaf 729462589) (.leaf 717455532))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 705669104) (.leaf 694098353)) (.branch 108 (.leaf 682738470) (.leaf 671584785))) (.branch 111 (.branch 110 (.leaf 660632762) (.leaf 649877995)) (.branch 112 (.leaf 639316200) (.leaf 628943215)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 618754994) (.leaf 608747600)) (.branch 116 (.leaf 598917207) (.leaf 589260090))) (.branch 119 (.branch 118 (.leaf 579772629) (.leaf 570451295)) (.branch 120 (.leaf 561292657) (.leaf 552293374)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 327).prefactor = (4938505327506623/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 327).cutoff/(generalMeanRows 327).c)).2 =
    (364042442962821/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 327).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 327).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 327).q*(generalMeanRows 327).c/2-2 = (151/250:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable060.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 327).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 327

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 327).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 327).criticalRate j.val*(generalMeanRows 327).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 327).c*(generalMeanRows 327).criticalPoint j.val)).2-
      (generalMeanRows 327).J/2-(generalMeanRows 327).error (generalMeanGrid j.val)+
      (generalMeanRows 327).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 327).c)).2-
      (generalMeanRows 327).J/2-(generalMeanRows 327).error 4 := by
  have he : (generalMeanRows 327).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 327) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 327)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0327

/-! Kernel-checked entropy margins for general spectral rectangle 328. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0328
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6118638473) (.branch 2 (.leaf 5935582216) (.leaf 5760353076))) (.branch 5 (.branch 4 (.leaf 5592514352) (.leaf 5431659824)) (.branch 6 (.leaf 5277411075) (.leaf 5129415116)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4987342257) (.leaf 4850884203)) (.branch 10 (.leaf 4719752346) (.leaf 4593676221))) (.branch 13 (.branch 12 (.leaf 4472402115) (.leaf 4355691806)) (.branch 14 (.leaf 4243321420) (.leaf 4135080386))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 4030770491) (.branch 17 (.leaf 3930205011) (.leaf 3833207922))) (.branch 20 (.branch 19 (.leaf 3739613165) (.leaf 3649263986)) (.branch 21 (.leaf 3562012318) (.leaf 3477718216)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3396249334) (.leaf 3317480445)) (.branch 25 (.leaf 3241292993) (.leaf 3167574679))) (.branch 28 (.branch 27 (.leaf 3096219081) (.leaf 3027125296)) (.branch 29 (.leaf 2960197609) (.leaf 2895345186)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2832481788) (.branch 32 (.leaf 2771525503) (.leaf 2712398498))) (.branch 35 (.branch 34 (.leaf 2655026783) (.leaf 2599339999)) (.branch 36 (.leaf 2545271208) (.leaf 2492756709)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2441735854) (.leaf 2392150884)) (.branch 40 (.leaf 2343946772) (.leaf 2297071072))) (.branch 43 (.branch 42 (.leaf 2251473787) (.leaf 2207107233)) (.branch 44 (.leaf 2163925920) (.leaf 2121886435))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 2080947338) (.branch 47 (.leaf 2041069052) (.leaf 2002213776))) (.branch 50 (.branch 49 (.leaf 1964345389) (.leaf 1927429363)) (.branch 51 (.leaf 1891432688) (.leaf 1856323792)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1822072469) (.leaf 1788649815)) (.branch 55 (.leaf 1756028158) (.leaf 1724181000))) (.branch 58 (.branch 57 (.leaf 1693082963) (.leaf 1662709728)) (.branch 59 (.leaf 1633037991) (.leaf 1604045407))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1575710549) (.branch 62 (.leaf 1548012864) (.leaf 1520932630))) (.branch 65 (.branch 64 (.leaf 1494450915) (.leaf 1468549545)) (.branch 66 (.leaf 1443211066) (.leaf 1418418709)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1394156361) (.leaf 1370408534)) (.branch 70 (.leaf 1347160334) (.leaf 1324397439))) (.branch 73 (.branch 72 (.leaf 1302106069) (.leaf 1280272962)) (.branch 74 (.leaf 1258885353) (.leaf 1237930950))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1217397913) (.branch 77 (.leaf 1197274834) (.leaf 1177550721))) (.branch 80 (.branch 79 (.leaf 1158214974) (.leaf 1139257373)) (.branch 81 (.leaf 1120668060) (.leaf 1102437523)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 1084556580) (.leaf 1067016369)) (.branch 85 (.leaf 1049808328) (.leaf 1032924191))) (.branch 88 (.branch 87 (.leaf 1016355966) (.leaf 1000095932)) (.branch 89 (.leaf 984136620) (.leaf 968470811)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 953091518) (.branch 92 (.leaf 937991982) (.leaf 923165660))) (.branch 95 (.branch 94 (.leaf 908606215) (.leaf 894307513)) (.branch 96 (.leaf 880263610) (.leaf 866468745)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 852917335) (.leaf 839603967)) (.branch 100 (.leaf 826523390) (.leaf 813670512))) (.branch 103 (.branch 102 (.leaf 801040390) (.leaf 788628228)) (.branch 104 (.leaf 776429366) (.leaf 764439282))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 752653583) (.leaf 741067998)) (.branch 108 (.leaf 729678379) (.leaf 718480690))) (.branch 111 (.branch 110 (.leaf 707471010) (.leaf 696645522)) (.branch 112 (.leaf 686000514) (.leaf 675532375)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 665237587) (.leaf 655112727)) (.branch 116 (.leaf 645154460) (.leaf 635359540))) (.branch 119 (.branch 118 (.leaf 625724802) (.leaf 616247161)) (.branch 120 (.leaf 606923613) (.leaf 597751226)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 328).prefactor = (184818068964103/40000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 328).cutoff/(generalMeanRows 328).c)).2 =
    (203200858400981/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 328).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 328).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 328).q*(generalMeanRows 328).c/2-2 = (72/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable139.value]
    have hcontinuation : (generalMeanRows 328).q*(generalMeanRows 328).cutoff/2-2 = (1044/559:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable140.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 328).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 328

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 328).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 328).criticalRate j.val*(generalMeanRows 328).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 328).c*(generalMeanRows 328).criticalPoint j.val)).2-
      (generalMeanRows 328).J/2-(generalMeanRows 328).error (generalMeanGrid j.val)+
      (generalMeanRows 328).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 328).c)).2-
      (generalMeanRows 328).J/2-(generalMeanRows 328).error 4 := by
  have he : (generalMeanRows 328).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 328) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 328)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0328

/-! Kernel-checked entropy margins for general spectral rectangle 329. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0329
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 6115875708) (.branch 2 (.leaf 5926751922) (.leaf 5745747528))) (.branch 5 (.branch 4 (.leaf 5572410859) (.leaf 5406321730)) (.branch 6 (.leaf 5247088678) (.leaf 5094346498)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4947754055) (.leaf 4806992310)) (.branch 10 (.leaf 4671762559) (.leaf 4541784839))) (.branch 13 (.branch 12 (.leaf 4416796488) (.leaf 4296550848)) (.branch 14 (.leaf 4180816075) (.leaf 4069374074))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3962019512) (.branch 17 (.leaf 3858558925) (.leaf 3758809900))) (.branch 20 (.branch 19 (.leaf 3662600322) (.leaf 3569767690)) (.branch 21 (.leaf 3480158475) (.leaf 3393627541)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3310037606) (.leaf 3229258743)) (.branch 25 (.leaf 3151167918) (.leaf 3075648569))) (.branch 28 (.branch 27 (.leaf 3002590203) (.leaf 2931888034)) (.branch 29 (.leaf 2863442639) (.leaf 2797159644)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2732949423) (.branch 32 (.leaf 2670726828) (.leaf 2610410927))) (.branch 35 (.branch 34 (.leaf 2551924765) (.leaf 2495195143)) (.branch 36 (.leaf 2440152402) (.leaf 2386730232)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2334865484) (.leaf 2284497998)) (.branch 40 (.leaf 2235570444) (.leaf 2188028167))) (.branch 43 (.branch 42 (.leaf 2141819042) (.leaf 2096893345)) (.branch 44 (.leaf 2053203626) (.leaf 2010704584))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1969352965) (.branch 47 (.leaf 1929107446) (.leaf 1889928547))) (.branch 50 (.branch 49 (.leaf 1851778527) (.leaf 1814621302)) (.branch 51 (.leaf 1778422362) (.leaf 1743148688)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1708768681) (.leaf 1675252091)) (.branch 55 (.leaf 1642569953) (.leaf 1610694519))) (.branch 58 (.branch 57 (.leaf 1579599203) (.leaf 1549258526)) (.branch 59 (.leaf 1519648057) (.leaf 1490744369))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1462524988) (.branch 62 (.leaf 1434968349) (.leaf 1408053753))) (.branch 65 (.branch 64 (.leaf 1381761325) (.leaf 1356071978)) (.branch 66 (.leaf 1330967377) (.leaf 1306429901)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1282442612) (.leaf 1258989225)) (.branch 70 (.leaf 1236054078) (.leaf 1213622101))) (.branch 73 (.branch 72 (.leaf 1191678793) (.leaf 1170210196)) (.branch 74 (.leaf 1149202869) (.leaf 1128643867))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1108520717) (.branch 77 (.leaf 1088821401) (.leaf 1069534331))) (.branch 80 (.branch 79 (.leaf 1050648336) (.leaf 1032152641)) (.branch 81 (.leaf 1014036848) (.leaf 996290926)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 978905188) (.leaf 961870284)) (.branch 85 (.leaf 945177179) (.leaf 928817147))) (.branch 88 (.branch 87 (.leaf 912781754) (.leaf 897062848)) (.branch 89 (.leaf 881652546) (.leaf 866543221)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 851727499) (.branch 92 (.leaf 837198240) (.leaf 822948534))) (.branch 95 (.branch 94 (.leaf 808971691) (.leaf 795261231)) (.branch 96 (.leaf 781810875) (.leaf 768614540)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 755666331) (.leaf 742960530)) (.branch 100 (.leaf 730491594) (.leaf 718254144))) (.branch 103 (.branch 102 (.leaf 706242962) (.leaf 694452984)) (.branch 104 (.leaf 682879294) (.leaf 671517118))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 660361819) (.leaf 649408893)) (.branch 108 (.leaf 638653962) (.leaf 628092773))) (.branch 111 (.branch 110 (.leaf 617721189) (.leaf 607535189)) (.branch 112 (.leaf 597530859) (.leaf 587704394)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 578052091) (.leaf 568570344)) (.branch 116 (.leaf 559255646) (.leaf 550104577))) (.branch 119 (.branch 118 (.leaf 541113810) (.leaf 532280103)) (.branch 120 (.leaf 523600297) (.leaf 515071312)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 329).prefactor = (2391128907780723/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 329).cutoff/(generalMeanRows 329).c)).2 =
    (388702139702561/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 329).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 329).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 329).q*(generalMeanRows 329).c/2-2 = (311/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable072.value]
    have hcontinuation : (generalMeanRows 329).q*(generalMeanRows 329).cutoff/2-2 = (1044/559:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable140.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 329).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 329

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 329).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 329).criticalRate j.val*(generalMeanRows 329).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 329).c*(generalMeanRows 329).criticalPoint j.val)).2-
      (generalMeanRows 329).J/2-(generalMeanRows 329).error (generalMeanGrid j.val)+
      (generalMeanRows 329).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 329).c)).2-
      (generalMeanRows 329).J/2-(generalMeanRows 329).error 4 := by
  have he : (generalMeanRows 329).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 329) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 329)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0329

/-! Kernel-checked entropy margins for general spectral rectangle 330. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0330
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5859350950) (.branch 2 (.leaf 5678103444) (.leaf 5504699744))) (.branch 5 (.branch 4 (.leaf 5338698841) (.leaf 5179690624)) (.branch 6 (.leaf 5027293179) (.leaf 4881150383)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4740929745) (.leaf 4606320481)) (.branch 10 (.leaf 4477031773) (.leaf 4352791211))) (.branch 13 (.branch 12 (.leaf 4233343373) (.leaf 4118448549)) (.branch 14 (.leaf 4007881572) (.leaf 3901430768))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3798896981) (.branch 17 (.leaf 3700092700) (.leaf 3604841246))) (.branch 20 (.branch 19 (.leaf 3512976035) (.leaf 3424339897)) (.branch 21 (.leaf 3338784450) (.leaf 3256169528)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3176362644) (.leaf 3099238503)) (.branch 25 (.leaf 3024678547) (.leaf 2952570534))) (.branch 28 (.branch 27 (.leaf 2882808149) (.leaf 2815290640)) (.branch 29 (.leaf 2749922485) (.leaf 2686613075)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2625276427) (.branch 32 (.leaf 2565830911) (.leaf 2508198995))) (.branch 35 (.branch 34 (.leaf 2452307010) (.leaf 2398084931)) (.branch 36 (.leaf 2345466167) (.leaf 2294387370)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2244788256) (.leaf 2196611430)) (.branch 40 (.leaf 2149802233) (.leaf 2104308589))) (.branch 43 (.branch 42 (.leaf 2060080867) (.leaf 2017071749)) (.branch 44 (.leaf 1975236106) (.leaf 1934530883))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1894914988) (.branch 47 (.leaf 1856349193) (.leaf 1818796031))) (.branch 50 (.branch 49 (.leaf 1782219709) (.leaf 1746586023)) (.branch 51 (.leaf 1711862274) (.leaf 1678017191)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1645020864) (.leaf 1612844668)) (.branch 55 (.leaf 1581461207) (.leaf 1550844246))) (.branch 58 (.branch 57 (.leaf 1520968659) (.leaf 1491810371)) (.branch 59 (.leaf 1463346309) (.leaf 1435554352))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1408413285) (.branch 62 (.leaf 1381902757) (.leaf 1356003237))) (.branch 65 (.branch 64 (.leaf 1330695979) (.leaf 1305962981)) (.branch 66 (.leaf 1281786953) (.leaf 1258151281)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1235039997) (.leaf 1212437751)) (.branch 70 (.leaf 1190329779) (.leaf 1168701879))) (.branch 73 (.branch 72 (.leaf 1147540383) (.leaf 1126832135)) (.branch 74 (.leaf 1106564467) (.leaf 1086725177))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1067302510) (.branch 77 (.leaf 1048285133) (.leaf 1029662125))) (.branch 80 (.branch 79 (.leaf 1011422950) (.leaf 993557446)) (.branch 81 (.leaf 976055808) (.leaf 958908570)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 942106594) (.leaf 925641052)) (.branch 85 (.leaf 909503418) (.leaf 893685450))) (.branch 88 (.branch 87 (.leaf 878179181) (.leaf 862976910)) (.branch 89 (.leaf 848071183) (.leaf 833454793)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 819120762) (.branch 92 (.leaf 805062336) (.leaf 791272974))) (.branch 95 (.branch 94 (.leaf 777746341) (.leaf 764476297)) (.branch 96 (.leaf 751456893) (.leaf 738682361)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 726147108) (.leaf 713845709)) (.branch 100 (.leaf 701772899) (.leaf 689923571))) (.branch 103 (.branch 102 (.leaf 678292764) (.leaf 666875664)) (.branch 104 (.leaf 655667592) (.leaf 644664006))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 633860488) (.leaf 623252748)) (.branch 108 (.leaf 612836611) (.leaf 602608020))) (.branch 111 (.branch 110 (.leaf 592563028) (.leaf 582697792)) (.branch 112 (.leaf 573008575) (.leaf 563491740)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 554143742) (.leaf 544961133)) (.branch 116 (.leaf 535940551) (.leaf 527078722))) (.branch 119 (.branch 118 (.leaf 518372456) (.leaf 509818643)) (.branch 120 (.leaf 501414250) (.leaf 493156322)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 330).prefactor = (1171618801852349/250000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 330).cutoff/(generalMeanRows 330).c)).2 =
    (401947366452581/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 330).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 330).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 330).q*(generalMeanRows 330).c/2-2 = (253/400:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable141.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 330).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 330

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 330).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 330).criticalRate j.val*(generalMeanRows 330).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 330).c*(generalMeanRows 330).criticalPoint j.val)).2-
      (generalMeanRows 330).J/2-(generalMeanRows 330).error (generalMeanGrid j.val)+
      (generalMeanRows 330).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 330).c)).2-
      (generalMeanRows 330).J/2-(generalMeanRows 330).error 4 := by
  have he : (generalMeanRows 330).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 330) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 330)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0330

/-! Kernel-checked entropy margins for general spectral rectangle 331. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0331
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5615508312) (.branch 2 (.leaf 5442369148) (.leaf 5276776801))) (.branch 5 (.branch 4 (.leaf 5118302008) (.leaf 4966545787)) (.branch 6 (.leaf 4821136785) (.leaf 4681728924)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4547999286) (.leaf 4419646227)) (.branch 10 (.leaf 4296387667) (.leaf 4177959559))) (.branch 13 (.branch 12 (.leaf 4064114500) (.leaf 3954620469)) (.branch 14 (.leaf 3849259688) (.leaf 3747827577))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3650131811) (.branch 17 (.leaf 3555991443) (.leaf 3465236119))) (.branch 20 (.branch 19 (.leaf 3377705345) (.leaf 3293247818)) (.branch 21 (.leaf 3211720812) (.leaf 3132989613)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 3056926990) (.leaf 2983412719)) (.branch 25 (.leaf 2912333131) (.leaf 2843580703))) (.branch 28 (.branch 27 (.leaf 2777053670) (.leaf 2712655671)) (.branch 29 (.leaf 2650295420) (.leaf 2589886396)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2531346561) (.branch 32 (.leaf 2474598088) (.leaf 2419567116))) (.branch 35 (.branch 34 (.leaf 2366183518) (.leaf 2314380687)) (.branch 36 (.leaf 2264095326) (.leaf 2215267269)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2167839294) (.leaf 2121756968)) (.branch 40 (.leaf 2076968480) (.leaf 2033424506))) (.branch 43 (.branch 42 (.leaf 1991078066) (.leaf 1949884398)) (.branch 44 (.leaf 1909800838) (.leaf 1870786705))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1832803197) (.branch 47 (.leaf 1795813291) (.leaf 1759781646))) (.branch 50 (.branch 49 (.leaf 1724674519) (.leaf 1690459676)) (.branch 51 (.leaf 1657106320) (.leaf 1624585011)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1592867601) (.leaf 1561927164)) (.branch 55 (.leaf 1531737937) (.leaf 1502275261))) (.branch 58 (.branch 57 (.leaf 1473515523) (.leaf 1445436107)) (.branch 59 (.leaf 1418015344) (.leaf 1391232463))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1365067549) (.branch 62 (.leaf 1339501502) (.leaf 1314515995))) (.branch 65 (.branch 64 (.leaf 1290093438) (.leaf 1266216943)) (.branch 66 (.leaf 1242870290) (.leaf 1220037896)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1197704784) (.leaf 1175856554)) (.branch 70 (.leaf 1154479360) (.leaf 1133559878))) (.branch 73 (.branch 72 (.leaf 1113085287) (.leaf 1093043245)) (.branch 74 (.leaf 1073421865) (.leaf 1054209697))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 1035395706) (.branch 77 (.leaf 1016969256) (.leaf 998920089))) (.branch 80 (.branch 79 (.leaf 981238312) (.leaf 963914379)) (.branch 81 (.leaf 946939073) (.leaf 930303498)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 913999061) (.leaf 898017458)) (.branch 85 (.leaf 882350665) (.leaf 866990924))) (.branch 88 (.branch 87 (.leaf 851930733) (.leaf 837162834)) (.branch 89 (.leaf 822680204) (.leaf 808476045)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 794543774) (.branch 92 (.leaf 780877015) (.leaf 767469590))) (.branch 95 (.branch 94 (.leaf 754315514) (.leaf 741408983)) (.branch 96 (.leaf 728744368) (.leaf 716316211)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 704119215) (.leaf 692148238)) (.branch 100 (.leaf 680398291) (.leaf 668864526))) (.branch 103 (.branch 102 (.leaf 657542236) (.leaf 646426847)) (.branch 104 (.leaf 635513913) (.leaf 624799113))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 614278245) (.leaf 603947221)) (.branch 108 (.leaf 593802066) (.leaf 583838909))) (.branch 111 (.branch 110 (.leaf 574053984) (.leaf 564443625)) (.branch 112 (.leaf 555004261) (.leaf 545732413)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 536624693) (.leaf 527677799)) (.branch 116 (.leaf 518888512) (.leaf 510253693))) (.branch 119 (.branch 118 (.leaf 501770284) (.leaf 493435299)) (.branch 120 (.leaf 485245828) (.leaf 477199030)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 331).prefactor = (4581599392280411/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 331).cutoff/(generalMeanRows 331).c)).2 =
    (208725776494273/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 331).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 331).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 331).q*(generalMeanRows 331).c/2-2 = (16/25:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable012.value]
    have hcontinuation : (generalMeanRows 331).q*(generalMeanRows 331).cutoff/2-2 = (259/129:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable142.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 331).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 331

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 331).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 331).criticalRate j.val*(generalMeanRows 331).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 331).c*(generalMeanRows 331).criticalPoint j.val)).2-
      (generalMeanRows 331).J/2-(generalMeanRows 331).error (generalMeanGrid j.val)+
      (generalMeanRows 331).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 331).c)).2-
      (generalMeanRows 331).J/2-(generalMeanRows 331).error 4 := by
  have he : (generalMeanRows 331).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 331) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 331)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0331

/-! Kernel-checked entropy margins for general spectral rectangle 332. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0332
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4886640276) (.branch 2 (.leaf 4712298957) (.leaf 4545817639))) (.branch 5 (.branch 4 (.leaf 4386753114) (.leaf 4234693173)) (.branch 6 (.leaf 4089253905) (.leaf 3950077282)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3816829005) (.leaf 3689196573)) (.branch 10 (.leaf 3566887536) (.leaf 3449627933))) (.branch 13 (.branch 12 (.leaf 3337160869) (.leaf 3229245231)) (.branch 14 (.leaf 3125654518) (.leaf 3026175783))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2930608655) (.branch 17 (.leaf 2838764460) (.leaf 2750465407))) (.branch 20 (.branch 19 (.leaf 2665543845) (.leaf 2583841580)) (.branch 21 (.leaf 2505209243) (.leaf 2429505718)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2356597601) (.leaf 2286358711)) (.branch 25 (.leaf 2218669631) (.leaf 2153417287))) (.branch 28 (.branch 27 (.leaf 2090494555) (.leaf 2029799900)) (.branch 29 (.leaf 1971237033) (.leaf 1914714603)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1860145900) (.branch 32 (.leaf 1807448586) (.leaf 1756544435))) (.branch 35 (.branch 34 (.leaf 1707359103) (.leaf 1659821903)) (.branch 36 (.leaf 1613865598) (.leaf 1569426206)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1526442822) (.leaf 1484857444)) (.branch 40 (.leaf 1444614819) (.leaf 1405662288))) (.branch 43 (.branch 42 (.leaf 1367949651) (.leaf 1331429029)) (.branch 44 (.leaf 1296054749) (.leaf 1261783220))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1228572827) (.branch 47 (.leaf 1196383828) (.leaf 1165178256))) (.branch 50 (.branch 49 (.leaf 1134919831) (.leaf 1105573869)) (.branch 51 (.leaf 1077107205) (.leaf 1049488114)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1022686241) (.leaf 996672532)) (.branch 55 (.leaf 971419166) (.leaf 946899504))) (.branch 58 (.branch 57 (.leaf 923088019) (.leaf 899960252)) (.branch 59 (.leaf 877492756) (.leaf 855663046))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 834449558) (.branch 62 (.leaf 813831601) (.leaf 793789318))) (.branch 65 (.branch 64 (.leaf 774303646) (.leaf 755356281)) (.branch 66 (.leaf 736929638) (.leaf 719006825)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 701571605) (.leaf 684608370)) (.branch 70 (.leaf 668102111) (.leaf 652038392))) (.branch 73 (.branch 72 (.leaf 636403322) (.leaf 621183535)) (.branch 74 (.leaf 606366163) (.leaf 591938817))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 577889562) (.branch 77 (.leaf 564206903) (.leaf 550879760))) (.branch 80 (.branch 79 (.leaf 537897457) (.leaf 525249698)) (.branch 81 (.leaf 512926555) (.leaf 500918451)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 489216146) (.leaf 477810723)) (.branch 85 (.leaf 466693574) (.leaf 455856388))) (.branch 88 (.branch 87 (.leaf 445291138) (.leaf 434990071)) (.branch 89 (.leaf 424945693) (.leaf 415150767)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 405598291) (.branch 92 (.leaf 396281499) (.leaf 387193848))) (.branch 95 (.branch 94 (.leaf 378329006) (.leaf 369680849)) (.branch 96 (.leaf 361243450) (.leaf 353011072)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 344978162) (.leaf 337139341)) (.branch 100 (.leaf 329489401) (.leaf 322023296))) (.branch 103 (.branch 102 (.leaf 314736137) (.leaf 307623187)) (.branch 104 (.leaf 300679853) (.leaf 293901684))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 287284363) (.leaf 280823702)) (.branch 108 (.leaf 274515643) (.leaf 268356243))) (.branch 111 (.branch 110 (.leaf 262341681) (.leaf 256468247)) (.branch 112 (.leaf 250732338) (.leaf 245130458)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 239659212) (.leaf 234315304)) (.branch 116 (.leaf 229095529) (.leaf 223996778))) (.branch 119 (.branch 118 (.leaf 219016027) (.leaf 214150338)) (.branch 120 (.leaf 209396857) (.leaf 204752808)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 332).prefactor = (2360793562246847/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 332).cutoff/(generalMeanRows 332).c)).2 =
    (84352211328753/250000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 332).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 332).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 332).q*(generalMeanRows 332).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 332).q*(generalMeanRows 332).cutoff/2-2 = (259/129:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable142.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 332).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 332

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 332).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 332).criticalRate j.val*(generalMeanRows 332).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 332).c*(generalMeanRows 332).criticalPoint j.val)).2-
      (generalMeanRows 332).J/2-(generalMeanRows 332).error (generalMeanGrid j.val)+
      (generalMeanRows 332).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 332).c)).2-
      (generalMeanRows 332).J/2-(generalMeanRows 332).error 4 := by
  have he : (generalMeanRows 332).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 332) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 332)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0332

/-! Kernel-checked entropy margins for general spectral rectangle 333. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0333
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5058011154) (.branch 2 (.leaf 4884384014) (.leaf 4718557647))) (.branch 5 (.branch 4 (.leaf 4560087479) (.leaf 4408560266)) (.branch 6 (.leaf 4263591360) (.leaf 4124822275)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3991918503) (.leaf 3864567554)) (.branch 10 (.leaf 3742477197) (.leaf 3625373870))) (.branch 13 (.branch 12 (.leaf 3513001244) (.leaf 3405118913)) (.branch 14 (.leaf 3301501220) (.leaf 3201936170))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3106224452) (.branch 17 (.leaf 3014178540) (.leaf 2925621866))) (.branch 20 (.branch 19 (.leaf 2840388070) (.leaf 2758320307)) (.branch 21 (.leaf 2679270606) (.leaf 2603099285)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2529674410) (.leaf 2458871293)) (.branch 25 (.leaf 2390572032) (.leaf 2324665078))) (.branch 28 (.branch 27 (.leaf 2261044844) (.leaf 2199611332)) (.branch 29 (.leaf 2140269790) (.leaf 2082930402)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2027507981) (.branch 32 (.leaf 1973921702) (.leaf 1922094841))) (.branch 35 (.branch 34 (.leaf 1871954535) (.leaf 1823431561)) (.branch 36 (.leaf 1776460123) (.leaf 1730977663)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1686924670) (.leaf 1644244514)) (.branch 40 (.leaf 1602883285) (.leaf 1562789643))) (.branch 43 (.branch 42 (.leaf 1523914673) (.leaf 1486211759)) (.branch 44 (.leaf 1449636455) (.leaf 1414146370))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1379701059) (.branch 47 (.leaf 1346261920) (.leaf 1313792094))) (.branch 50 (.branch 49 (.leaf 1282256377) (.leaf 1251621133)) (.branch 51 (.leaf 1221854212) (.leaf 1192924877)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1164803728) (.leaf 1137462636)) (.branch 55 (.leaf 1110874678) (.leaf 1085014080))) (.branch 58 (.branch 57 (.leaf 1059856154) (.leaf 1035377251)) (.branch 59 (.leaf 1011554705) (.leaf 988366786))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 965792656) (.branch 62 (.leaf 943812325) (.leaf 922406610))) (.branch 65 (.branch 64 (.leaf 901557098) (.leaf 881246107)) (.branch 66 (.leaf 861456653) (.leaf 842172419)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 823377721) (.leaf 805057479)) (.branch 70 (.leaf 787197194) (.leaf 769782912))) (.branch 73 (.branch 72 (.leaf 752801210) (.leaf 736239164)) (.branch 74 (.leaf 720084331) (.leaf 704324726))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 688948801) (.branch 77 (.leaf 673945426) (.leaf 659303874))) (.branch 80 (.branch 79 (.leaf 645013798) (.leaf 631065219)) (.branch 81 (.leaf 617448508) (.leaf 604154372)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 591173839) (.leaf 578498245)) (.branch 85 (.leaf 566119222) (.leaf 554028682))) (.branch 88 (.branch 87 (.leaf 542218812) (.leaf 530682056)) (.branch 89 (.leaf 519411108) (.leaf 508398903)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 497638605) (.branch 92 (.leaf 487123596) (.leaf 476847473))) (.branch 95 (.branch 94 (.leaf 466804036) (.leaf 456987279)) (.branch 96 (.leaf 447391386) (.leaf 438010720)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 428839818) (.leaf 419873386)) (.branch 100 (.leaf 411106288) (.leaf 402533546))) (.branch 103 (.branch 102 (.leaf 394150329) (.leaf 385951950)) (.branch 104 (.leaf 377933861) (.leaf 370091647))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 362421022) (.leaf 354917822)) (.branch 108 (.leaf 347578005) (.leaf 340397643))) (.branch 111 (.branch 110 (.leaf 333372920) (.leaf 326500126)) (.branch 112 (.leaf 319775657) (.leaf 313196006)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 306757764) (.leaf 300457618)) (.branch 116 (.leaf 294292342) (.leaf 288258798))) (.branch 119 (.branch 118 (.leaf 282353933) (.leaf 276574776)) (.branch 120 (.leaf 270918434) (.leaf 265382092)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 333).prefactor = (4719818171200337/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 333).cutoff/(generalMeanRows 333).c)).2 =
    (372452249075193/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 333).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 333).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 333).q*(generalMeanRows 333).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 333).q*(generalMeanRows 333).cutoff/2-2 = (524/255:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable143.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 333).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 333

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 333).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 333).criticalRate j.val*(generalMeanRows 333).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 333).c*(generalMeanRows 333).criticalPoint j.val)).2-
      (generalMeanRows 333).J/2-(generalMeanRows 333).error (generalMeanGrid j.val)+
      (generalMeanRows 333).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 333).c)).2-
      (generalMeanRows 333).J/2-(generalMeanRows 333).error 4 := by
  have he : (generalMeanRows 333).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 333) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 333)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0333

/-! Kernel-checked entropy margins for general spectral rectangle 334. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0334
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5194071442) (.branch 2 (.leaf 5020749108) (.leaf 4855190023))) (.branch 5 (.branch 4 (.leaf 4696948912) (.leaf 4545612020)) (.branch 6 (.leaf 4400794361) (.leaf 4262137263)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4129306175) (.leaf 4001988692)) (.branch 10 (.leaf 3879892782) (.leaf 3762745185))) (.branch 13 (.branch 12 (.leaf 3650289965) (.leaf 3542287196)) (.branch 14 (.leaf 3438511768) (.leaf 3338752304))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3242810163) (.branch 17 (.leaf 3150498541) (.leaf 3061641638))) (.branch 20 (.branch 19 (.leaf 2976073895) (.leaf 2893639302)) (.branch 21 (.leaf 2814190749) (.leaf 2737589439)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2663704337) (.leaf 2592411673)) (.branch 25 (.leaf 2523594467) (.leaf 2457142106))) (.branch 28 (.branch 27 (.leaf 2392949937) (.leaf 2330918901)) (.branch 29 (.leaf 2270955185) (.leaf 2212969904)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2156878801) (.branch 32 (.leaf 2102601974) (.leaf 2050063611))) (.branch 35 (.branch 34 (.leaf 1999191754) (.leaf 1949918071)) (.branch 36 (.leaf 1902177648) (.leaf 1855908791)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1811052842) (.leaf 1767554010)) (.branch 40 (.leaf 1725359206) (.leaf 1684417894))) (.branch 43 (.branch 42 (.leaf 1644681950) (.leaf 1606105530)) (.branch 44 (.leaf 1568644942) (.leaf 1532258533))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1496906576) (.branch 47 (.leaf 1462551170) (.leaf 1429156140))) (.branch 50 (.branch 49 (.leaf 1396686948) (.leaf 1365110604)) (.branch 51 (.leaf 1334395589) (.leaf 1304511776)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1275430358) (.leaf 1247123783)) (.branch 55 (.leaf 1219565688) (.leaf 1192730837))) (.branch 58 (.branch 57 (.leaf 1166595070) (.leaf 1141135243)) (.branch 59 (.leaf 1116329180) (.leaf 1092155628))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1068594207) (.branch 62 (.leaf 1045625368) (.leaf 1023230356))) (.branch 65 (.branch 64 (.leaf 1001391170) (.leaf 980090525)) (.branch 66 (.leaf 959311820) (.leaf 939039106)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 919257053) (.leaf 899950922)) (.branch 70 (.leaf 881106540) (.leaf 862710270))) (.branch 73 (.branch 72 (.leaf 844748988) (.leaf 827210060)) (.branch 74 (.leaf 810081320) (.leaf 793351049))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 777007951) (.branch 77 (.leaf 761041142) (.leaf 745440124))) (.branch 80 (.branch 79 (.leaf 730194773) (.leaf 715295321)) (.branch 81 (.leaf 700732339) (.leaf 686496727)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 672579693) (.leaf 658972749)) (.branch 85 (.leaf 645667688) (.leaf 632656580))) (.branch 88 (.branch 87 (.leaf 619931757) (.leaf 607485805)) (.branch 89 (.leaf 595311547) (.leaf 583402043)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 571750572) (.branch 92 (.leaf 560350628) (.leaf 549195909))) (.branch 95 (.branch 94 (.leaf 538280310) (.leaf 527597917)) (.branch 96 (.leaf 517142995) (.leaf 506909985)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 496893496) (.leaf 487088299)) (.branch 100 (.leaf 477489321) (.leaf 468091637))) (.branch 103 (.branch 102 (.leaf 458890467) (.leaf 449881169)) (.branch 104 (.leaf 441059237) (.leaf 432420292))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 423960080) (.leaf 415674465)) (.branch 108 (.leaf 407559428) (.leaf 399611063))) (.branch 111 (.branch 110 (.leaf 391825567) (.leaf 384199246)) (.branch 112 (.leaf 376728503) (.leaf 369409839)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 362239847) (.leaf 355215213)) (.branch 116 (.leaf 348332708) (.leaf 341589189))) (.branch 119 (.branch 118 (.leaf 334981595) (.leaf 328506941)) (.branch 120 (.leaf 322162324) (.leaf 315944909)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 334).prefactor = (4718726191479517/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 334).cutoff/(generalMeanRows 334).c)).2 =
    (24639082522417/62500000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 334).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 334).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 334).q*(generalMeanRows 334).c/2-2 = (3/4:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable019.value]
    have hcontinuation : (generalMeanRows 334).q*(generalMeanRows 334).cutoff/2-2 = (1054/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable144.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 334).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 334

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 334).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 334).criticalRate j.val*(generalMeanRows 334).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 334).c*(generalMeanRows 334).criticalPoint j.val)).2-
      (generalMeanRows 334).J/2-(generalMeanRows 334).error (generalMeanGrid j.val)+
      (generalMeanRows 334).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 334).c)).2-
      (generalMeanRows 334).J/2-(generalMeanRows 334).error 4 := by
  have he : (generalMeanRows 334).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 334) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 334)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0334

/-! Kernel-checked entropy margins for general spectral rectangle 335. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0335
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5055613834) (.branch 2 (.leaf 4881932942) (.leaf 4716087125))) (.branch 5 (.branch 4 (.leaf 4557627726) (.leaf 4406137791)) (.branch 6 (.leaf 4261229305) (.leaf 4122540724)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3989734767) (.leaf 3862496432)) (.branch 10 (.leaf 3740531217) (.leaf 3623563503))) (.branch 13 (.branch 12 (.leaf 3511335104) (.leaf 3403603944)) (.branch 14 (.leaf 3300142858) (.leaf 3200738500))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3105190345) (.branch 17 (.leaf 3013309783) (.leaf 2924919278))) (.branch 20 (.branch 19 (.leaf 2839851611) (.leaf 2757949170)) (.branch 21 (.leaf 2679063313) (.leaf 2603053764)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2529788071) (.leaf 2459141096)) (.branch 25 (.leaf 2390994545) (.leaf 2325236538))) (.branch 28 (.branch 27 (.leaf 2261761203) (.leaf 2200468306)) (.branch 29 (.leaf 2141262902) (.leaf 2084055015)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2028759337) (.branch 32 (.leaf 1975294950) (.leaf 1923585064))) (.branch 35 (.branch 34 (.leaf 1873556778) (.leaf 1825140851)) (.branch 36 (.leaf 1778271491) (.leaf 1732886158)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1688925377) (.leaf 1646332569)) (.branch 40 (.leaf 1605053886) (.leaf 1565038060))) (.branch 43 (.branch 42 (.leaf 1526236258) (.leaf 1488601955)) (.branch 44 (.leaf 1452090801) (.leaf 1416660509))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1382270742) (.branch 47 (.leaf 1348883007) (.leaf 1316460563))) (.branch 50 (.branch 49 (.leaf 1284968321) (.leaf 1254372767)) (.branch 51 (.leaf 1224641870) (.leaf 1195745015)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1167652922) (.leaf 1140337584)) (.branch 55 (.leaf 1113772201) (.leaf 1087931116))) (.branch 58 (.branch 57 (.leaf 1062789764) (.leaf 1038324610)) (.branch 59 (.leaf 1014513104) (.leaf 991333632))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 968765468) (.branch 62 (.leaf 946788731) (.leaf 925384345))) (.branch 65 (.branch 64 (.leaf 904534003) (.leaf 884220126)) (.branch 66 (.leaf 864425830) (.leaf 845134895)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 826331733) (.leaf 808001356)) (.branch 70 (.leaf 790129353) (.leaf 772701859))) (.branch 73 (.branch 72 (.leaf 755705533) (.leaf 739127534)) (.branch 74 (.leaf 722955497) (.leaf 707177513))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 691782108) (.branch 77 (.leaf 676758222) (.leaf 662095197))) (.branch 80 (.branch 79 (.leaf 647782752) (.leaf 633810970)) (.branch 81 (.leaf 620170283) (.leaf 606851457)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 593845576) (.leaf 581144029)) (.branch 85 (.leaf 568738500) (.leaf 556620951))) (.branch 88 (.branch 87 (.leaf 544783616) (.leaf 533218984)) (.branch 89 (.leaf 521919792) (.leaf 510879017)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 500089861) (.branch 92 (.leaf 489545745) (.leaf 479240302))) (.branch 95 (.branch 94 (.leaf 469167364) (.leaf 459320960)) (.branch 96 (.leaf 449695303) (.leaf 440284786)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 431083974) (.leaf 422087599)) (.branch 100 (.leaf 413290550) (.leaf 404687872))) (.branch 103 (.branch 102 (.leaf 396274757) (.leaf 388046540)) (.branch 104 (.leaf 379998691) (.leaf 372126815))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 364426642) (.leaf 356894027)) (.branch 108 (.leaf 349524943) (.leaf 342315475))) (.branch 111 (.branch 110 (.leaf 335261821) (.leaf 328360285)) (.branch 112 (.leaf 321607273) (.leaf 314999291)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 308532940) (.leaf 302204916)) (.branch 116 (.leaf 296012001) (.leaf 289951066))) (.branch 119 (.branch 118 (.leaf 284019065) (.leaf 278213035)) (.branch 120 (.leaf 272530088) (.leaf 266967415)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 335).prefactor = (4752614038175123/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 335).cutoff/(generalMeanRows 335).c)).2 =
    (189175985601191/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 335).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 335).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 335).q*(generalMeanRows 335).c/2-2 = (397/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable105.value]
    have hcontinuation : (generalMeanRows 335).q*(generalMeanRows 335).cutoff/2-2 = (1054/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable144.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 335).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 335

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 335).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 335).criticalRate j.val*(generalMeanRows 335).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 335).c*(generalMeanRows 335).criticalPoint j.val)).2-
      (generalMeanRows 335).J/2-(generalMeanRows 335).error (generalMeanGrid j.val)+
      (generalMeanRows 335).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 335).c)).2-
      (generalMeanRows 335).J/2-(generalMeanRows 335).error 4 := by
  have he : (generalMeanRows 335).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 335) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 335)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0335

/-! Kernel-checked entropy margins for general spectral rectangle 336. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0336
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5009826570) (.branch 2 (.leaf 4835432011) (.leaf 4668902445))) (.branch 5 (.branch 4 (.leaf 4509789907) (.leaf 4357677977)) (.branch 6 (.leaf 4212179024) (.leaf 4072931758)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3939599028) (.leaf 3811865855)) (.branch 10 (.leaf 3689437660) (.leaf 3572038658))) (.branch 13 (.branch 12 (.leaf 3459410419) (.leaf 3351310551)) (.branch 14 (.leaf 3247511507) (.leaf 3147799508))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3051973543) (.branch 17 (.leaf 2959844471) (.leaf 2871234192))) (.branch 20 (.branch 19 (.leaf 2785974887) (.leaf 2703908319)) (.branch 21 (.leaf 2624885193) (.leaf 2548764566)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2475413299) (.leaf 2404705556)) (.branch 25 (.leaf 2336522336) (.leaf 2270751044))) (.branch 28 (.branch 27 (.leaf 2207285090) (.leaf 2146023520)) (.branch 29 (.leaf 2086870667) (.leaf 2029735838)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1974533009) (.branch 32 (.leaf 1921180553) (.leaf 1869600976))) (.branch 35 (.branch 34 (.leaf 1819720682) (.leaf 1771469743)) (.branch 36 (.leaf 1724781688) (.leaf 1679593310)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1635844480) (.leaf 1593477973)) (.branch 40 (.leaf 1552439310) (.leaf 1512676603))) (.branch 43 (.branch 42 (.leaf 1474140414) (.leaf 1436783624)) (.branch 44 (.leaf 1400561305) (.leaf 1365430605))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1331350635) (.branch 47 (.leaf 1298282365) (.leaf 1266188532))) (.branch 50 (.branch 49 (.leaf 1235033538) (.leaf 1204783372)) (.branch 51 (.leaf 1175405526) (.leaf 1146868915)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1119143810) (.leaf 1092201762)) (.branch 55 (.leaf 1066015546) (.leaf 1040559094))) (.branch 58 (.branch 57 (.leaf 1015807440) (.leaf 991736666)) (.branch 59 (.leaf 968323849) (.leaf 945547012))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 923385083) (.branch 62 (.leaf 901817844) (.leaf 880825897))) (.branch 65 (.branch 64 (.leaf 860390621) (.leaf 840494136)) (.branch 66 (.leaf 821119269) (.leaf 802249521)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 783869035) (.leaf 765962566)) (.branch 70 (.leaf 748515454) (.leaf 731513597))) (.branch 73 (.branch 72 (.leaf 714943425) (.leaf 698791878)) (.branch 74 (.leaf 683046381) (.leaf 667694824))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 652725538) (.branch 77 (.leaf 638127283) (.leaf 623889220))) (.branch 80 (.branch 79 (.leaf 610000902) (.leaf 596452251)) (.branch 81 (.leaf 583233545) (.leaf 570335404)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 557748772) (.leaf 545464906)) (.branch 85 (.leaf 533475363) (.leaf 521771985))) (.branch 88 (.branch 87 (.leaf 510346892) (.leaf 499192465)) (.branch 89 (.leaf 488301339) (.leaf 477666394)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 467280739) (.branch 92 (.leaf 457137711) (.leaf 447230859))) (.branch 95 (.branch 94 (.leaf 437553940) (.leaf 428100909)) (.branch 96 (.leaf 418865913) (.leaf 409843279)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 401027516) (.leaf 392413297)) (.branch 100 (.leaf 383995462) (.leaf 375769007))) (.branch 103 (.branch 102 (.leaf 367729080) (.leaf 359870974)) (.branch 104 (.leaf 352190122) (.leaf 344682094))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 337342590) (.leaf 330167435)) (.branch 108 (.leaf 323152575) (.leaf 316294074))) (.branch 111 (.branch 110 (.leaf 309588109) (.leaf 303030965)) (.branch 112 (.leaf 296619032) (.leaf 290348804)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 284216870) (.leaf 278219915)) (.branch 116 (.leaf 272354716) (.leaf 266618139))) (.branch 119 (.branch 118 (.leaf 261007134) (.leaf 255518735)) (.branch 120 (.leaf 250150055) (.leaf 244898285)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 336).prefactor = (2377140471470981/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 336).cutoff/(generalMeanRows 336).c)).2 =
    (45576133951771/125000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 336).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 336).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 336).q*(generalMeanRows 336).c/2-2 = (102/125:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable107.value]
    have hcontinuation : (generalMeanRows 336).q*(generalMeanRows 336).cutoff/2-2 = (524/255:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable143.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 336).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 336

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 336).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 336).criticalRate j.val*(generalMeanRows 336).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 336).c*(generalMeanRows 336).criticalPoint j.val)).2-
      (generalMeanRows 336).J/2-(generalMeanRows 336).error (generalMeanGrid j.val)+
      (generalMeanRows 336).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 336).c)).2-
      (generalMeanRows 336).J/2-(generalMeanRows 336).error 4 := by
  have he : (generalMeanRows 336).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 336) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 336)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0336

/-! Kernel-checked entropy margins for general spectral rectangle 337. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0337
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4880656001) (.branch 2 (.leaf 4706093162) (.leaf 4539465714))) (.branch 5 (.branch 4 (.leaf 4380322060) (.leaf 4228242348)) (.branch 6 (.leaf 4082835705) (.leaf 3943737767)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3810608471) (.leaf 3683130074)) (.branch 10 (.leaf 3561005366) (.leaf 3443956065))) (.branch 13 (.branch 12 (.leaf 3331721358) (.leaf 3224056584)) (.branch 14 (.leaf 3120732035) (.leaf 3021531860))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2926253078) (.branch 17 (.leaf 2834704662) (.leaf 2746706706))) (.branch 20 (.branch 19 (.leaf 2662089663) (.leaf 2580693646)) (.branch 21 (.leaf 2502367774) (.leaf 2426969589)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2354364496) (.leaf 2284425265)) (.branch 25 (.leaf 2217031557) (.leaf 2152069496))) (.branch 28 (.branch 27 (.leaf 2089431259) (.leaf 2029014710)) (.branch 29 (.leaf 1970723049) (.leaf 1914464492)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1860151971) (.branch 32 (.leaf 1807702853) (.leaf 1757038683))) (.branch 35 (.branch 34 (.leaf 1708084936) (.leaf 1660770794)) (.branch 36 (.leaf 1615028934) (.leaf 1570795329)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1528009061) (.leaf 1486612150)) (.branch 40 (.leaf 1446549390) (.leaf 1407768196))) (.branch 43 (.branch 42 (.leaf 1370218462) (.leaf 1333852426)) (.branch 44 (.leaf 1298624545) (.leaf 1264491374))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1231411458) (.branch 47 (.leaf 1199345225) (.leaf 1168254888))) (.branch 50 (.branch 49 (.leaf 1138104351) (.leaf 1108859126)) (.branch 51 (.leaf 1080486243) (.leaf 1052954182)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1026232789) (.leaf 1000293218)) (.branch 55 (.leaf 975107858) (.leaf 950650272))) (.branch 58 (.branch 57 (.leaf 926895145) (.leaf 903818222)) (.branch 59 (.leaf 881396260) (.leaf 859606978))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 838429011) (.branch 62 (.leaf 817841866) (.leaf 797825879))) (.branch 65 (.branch 64 (.leaf 778362178) (.leaf 759432645)) (.branch 66 (.leaf 741019879) (.leaf 723107167)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 705678446) (.leaf 688718279)) (.branch 70 (.leaf 672211822) (.leaf 656144800))) (.branch 73 (.branch 72 (.leaf 640503481) (.leaf 625274649)) (.branch 74 (.leaf 610445586) (.leaf 596004043))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 581938227) (.branch 77 (.leaf 568236774) (.leaf 554888737))) (.branch 80 (.branch 79 (.leaf 541883562) (.leaf 529211075)) (.branch 81 (.leaf 516861465) (.leaf 504825266)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 493093347) (.leaf 481656893)) (.branch 85 (.leaf 470507398) (.leaf 459636646))) (.branch 88 (.branch 87 (.leaf 449036702) (.leaf 438699900)) (.branch 89 (.leaf 428618834) (.leaf 418786344)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 409195508) (.branch 92 (.leaf 399839634) (.leaf 390712249))) (.branch 95 (.branch 94 (.leaf 381807089) (.leaf 373118095)) (.branch 96 (.leaf 364639402) (.leaf 356365331)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 348290384) (.leaf 340409237)) (.branch 100 (.leaf 332716731) (.leaf 325207869))) (.branch 103 (.branch 102 (.leaf 317877808) (.leaf 310721853)) (.branch 104 (.leaf 303735453) (.leaf 296914195))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 290253799) (.leaf 283750112)) (.branch 108 (.leaf 277399107) (.leaf 271196874))) (.branch 111 (.branch 110 (.leaf 265139620) (.leaf 259223661)) (.branch 112 (.leaf 253445422) (.leaf 247801429)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 242288311) (.leaf 236902791)) (.branch 116 (.leaf 231641686) (.leaf 226501903))) (.branch 119 (.branch 118 (.leaf 221480436) (.leaf 216574363)) (.branch 120 (.leaf 211780844) (.leaf 207097116)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 337).prefactor = (478899535205457/100000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 337).cutoff/(generalMeanRows 337).c)).2 =
    (174552442539101/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 337).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 337).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 337).q*(generalMeanRows 337).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 337).q*(generalMeanRows 337).cutoff/2-2 = (524/255:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable143.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 337).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 337

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 337).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 337).criticalRate j.val*(generalMeanRows 337).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 337).c*(generalMeanRows 337).criticalPoint j.val)).2-
      (generalMeanRows 337).J/2-(generalMeanRows 337).error (generalMeanGrid j.val)+
      (generalMeanRows 337).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 337).c)).2-
      (generalMeanRows 337).J/2-(generalMeanRows 337).error 4 := by
  have he : (generalMeanRows 337).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 337) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 337)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0337

/-! Kernel-checked entropy margins for general spectral rectangle 338. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0338
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5322544786) (.branch 2 (.leaf 5155617752) (.leaf 4996040223))) (.branch 5 (.branch 4 (.leaf 4843389828) (.leaf 4697274190)) (.branch 6 (.leaf 4557328302) (.leaf 4423212197)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4294608852) (.leaf 4171222309)) (.branch 10 (.leaf 4052775989) (.leaf 3939011163))) (.branch 13 (.branch 12 (.leaf 3829685574) (.leaf 3724572188)) (.branch 14 (.leaf 3623458053) (.leaf 3526143266))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3432440032) (.branch 17 (.leaf 3342171797) (.leaf 3255172459))) (.branch 20 (.branch 19 (.leaf 3171285645) (.leaf 3090364045)) (.branch 21 (.leaf 3012268799) (.leaf 2936868935)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2864040848) (.leaf 2793667819)) (.branch 25 (.leaf 2725639575) (.leaf 2659851873))) (.branch 28 (.branch 27 (.leaf 2596206121) (.leaf 2534609029)) (.branch 29 (.leaf 2474972273) (.leaf 2417212199)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2361249532) (.branch 32 (.leaf 2307009118) (.leaf 2254419672))) (.branch 35 (.branch 34 (.leaf 2203413554) (.leaf 2153926555)) (.branch 36 (.leaf 2105897692) (.leaf 2059269026)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2013985485) (.leaf 1969994703)) (.branch 40 (.leaf 1927246863) (.leaf 1885694559))) (.branch 43 (.branch 42 (.leaf 1845292656) (.leaf 1805998169)) (.branch 44 (.leaf 1767770141) (.leaf 1730569535))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1694359128) (.branch 47 (.leaf 1659103414) (.leaf 1624768510))) (.branch 50 (.branch 49 (.leaf 1591322072) (.leaf 1558733213)) (.branch 51 (.leaf 1526972424) (.leaf 1496011506)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1465823499) (.leaf 1436382616)) (.branch 55 (.leaf 1407664188) (.leaf 1379644604))) (.branch 58 (.branch 57 (.leaf 1352301256) (.leaf 1325612491)) (.branch 59 (.leaf 1299557560) (.leaf 1274116579))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1249270477) (.branch 62 (.leaf 1225000963) (.leaf 1201290487))) (.branch 65 (.branch 64 (.leaf 1178122201) (.leaf 1155479927)) (.branch 66 (.leaf 1133348123) (.leaf 1111711856)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1090556771) (.leaf 1069869061)) (.branch 70 (.leaf 1049635447) (.leaf 1029843149))) (.branch 73 (.branch 72 (.leaf 1010479864) (.leaf 991533744)) (.branch 74 (.leaf 972993377) (.leaf 954847763))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 937086300) (.branch 77 (.leaf 919698762) (.leaf 902675287))) (.branch 80 (.branch 79 (.leaf 886006356) (.leaf 869682781)) (.branch 81 (.leaf 853695689) (.leaf 838036509)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 822696958) (.leaf 807669032)) (.branch 85 (.leaf 792944990) (.leaf 778517344))) (.branch 88 (.branch 87 (.leaf 764378850) (.leaf 750522496)) (.branch 89 (.leaf 736941495) (.leaf 723629272)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 710579458) (.branch 92 (.leaf 697785881) (.leaf 685242560))) (.branch 95 (.branch 94 (.leaf 672943692) (.leaf 660883652)) (.branch 96 (.leaf 649056980) (.leaf 637458380)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 626082708) (.leaf 614924971)) (.branch 100 (.leaf 603980318) (.leaf 593244038))) (.branch 103 (.branch 102 (.leaf 582711551) (.leaf 572378405)) (.branch 104 (.leaf 562240273) (.leaf 552292945))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 542532326) (.leaf 532954431)) (.branch 108 (.leaf 523555383) (.leaf 514331407))) (.branch 111 (.branch 110 (.leaf 505278826) (.leaf 496394060)) (.branch 112 (.leaf 487673622) (.leaf 479114114)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 470712222) (.leaf 462464720)) (.branch 116 (.leaf 454368458) (.leaf 446420368))) (.branch 119 (.branch 118 (.leaf 438617455) (.leaf 430956798)) (.branch 120 (.leaf 423435548) (.leaf 416050922)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 338).prefactor = (906568420869499/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 338).cutoff/(generalMeanRows 338).c)).2 =
    (211598597142313/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 338).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 338).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 338).q*(generalMeanRows 338).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 338).q*(generalMeanRows 338).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 338).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 338

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 338).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 338).criticalRate j.val*(generalMeanRows 338).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 338).c*(generalMeanRows 338).criticalPoint j.val)).2-
      (generalMeanRows 338).J/2-(generalMeanRows 338).error (generalMeanGrid j.val)+
      (generalMeanRows 338).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 338).c)).2-
      (generalMeanRows 338).J/2-(generalMeanRows 338).error 4 := by
  have he : (generalMeanRows 338).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 338) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 338)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0338

/-! Kernel-checked entropy margins for general spectral rectangle 339. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0339
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5305456995) (.branch 2 (.leaf 5136429224) (.leaf 4974865149))) (.branch 5 (.branch 4 (.leaf 4820336410) (.leaf 4672445039)) (.branch 6 (.leaf 4530820803) (.leaf 4395118841)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4265017539) (.leaf 4140216635)) (.branch 10 (.leaf 4020435497) (.leaf 3905411587))) (.branch 13 (.branch 12 (.leaf 3794899057) (.leaf 3688667487)) (.branch 14 (.leaf 3586500728) (.leaf 3488195858))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3393562222) (.branch 17 (.leaf 3302420563) (.leaf 3214602216))) (.branch 20 (.branch 19 (.leaf 3129948377) (.leaf 3048309431)) (.branch 21 (.leaf 2969544327) (.leaf 2893520012)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2820110901) (.leaf 2749198393)) (.branch 25 (.leaf 2680670419) (.leaf 2614421028))) (.branch 28 (.branch 27 (.leaf 2550350000) (.leaf 2488362489)) (.branch 29 (.leaf 2428368690) (.leaf 2370283530)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2314026383) (.branch 32 (.leaf 2259520800) (.leaf 2206694260))) (.branch 35 (.branch 34 (.leaf 2155477942) (.leaf 2105806501)) (.branch 36 (.leaf 2057617871) (.leaf 2010853074)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1965456043) (.leaf 1921373457)) (.branch 40 (.leaf 1878554586) (.leaf 1836951144))) (.branch 43 (.branch 42 (.leaf 1796517155) (.leaf 1757208825)) (.branch 44 (.leaf 1718984422) (.leaf 1681804161))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1645630105) (.branch 47 (.leaf 1610426057) (.leaf 1576157474))) (.branch 50 (.branch 49 (.leaf 1542791376) (.leaf 1510296263)) (.branch 51 (.leaf 1478642038) (.leaf 1447799936)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1417742450) (.leaf 1388443270)) (.branch 55 (.leaf 1359877223) (.leaf 1332020210))) (.branch 58 (.branch 57 (.leaf 1304849155) (.leaf 1278341954)) (.branch 59 (.leaf 1252477425) (.leaf 1227235263))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1202595994) (.branch 62 (.leaf 1178540941) (.leaf 1155052176))) (.branch 65 (.branch 64 (.leaf 1132112490) (.leaf 1109705359)) (.branch 66 (.leaf 1087814904) (.leaf 1066425869)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1045523585) (.leaf 1025093947)) (.branch 70 (.leaf 1005123383) (.leaf 985598835))) (.branch 73 (.branch 72 (.leaf 966507730) (.leaf 947837959)) (.branch 74 (.leaf 929577859) (.leaf 911716188))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 894242110) (.branch 77 (.leaf 877145176) (.leaf 860415304))) (.branch 80 (.branch 79 (.leaf 844042767) (.leaf 828018173)) (.branch 81 (.leaf 812332456) (.leaf 796976857)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 781942912) (.leaf 767222442)) (.branch 85 (.leaf 752807536) (.leaf 738690546))) (.branch 88 (.branch 87 (.leaf 724864070) (.leaf 711320946)) (.branch 89 (.leaf 698054240) (.leaf 685057238)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 672323436) (.branch 92 (.leaf 659846533) (.leaf 647620420))) (.branch 95 (.branch 94 (.leaf 635639176) (.leaf 623897059)) (.branch 96 (.leaf 612388497) (.leaf 601108085)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 590050577) (.leaf 579210881)) (.branch 100 (.leaf 568584049) (.leaf 558165277))) (.branch 103 (.branch 102 (.leaf 547949898) (.leaf 537933375)) (.branch 104 (.leaf 528111297) (.leaf 518479377))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 509033445) (.leaf 499769443)) (.branch 108 (.leaf 490683425) (.leaf 481771548))) (.branch 111 (.branch 110 (.leaf 473030072) (.leaf 464455357)) (.branch 112 (.leaf 456043855) (.leaf 447792113)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 439696764) (.leaf 431754530)) (.branch 116 (.leaf 423962212) (.leaf 416316696))) (.branch 119 (.branch 118 (.leaf 408814941) (.leaf 401453984)) (.branch 120 (.leaf 394230935) (.leaf 387142974)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 339).prefactor = (919409555754079/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 339).cutoff/(generalMeanRows 339).c)).2 =
    (415197151617551/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 339).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 339).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 339).q*(generalMeanRows 339).c/2-2 = (2793/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable128.value]
    have hcontinuation : (generalMeanRows 339).q*(generalMeanRows 339).cutoff/2-2 = (48/23:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable145.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 339).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 339

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 339).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 339).criticalRate j.val*(generalMeanRows 339).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 339).c*(generalMeanRows 339).criticalPoint j.val)).2-
      (generalMeanRows 339).J/2-(generalMeanRows 339).error (generalMeanGrid j.val)+
      (generalMeanRows 339).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 339).c)).2-
      (generalMeanRows 339).J/2-(generalMeanRows 339).error 4 := by
  have he : (generalMeanRows 339).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 339) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 339)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0339

/-! Kernel-checked entropy margins for general spectral rectangle 340. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0340
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4922783931) (.branch 2 (.leaf 4748887276) (.leaf 4582896087))) (.branch 5 (.branch 4 (.leaf 4424358191) (.leaf 4272853311)) (.branch 6 (.leaf 4127990287) (.leaf 3989404594)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3856756121) (.leaf 3729727182)) (.branch 10 (.leaf 3608020716) (.leaf 3491358669))) (.branch 13 (.branch 12 (.leaf 3379480537) (.leaf 3272142027)) (.branch 14 (.leaf 3169113862) (.leaf 3070180674))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2975140008) (.branch 17 (.leaf 2883801401) (.leaf 2795985550))) (.branch 20 (.branch 19 (.leaf 2711523536) (.leaf 2630256124)) (.branch 21 (.leaf 2552033109) (.leaf 2476712722)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2404161072) (.leaf 2334251642)) (.branch 25 (.leaf 2266864815) (.leaf 2201887437))) (.branch 28 (.branch 27 (.leaf 2139212414) (.leaf 2078738336)) (.branch 29 (.leaf 2020369128) (.leaf 1964013727)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1909585781) (.branch 32 (.leaf 1857003367) (.leaf 1806188729))) (.branch 35 (.branch 34 (.leaf 1757068036) (.leaf 1709571153)) (.branch 36 (.leaf 1663631428) (.leaf 1619185492)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1576173077) (.leaf 1534536837)) (.branch 40 (.leaf 1494222189) (.leaf 1455177154))) (.branch 43 (.branch 42 (.leaf 1417352223) (.leaf 1380700212)) (.branch 44 (.leaf 1345176146) (.leaf 1310737130))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1277342246) (.branch 47 (.leaf 1244952444) (.leaf 1213530446))) (.branch 50 (.branch 49 (.leaf 1183040648) (.leaf 1153449040)) (.branch 51 (.leaf 1124723119) (.leaf 1096831811)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1069745401) (.leaf 1043435463)) (.branch 55 (.leaf 1017874793) (.leaf 993037351))) (.branch 58 (.branch 57 (.leaf 968898201) (.leaf 945433457)) (.branch 59 (.leaf 922620230) (.leaf 900436581))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 878861476) (.branch 62 (.leaf 857874738) (.leaf 837457010))) (.branch 65 (.branch 64 (.leaf 817589714) (.leaf 798255014)) (.branch 66 (.leaf 779435781) (.leaf 761115562)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 743278546) (.leaf 725909533)) (.branch 70 (.leaf 708993912) (.leaf 692517626))) (.branch 73 (.branch 72 (.leaf 676467155) (.leaf 660829485)) (.branch 74 (.leaf 645592089) (.leaf 630742903))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 616270310) (.branch 77 (.leaf 602163113) (.leaf 588410523))) (.branch 80 (.branch 79 (.leaf 575002140) (.leaf 561927934)) (.branch 81 (.leaf 549178230) (.leaf 536743694)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 524615317) (.leaf 512784403)) (.branch 85 (.leaf 501242556) (.leaf 489981663))) (.branch 88 (.branch 87 (.leaf 478993890) (.leaf 468271664)) (.branch 89 (.leaf 457807666) (.leaf 447594819)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 437626279) (.branch 92 (.leaf 427895427) (.leaf 418395855))) (.branch 95 (.branch 94 (.leaf 409121366) (.leaf 400065957)) (.branch 96 (.leaf 391223819) (.leaf 382589324)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 374157021) (.leaf 365921628)) (.branch 100 (.leaf 357878028) (.leaf 350021257))) (.branch 103 (.branch 102 (.leaf 342346506) (.leaf 334849110)) (.branch 104 (.leaf 327524544) (.leaf 320368418))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 313376474) (.leaf 306544577)) (.branch 108 (.leaf 299868715) (.leaf 293344992))) (.branch 111 (.branch 110 (.leaf 286969624) (.leaf 280738937)) (.branch 112 (.leaf 274649361) (.leaf 268697429)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 262879769) (.leaf 257193106)) (.branch 116 (.leaf 251634255) (.leaf 246200121))) (.branch 119 (.branch 118 (.leaf 240887692) (.leaf 235694041)) (.branch 120 (.leaf 230616319) (.leaf 225651756)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 340).prefactor = (299171578293797/62500000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 340).cutoff/(generalMeanRows 340).c)).2 =
    (181363326649651/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 340).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 340).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 340).q*(generalMeanRows 340).c/2-2 = (419/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable106.value]
    have hcontinuation : (generalMeanRows 340).q*(generalMeanRows 340).cutoff/2-2 = (1054/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable144.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 340).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 340

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 340).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 340).criticalRate j.val*(generalMeanRows 340).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 340).c*(generalMeanRows 340).criticalPoint j.val)).2-
      (generalMeanRows 340).J/2-(generalMeanRows 340).error (generalMeanGrid j.val)+
      (generalMeanRows 340).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 340).c)).2-
      (generalMeanRows 340).J/2-(generalMeanRows 340).error 4 := by
  have he : (generalMeanRows 340).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 340) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 340)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0340

/-! Kernel-checked entropy margins for general spectral rectangle 341. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0341
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4795339682) (.branch 2 (.leaf 4621359018) (.leaf 4455352537))) (.branch 5 (.branch 4 (.leaf 4296864423) (.leaf 4145470962)) (.branch 6 (.leaf 4000777745) (.leaf 3862417169)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3730046210) (.leaf 3603344410)) (.branch 10 (.leaf 3482012080) (.leaf 3365768667))) (.branch 13 (.branch 12 (.leaf 3254351284) (.leaf 3147513374)) (.branch 14 (.leaf 3045023496) (.leaf 2946664220))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2852231122) (.branch 17 (.leaf 2761531859) (.leaf 2674385328))) (.branch 20 (.branch 19 (.leaf 2590620894) (.leaf 2510077676)) (.branch 21 (.leaf 2432603896) (.leaf 2358056276)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2286299483) (.leaf 2217205618)) (.branch 25 (.leaf 2150653739) (.leaf 2086529421))) (.branch 28 (.branch 27 (.leaf 2024724354) (.leaf 1965135960)) (.branch 29 (.leaf 1907667045) (.leaf 1852225473)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1798723863) (.branch 32 (.leaf 1747079304) (.leaf 1697213093))) (.branch 35 (.branch 34 (.leaf 1649050491) (.leaf 1602520491)) (.branch 36 (.leaf 1557555607) (.leaf 1514091669)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1472067639) (.leaf 1431425436)) (.branch 40 (.leaf 1392109769) (.leaf 1354067985))) (.branch 43 (.branch 42 (.leaf 1317249924) (.leaf 1281607782)) (.branch 44 (.leaf 1247095986) (.leaf 1213671074))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1181291582) (.branch 47 (.leaf 1149917936) (.leaf 1119512358))) (.branch 50 (.branch 49 (.leaf 1090038768) (.leaf 1061462697)) (.branch 51 (.leaf 1033751205) (.leaf 1006872802)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 980797374) (.leaf 955496113)) (.branch 55 (.leaf 930941454) (.leaf 907107010))) (.branch 58 (.branch 57 (.leaf 883967516) (.leaf 861498771)) (.branch 59 (.leaf 839677588) (.leaf 818481744))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 797889934) (.branch 62 (.leaf 777881725) (.leaf 758437516))) (.branch 65 (.branch 64 (.leaf 739538500) (.leaf 721166621)) (.branch 66 (.leaf 703304545) (.leaf 685935622)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 669043857) (.leaf 652613879)) (.branch 70 (.leaf 636630910) (.leaf 621080743))) (.branch 73 (.branch 72 (.leaf 605949711) (.leaf 591224666)) (.branch 74 (.leaf 576892956) (.leaf 562942398))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 549361265) (.branch 77 (.leaf 536138261) (.leaf 523262501))) (.branch 80 (.branch 79 (.leaf 510723499) (.leaf 498511145)) (.branch 81 (.leaf 486615692) (.leaf 475027739)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 463738218) (.leaf 452738378)) (.branch 85 (.leaf 442019773) (.leaf 431574252))) (.branch 88 (.branch 87 (.leaf 421393940) (.leaf 411471234)) (.branch 89 (.leaf 401798786) (.leaf 392369498)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 383176508) (.branch 92 (.leaf 374213181) (.leaf 365473105))) (.branch 95 (.branch 94 (.leaf 356950073) (.leaf 348638083)) (.branch 96 (.leaf 340531327) (.leaf 332624184)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 324911211) (.leaf 317387140)) (.branch 100 (.leaf 310046867) (.leaf 302885450))) (.branch 103 (.branch 102 (.leaf 295898099) (.leaf 289080173)) (.branch 104 (.leaf 282427174) (.leaf 275934742))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 269598648) (.leaf 263414793)) (.branch 108 (.leaf 257379200) (.leaf 251488010))) (.branch 111 (.branch 110 (.leaf 245737479) (.leaf 240123975)) (.branch 112 (.leaf 234643971) (.leaf 229294043)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 224070868) (.leaf 218971217)) (.branch 116 (.leaf 213991955) (.leaf 209130036))) (.branch 119 (.branch 118 (.leaf 204382502) (.leaf 199746477)) (.branch 120 (.leaf 195219167) (.leaf 190797855)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 341).prefactor = (4821121582818683/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 341).cutoff/(generalMeanRows 341).c)).2 =
    (347341734459821/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 341).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 341).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 341).q*(generalMeanRows 341).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 341).q*(generalMeanRows 341).cutoff/2-2 = (1054/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable144.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 341).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 341

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 341).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 341).criticalRate j.val*(generalMeanRows 341).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 341).c*(generalMeanRows 341).criticalPoint j.val)).2-
      (generalMeanRows 341).J/2-(generalMeanRows 341).error (generalMeanGrid j.val)+
      (generalMeanRows 341).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 341).c)).2-
      (generalMeanRows 341).J/2-(generalMeanRows 341).error 4 := by
  have he : (generalMeanRows 341).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 341) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 341)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0341

/-! Kernel-checked entropy margins for general spectral rectangle 342. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0342
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5287693129) (.branch 2 (.leaf 5121874193) (.leaf 4963412307))) (.branch 5 (.branch 4 (.leaf 4811880559) (.leaf 4666882526)) (.branch 6 (.leaf 4528049609) (.leaf 4395038656)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4267529839) (.leaf 4145224735)) (.branch 10 (.leaf 4027844612) (.leaf 3915128871))) (.branch 13 (.branch 12 (.leaf 3806833644) (.leaf 3702730518)) (.branch 14 (.leaf 3602605378) (.leaf 3506257349))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3413497837) (.branch 17 (.leaf 3324149650) (.leaf 3238046189))) (.branch 20 (.branch 19 (.leaf 3155030713) (.leaf 3074955657)) (.branch 21 (.leaf 2997682014) (.leaf 2923078755)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2851022303) (.leaf 2781396041)) (.branch 25 (.leaf 2714089860) (.leaf 2648999745))) (.branch 28 (.branch 27 (.leaf 2586027381) (.leaf 2525079797)) (.branch 29 (.leaf 2466069032) (.leaf 2408911825)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2353529325) (.branch 32 (.leaf 2299846826) (.leaf 2247793513))) (.branch 35 (.branch 34 (.leaf 2197302234) (.leaf 2148309276)) (.branch 36 (.leaf 2100754170) (.leaf 2054579496)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2009730707) (.leaf 1966155965)) (.branch 40 (.leaf 1923805986) (.leaf 1882633892))) (.branch 43 (.branch 42 (.leaf 1842595079) (.leaf 1803647087)) (.branch 44 (.leaf 1765749482) (.leaf 1728863743))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1692953157) (.branch 47 (.leaf 1657982721) (.leaf 1623919048))) (.branch 50 (.branch 49 (.leaf 1590730281) (.leaf 1558386010)) (.branch 51 (.leaf 1526857196) (.leaf 1496116096)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1466136199) (.leaf 1436892157)) (.branch 55 (.leaf 1408359729) (.leaf 1380515717))) (.branch 58 (.branch 57 (.leaf 1353337922) (.leaf 1326805084)) (.branch 59 (.leaf 1300896839) (.leaf 1275593674))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1250876881) (.branch 62 (.leaf 1226728520) (.leaf 1203131382))) (.branch 65 (.branch 64 (.leaf 1180068947) (.leaf 1157525356)) (.branch 66 (.leaf 1135485379) (.leaf 1113934379)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1092858291) (.leaf 1072243586)) (.branch 70 (.leaf 1052077255) (.leaf 1032346778))) (.branch 73 (.branch 72 (.leaf 1013040102) (.leaf 994145622)) (.branch 74 (.leaf 975652157) (.leaf 957548933))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 939825564) (.branch 77 (.leaf 922472032) (.leaf 905478674))) (.branch 80 (.branch 79 (.leaf 888836165) (.leaf 872535500)) (.branch 81 (.leaf 856567984) (.leaf 840925218)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 825599084) (.leaf 810581732)) (.branch 85 (.leaf 795865574) (.leaf 781443267))) (.branch 88 (.branch 87 (.leaf 767307705) (.leaf 753452009)) (.branch 89 (.leaf 739869520) (.leaf 726553784)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 713498551) (.branch 92 (.leaf 700697759) (.leaf 688145534))) (.branch 95 (.branch 94 (.leaf 675836177) (.leaf 663764159)) (.branch 96 (.leaf 651924115) (.leaf 640310837)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 628919267) (.leaf 617744494)) (.branch 100 (.leaf 606781744) (.leaf 596026380))) (.branch 103 (.branch 102 (.leaf 585473893) (.leaf 575119899)) (.branch 104 (.leaf 564960135) (.leaf 554990450))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 545206810) (.leaf 535605286)) (.branch 108 (.leaf 526182051) (.leaf 516933380))) (.branch 111 (.branch 110 (.leaf 507855647) (.leaf 498945315)) (.branch 112 (.leaf 490198939) (.leaf 481613163)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 473184713) (.leaf 464910397)) (.branch 116 (.leaf 456787102) (.leaf 448811792))) (.branch 119 (.branch 118 (.leaf 440981502) (.leaf 433293343)) (.branch 120 (.leaf 425744492) (.leaf 418332193)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 342).prefactor = (4562307452797047/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 342).cutoff/(generalMeanRows 342).c)).2 =
    (434893234047819/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 342).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 342).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 342).q*(generalMeanRows 342).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 342).q*(generalMeanRows 342).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 342).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 342

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 342).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 342).criticalRate j.val*(generalMeanRows 342).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 342).c*(generalMeanRows 342).criticalPoint j.val)).2-
      (generalMeanRows 342).J/2-(generalMeanRows 342).error (generalMeanGrid j.val)+
      (generalMeanRows 342).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 342).c)).2-
      (generalMeanRows 342).J/2-(generalMeanRows 342).error 4 := by
  have he : (generalMeanRows 342).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 342) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 342)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0342

/-! Kernel-checked entropy margins for general spectral rectangle 343. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0343
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5323812260) (.branch 2 (.leaf 5156860650) (.leaf 4997316344))) (.branch 5 (.branch 4 (.leaf 4844749514) (.leaf 4698761030)) (.branch 6 (.leaf 4558979773) (.leaf 4425060251)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4296680447) (.leaf 4173539903)) (.branch 10 (.leaf 4055357980) (.leaf 3941872301))) (.branch 13 (.branch 12 (.leaf 3832837332) (.leaf 3728023100)) (.branch 14 (.leaf 3627214026) (.leaf 3530207863))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3436814731) (.branch 17 (.leaf 3346856225) (.leaf 3260164609))) (.branch 20 (.branch 19 (.leaf 3176582071) (.leaf 3095960039)) (.branch 21 (.leaf 3018158556) (.leaf 2943045698)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2870497043) (.leaf 2800395178)) (.branch 25 (.leaf 2732629243) (.leaf 2667094511))) (.branch 28 (.branch 27 (.leaf 2603691996) (.leaf 2542328092)) (.branch 29 (.leaf 2482914237) (.leaf 2425366600)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2369605794) (.branch 32 (.leaf 2315556601) (.leaf 2263147723))) (.branch 35 (.branch 34 (.leaf 2212311548) (.leaf 2162983930)) (.branch 36 (.leaf 2115103985) (.leaf 2068613901)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2023458759) (.leaf 1979586367)) (.branch 40 (.leaf 1936947104) (.leaf 1895493772))) (.branch 43 (.branch 42 (.leaf 1855181462) (.leaf 1815967425)) (.branch 44 (.leaf 1777810950) (.leaf 1740673252))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1704517368) (.branch 47 (.leaf 1669308056) (.leaf 1635011701))) (.branch 50 (.branch 49 (.leaf 1601596229) (.leaf 1569031021)) (.branch 51 (.leaf 1537286839) (.leaf 1506335754)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1476151070) (.leaf 1446707269)) (.branch 55 (.leaf 1417979941) (.leaf 1389945733))) (.branch 58 (.branch 57 (.leaf 1362582292) (.leaf 1335868213)) (.branch 59 (.leaf 1309782995) (.leaf 1284306989))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1259421360) (.branch 62 (.leaf 1235108048) (.leaf 1211349722))) (.branch 65 (.branch 64 (.leaf 1188129752) (.leaf 1165432171)) (.branch 66 (.leaf 1143241643) (.leaf 1121543433)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1100323378) (.leaf 1079567859)) (.branch 70 (.leaf 1059263776) (.leaf 1039398524))) (.branch 73 (.branch 72 (.leaf 1019959968) (.leaf 1000936424)) (.branch 74 (.leaf 982316634) (.leaf 964089751))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 946245317) (.branch 77 (.leaf 928773247) (.leaf 911663811))) (.branch 80 (.branch 79 (.leaf 894907620) (.leaf 878495608)) (.branch 81 (.leaf 862419022) (.leaf 846669404)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 831238579) (.leaf 816118648)) (.branch 85 (.leaf 801301966) (.leaf 786781143))) (.branch 88 (.branch 87 (.leaf 772549024) (.leaf 758598683)) (.branch 89 (.leaf 744923414) (.leaf 731516722)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 718372311) (.branch 92 (.leaf 705484080) (.leaf 692846113))) (.branch 95 (.branch 94 (.leaf 680452673) (.leaf 668298194)) (.branch 96 (.leaf 656377273) (.leaf 644684667)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 633215284) (.leaf 621964178)) (.branch 100 (.leaf 610926544) (.leaf 600097713))) (.branch 103 (.branch 102 (.leaf 589473144) (.leaf 579048424)) (.branch 104 (.leaf 568819260) (.leaf 558781475))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 548931005) (.leaf 539263894)) (.branch 108 (.leaf 529776291) (.leaf 520464445))) (.branch 111 (.branch 110 (.leaf 511324703) (.leaf 502353506)) (.branch 112 (.leaf 493547386) (.leaf 484902963)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 476416939) (.leaf 468086103)) (.branch 116 (.leaf 459907320) (.leaf 451877531))) (.branch 119 (.branch 118 (.leaf 443993755) (.leaf 436253080)) (.branch 120 (.leaf 428652664) (.leaf 421189733)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 343).prefactor = (2296735812928113/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 343).cutoff/(generalMeanRows 343).c)).2 =
    (434893234047819/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 343).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 343).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 343).q*(generalMeanRows 343).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 343).q*(generalMeanRows 343).cutoff/2-2 = (4174/1955:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable146.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 343).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 343

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 343).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 343).criticalRate j.val*(generalMeanRows 343).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 343).c*(generalMeanRows 343).criticalPoint j.val)).2-
      (generalMeanRows 343).J/2-(generalMeanRows 343).error (generalMeanGrid j.val)+
      (generalMeanRows 343).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 343).c)).2-
      (generalMeanRows 343).J/2-(generalMeanRows 343).error 4 := by
  have he : (generalMeanRows 343).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 343) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 343)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0343

/-! Kernel-checked entropy margins for general spectral rectangle 344. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0344
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4855699949) (.branch 2 (.leaf 4681755966) (.leaf 4515767628))) (.branch 5 (.branch 4 (.leaf 4357278993) (.leaf 4205866295)) (.branch 6 (.leaf 4061135147) (.leaf 3922718034)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3790272076) (.leaf 3663477011)) (.branch 10 (.leaf 3542033395) (.leaf 3425660958))) (.branch 13 (.branch 12 (.leaf 3314097133) (.leaf 3207095716)) (.branch 14 (.leaf 3104425644) (.leaf 3005869893))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2911224462) (.branch 17 (.leaf 2820297449) (.leaf 2732908208))) (.branch 20 (.branch 19 (.leaf 2648886570) (.leaf 2568072132)) (.branch 21 (.leaf 2490313599) (.leaf 2415468182)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2343401041) (.leaf 2273984770)) (.branch 25 (.leaf 2207098921) (.leaf 2142629561))) (.branch 28 (.branch 27 (.leaf 2080468870) (.leaf 2020514757)) (.branch 29 (.leaf 1962670510) (.leaf 1906844470)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1852949723) (.branch 32 (.leaf 1800903824) (.leaf 1750628525))) (.branch 35 (.branch 34 (.leaf 1702049534) (.leaf 1655096284)) (.branch 36 (.leaf 1609701718) (.leaf 1565802088)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1523336768) (.leaf 1482248076)) (.branch 40 (.leaf 1442481115) (.leaf 1403983613))) (.branch 43 (.branch 42 (.leaf 1366705781) (.leaf 1330600177)) (.branch 44 (.leaf 1295621579) (.leaf 1261726865))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1228874901) (.branch 47 (.leaf 1197026434) (.leaf 1166143995))) (.branch 50 (.branch 49 (.leaf 1136191805) (.leaf 1107135684)) (.branch 51 (.leaf 1078942971) (.leaf 1051582448)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1025024260) (.leaf 999239851)) (.branch 55 (.leaf 974201897) (.leaf 949884245))) (.branch 58 (.branch 57 (.leaf 926261851) (.leaf 903310731)) (.branch 59 (.leaf 881007902) (.leaf 859331341))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 838259930) (.branch 62 (.leaf 817773419) (.leaf 797852381))) (.branch 65 (.branch 64 (.leaf 778478171) (.leaf 759632895)) (.branch 66 (.leaf 741299368) (.leaf 723461085)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 706102187) (.leaf 689207433)) (.branch 70 (.leaf 672762169) (.leaf 656752305))) (.branch 73 (.branch 72 (.leaf 641164285) (.leaf 625985068)) (.branch 74 (.leaf 611202097) (.leaf 596803287))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 582776998) (.branch 77 (.leaf 569112016) (.leaf 555797536))) (.branch 80 (.branch 79 (.leaf 542823142) (.leaf 530178795)) (.branch 81 (.leaf 517854809) (.leaf 505841845)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 494130888) (.leaf 482713238)) (.branch 85 (.leaf 471580497) (.leaf 460724555))) (.branch 88 (.branch 87 (.leaf 450137578) (.leaf 439811997)) (.branch 89 (.leaf 429740497) (.leaf 419916010)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 410331697) (.branch 92 (.leaf 400980949) (.leaf 391857370))) (.branch 95 (.branch 94 (.leaf 382954773) (.leaf 374267168)) (.branch 96 (.leaf 365788761) (.leaf 357513937)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 349437262) (.leaf 341553472)) (.branch 100 (.leaf 333857464) (.leaf 326344297))) (.branch 103 (.branch 102 (.leaf 319009179) (.leaf 311847466)) (.branch 104 (.leaf 304854653) (.leaf 298026373))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 291358389) (.leaf 284846590)) (.branch 108 (.leaf 278486987) (.leaf 272275708))) (.branch 111 (.branch 110 (.leaf 266208995) (.leaf 260283197)) (.branch 112 (.leaf 254494772) (.leaf 248840276)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 243316366) (.leaf 237919794)) (.branch 116 (.leaf 232647402) (.leaf 227496122))) (.branch 119 (.branch 118 (.leaf 222462971) (.leaf 217545049)) (.branch 120 (.leaf 212739536) (.leaf 208043691)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 344).prefactor = (2409832865818903/500000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 344).cutoff/(generalMeanRows 344).c)).2 =
    (357967572336047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 344).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 344).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 344).q*(generalMeanRows 344).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 344).q*(generalMeanRows 344).cutoff/2-2 = (2114/1011:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable147.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 344).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 344

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 344).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 344).criticalRate j.val*(generalMeanRows 344).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 344).c*(generalMeanRows 344).criticalPoint j.val)).2-
      (generalMeanRows 344).J/2-(generalMeanRows 344).error (generalMeanGrid j.val)+
      (generalMeanRows 344).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 344).c)).2-
      (generalMeanRows 344).J/2-(generalMeanRows 344).error 4 := by
  have he : (generalMeanRows 344).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 344) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 344)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0344

/-! Kernel-checked entropy margins for general spectral rectangle 345. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0345
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4872962207) (.branch 2 (.leaf 4698399844) (.leaf 4531821410))) (.branch 5 (.branch 4 (.leaf 4372769340) (.leaf 4220818362)) (.branch 6 (.leaf 4075572687) (.leaf 3936663495)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3803746684) (.leaf 3676500857)) (.branch 10 (.leaf 3554625503) (.leaf 3437839356))) (.branch 13 (.branch 12 (.leaf 3325878916) (.leaf 3218497103)) (.branch 14 (.leaf 3115462034) (.leaf 3016555913))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2921574012) (.branch 17 (.leaf 2830323749) (.leaf 2742623835))) (.branch 20 (.branch 19 (.leaf 2658303496) (.leaf 2577201758)) (.branch 21 (.leaf 2499166789) (.leaf 2424055293)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2351731950) (.leaf 2282068901)) (.branch 25 (.leaf 2214945269) (.leaf 2150246717))) (.branch 28 (.branch 27 (.leaf 2087865042) (.leaf 2027697789)) (.branch 29 (.leaf 1969647903) (.leaf 1913623398)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1859537053) (.branch 32 (.leaf 1807306128) (.leaf 1756852097))) (.branch 35 (.branch 34 (.leaf 1708100406) (.leaf 1660980235)) (.branch 36 (.leaf 1615424289) (.leaf 1571368594)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1528752307) (.leaf 1487517543)) (.branch 40 (.leaf 1447609209) (.leaf 1408974846))) (.branch 43 (.branch 42 (.leaf 1371564489) (.leaf 1335330528)) (.branch 44 (.leaf 1300227579) (.leaf 1266212368))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1233243613) (.branch 47 (.leaf 1201281923) (.leaf 1170289696))) (.branch 50 (.branch 49 (.leaf 1140231024) (.leaf 1111071607)) (.branch 51 (.leaf 1082778668) (.leaf 1055320876)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1028668273) (.leaf 1002792199)) (.branch 55 (.leaf 977665234) (.leaf 953261131))) (.branch 58 (.branch 57 (.leaf 929554759) (.leaf 906522046)) (.branch 59 (.leaf 884139930) (.leaf 862386307))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 841239987) (.branch 62 (.leaf 820680645) (.leaf 800688786))) (.branch 65 (.branch 64 (.leaf 781245700) (.leaf 762333428)) (.branch 66 (.leaf 743934725) (.leaf 726033026)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 708612416) (.leaf 691657600)) (.branch 70 (.leaf 675153872) (.leaf 659087093))) (.branch 73 (.branch 72 (.leaf 643443657) (.leaf 628210476)) (.branch 74 (.leaf 613374951) (.leaf 598924953))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 584848800) (.branch 77 (.leaf 571135238) (.leaf 557773424))) (.branch 80 (.branch 79 (.leaf 544752906) (.leaf 532063607)) (.branch 81 (.leaf 519695809) (.leaf 507640138)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 495887548) (.leaf 484429308)) (.branch 85 (.leaf 473256990) (.leaf 462362454))) (.branch 88 (.branch 87 (.leaf 451737840) (.leaf 441375551)) (.branch 89 (.leaf 431268247) (.leaf 421408832)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 411790447) (.branch 92 (.leaf 402406457) (.leaf 393250443))) (.branch 95 (.branch 94 (.leaf 384316196) (.leaf 375597707)) (.branch 96 (.leaf 367089158) (.leaf 358784917)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 350679529) (.leaf 342767711)) (.branch 100 (.leaf 335044344) (.leaf 327504467))) (.branch 103 (.branch 102 (.leaf 320143273) (.leaf 312956099)) (.branch 104 (.leaf 305938427) (.leaf 299085872))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 292394183) (.leaf 285859234)) (.branch 108 (.leaf 279477023) (.leaf 273243662))) (.branch 111 (.branch 110 (.leaf 267155381) (.leaf 261208517)) (.branch 112 (.leaf 255399513) (.leaf 249724916)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 244181368) (.leaf 238765611)) (.branch 116 (.leaf 233474475) (.leaf 228304882))) (.branch 119 (.branch 118 (.leaf 223253838) (.leaf 218318432)) (.branch 120 (.leaf 213495836) (.leaf 208783297)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 345).prefactor = (38694399094007/8000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 345).cutoff/(generalMeanRows 345).c)).2 =
    (357967572336047/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 345).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 345).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 345).q*(generalMeanRows 345).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 345).q*(generalMeanRows 345).cutoff/2-2 = (2114/1011:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable147.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 345).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 345

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 345).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 345).criticalRate j.val*(generalMeanRows 345).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 345).c*(generalMeanRows 345).criticalPoint j.val)).2-
      (generalMeanRows 345).J/2-(generalMeanRows 345).error (generalMeanGrid j.val)+
      (generalMeanRows 345).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 345).c)).2-
      (generalMeanRows 345).J/2-(generalMeanRows 345).error 4 := by
  have he : (generalMeanRows 345).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 345) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 345)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0345

/-! Kernel-checked entropy margins for general spectral rectangle 346. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0346
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4812527903) (.branch 2 (.leaf 4637923630) (.leaf 4471322122))) (.branch 5 (.branch 4 (.leaf 4312265930) (.leaf 4160329820)) (.branch 6 (.leaf 4015117970) (.leaf 3876261461)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3743416036) (.leaf 3616260092)) (.branch 10 (.leaf 3494492863) (.leaf 3377832792))) (.branch 13 (.branch 12 (.leaf 3266016049) (.leaf 3158795194)) (.branch 14 (.leaf 3055937955) (.leaf 2957226124))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2862454544) (.branch 17 (.leaf 2771430182) (.leaf 2683971287))) (.branch 20 (.branch 19 (.leaf 2599906611) (.leaf 2519074697)) (.branch 21 (.leaf 2441323223) (.leaf 2366508397)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2294494402) (.leaf 2225152880)) (.branch 25 (.leaf 2158362455) (.leaf 2094008293))) (.branch 28 (.branch 27 (.leaf 2031981694) (.leaf 1972179714)) (.branch 29 (.leaf 1914504810) (.leaf 1858864515)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1805171136) (.branch 32 (.leaf 1753341464) (.leaf 1703296515))) (.branch 35 (.branch 34 (.leaf 1654961281) (.leaf 1608264501)) (.branch 36 (.leaf 1563138446) (.leaf 1519518718)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1477344059) (.leaf 1436556179)) (.branch 40 (.leaf 1397099591) (.leaf 1358921452))) (.branch 43 (.branch 42 (.leaf 1321971421) (.leaf 1286201525)) (.branch 44 (.leaf 1251566026) (.leaf 1218021308))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1185525755) (.branch 47 (.leaf 1154039655) (.leaf 1123525093))) (.branch 50 (.branch 49 (.leaf 1093945859) (.leaf 1065267361)) (.branch 51 (.leaf 1037456541) (.leaf 1010481796)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 984312904) (.leaf 958920955)) (.branch 55 (.leaf 934278283) (.leaf 910358408))) (.branch 58 (.branch 57 (.leaf 887135974) (.leaf 864586692)) (.branch 59 (.leaf 842687294) (.leaf 821415477))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 800749858) (.branch 62 (.leaf 780669933) (.leaf 761156029))) (.branch 65 (.branch 64 (.leaf 742189272) (.leaf 723751541)) (.branch 66 (.leaf 705825441) (.leaf 688394262)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 671441951) (.leaf 654953081)) (.branch 70 (.leaf 638912824) (.leaf 623306920))) (.branch 73 (.branch 72 (.leaf 608121653) (.leaf 593343828)) (.branch 74 (.leaf 578960747) (.leaf 564960186))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 551330373) (.branch 77 (.leaf 538059973) (.leaf 525138062))) (.branch 80 (.branch 79 (.leaf 512554116) (.leaf 500297989)) (.branch 81 (.leaf 488359898) (.leaf 476730409)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 465400422) (.leaf 454361155)) (.branch 85 (.leaf 443604131) (.leaf 433121169))) (.branch 88 (.branch 87 (.leaf 422904367) (.leaf 412946094)) (.branch 89 (.leaf 403238977) (.leaf 393775891)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 384549950) (.branch 92 (.leaf 375554496) (.leaf 366783092))) (.branch 95 (.branch 94 (.leaf 358229510) (.leaf 349887727)) (.branch 96 (.leaf 341751914) (.leaf 333816429)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 326075810) (.leaf 318524770)) (.branch 100 (.leaf 311158187) (.leaf 303971100))) (.branch 103 (.branch 102 (.leaf 296958704) (.leaf 290116340)) (.branch 104 (.leaf 283439494) (.leaf 276923791))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 270564987) (.leaf 264358967)) (.branch 108 (.leaf 258301740) (.leaf 252389433))) (.branch 111 (.branch 110 (.leaf 246618291) (.leaf 240984666)) (.branch 112 (.leaf 235485019) (.leaf 230115915)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 224874018) (.leaf 219756088)) (.branch 116 (.leaf 214758979) (.leaf 209879634))) (.branch 119 (.branch 118 (.leaf 205115083) (.leaf 200462441)) (.branch 120 (.leaf 195918903) (.leaf 191481743)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 346).prefactor = (4838402215830117/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 346).cutoff/(generalMeanRows 346).c)).2 =
    (347341734459821/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 346).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 346).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 346).q*(generalMeanRows 346).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 346).q*(generalMeanRows 346).cutoff/2-2 = (1054/507:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable144.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 346).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 346

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 346).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 346).criticalRate j.val*(generalMeanRows 346).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 346).c*(generalMeanRows 346).criticalPoint j.val)).2-
      (generalMeanRows 346).J/2-(generalMeanRows 346).error (generalMeanGrid j.val)+
      (generalMeanRows 346).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 346).c)).2-
      (generalMeanRows 346).J/2-(generalMeanRows 346).error 4 := by
  have he : (generalMeanRows 346).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 346) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 346)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0346

/-! Kernel-checked entropy margins for general spectral rectangle 347. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0347
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 5287128864) (.branch 2 (.leaf 5121364210) (.leaf 4962981937))) (.branch 5 (.branch 4 (.leaf 4811551560) (.leaf 4666673427)) (.branch 6 (.leaf 4527976031) (.leaf 4395113598)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 4267763940) (.leaf 4145626517)) (.branch 10 (.leaf 4028420695) (.leaf 3915884175))) (.branch 13 (.branch 12 (.leaf 3807771571) (.leaf 3703853114)) (.branch 14 (.leaf 3603913488) (.leaf 3507750753))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 3415175375) (.branch 17 (.leaf 3326009335) (.leaf 3240085312))) (.branch 20 (.branch 19 (.leaf 3157245935) (.leaf 3077343099)) (.branch 21 (.leaf 3000237328) (.leaf 2925797199)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2853898803) (.leaf 2784425246)) (.branch 25 (.leaf 2717266200) (.leaf 2652317470))) (.branch 28 (.branch 27 (.leaf 2589480609) (.leaf 2528662549)) (.branch 29 (.leaf 2469775266) (.leaf 2412735466)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 2357464294) (.branch 32 (.leaf 2303887061) (.leaf 2251932992))) (.branch 35 (.branch 34 (.leaf 2201534992) (.leaf 2152629426)) (.branch 36 (.leaf 2105155910) (.leaf 2059057127)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 2014278642) (.leaf 1970768739)) (.branch 40 (.leaf 1928478261) (.leaf 1887360466))) (.branch 43 (.branch 42 (.leaf 1847370892) (.leaf 1808467223)) (.branch 44 (.leaf 1770609172) (.leaf 1733758370))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1697878254) (.branch 47 (.leaf 1662933976) (.leaf 1628892302))) (.branch 50 (.branch 49 (.leaf 1595721528) (.leaf 1563391396)) (.branch 51 (.leaf 1531873017) (.leaf 1501138801)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1471162383) (.leaf 1441918561)) (.branch 55 (.leaf 1413383235) (.leaf 1385533351))) (.branch 58 (.branch 57 (.leaf 1358346846) (.leaf 1331802594)) (.branch 59 (.leaf 1305880365) (.leaf 1280560772))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 1255825233) (.branch 62 (.leaf 1231655931) (.leaf 1208035773))) (.branch 65 (.branch 64 (.leaf 1184948355) (.leaf 1162377930)) (.branch 66 (.leaf 1140309374) (.leaf 1118728156)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 1097620310) (.leaf 1076972407)) (.branch 70 (.leaf 1056771530) (.leaf 1037005250))) (.branch 73 (.branch 72 (.leaf 1017661602) (.leaf 998729064)) (.branch 74 (.leaf 980196538) (.leaf 962053326))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 944289116) (.branch 77 (.leaf 926893963) (.leaf 909858273))) (.branch 80 (.branch 79 (.leaf 893172784) (.leaf 876828558)) (.branch 81 (.leaf 860816958) (.leaf 845129643)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 829758549) (.leaf 814695881)) (.branch 85 (.leaf 799934099) (.leaf 785465908))) (.branch 88 (.branch 87 (.leaf 771284248) (.leaf 757382284)) (.branch 89 (.leaf 743753396) (.leaf 730391172)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 717289396) (.branch 92 (.leaf 704442044) (.leaf 691843273))) (.branch 95 (.branch 94 (.leaf 679487417) (.leaf 667368977)) (.branch 96 (.leaf 655482615) (.leaf 643823151)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 632385551) (.leaf 621164928)) (.branch 100 (.leaf 610156531) (.leaf 599355742))) (.branch 103 (.branch 102 (.leaf 588758073) (.leaf 578359158)) (.branch 104 (.leaf 568154750) (.leaf 558140717))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 548313037) (.leaf 538667795)) (.branch 108 (.leaf 529201178) (.leaf 519909473))) (.branch 111 (.branch 110 (.leaf 510789064) (.leaf 501836424)) (.branch 112 (.leaf 493048119) (.leaf 484420799)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 475951200) (.leaf 467636135)) (.branch 116 (.leaf 459472499) (.leaf 451457260))) (.branch 119 (.branch 118 (.leaf 443587460) (.leaf 435860213)) (.branch 120 (.leaf 428272700) (.leaf 420822169)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 347).prefactor = (918303164014133/200000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 347).cutoff/(generalMeanRows 347).c)).2 =
    (440792956175007/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 347).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 347).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 347).q*(generalMeanRows 347).c/2-2 = (2707/4000:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable126.value]
    have hcontinuation : (generalMeanRows 347).q*(generalMeanRows 347).cutoff/2-2 = (8394/3887:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable148.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 347).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 347

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 347).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 347).criticalRate j.val*(generalMeanRows 347).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 347).c*(generalMeanRows 347).criticalPoint j.val)).2-
      (generalMeanRows 347).J/2-(generalMeanRows 347).error (generalMeanGrid j.val)+
      (generalMeanRows 347).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 347).c)).2-
      (generalMeanRows 347).J/2-(generalMeanRows 347).error 4 := by
  have he : (generalMeanRows 347).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 347) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 347)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0347

/-! Kernel-checked entropy margins for general spectral rectangle 348. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0348
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4809341866) (.branch 2 (.leaf 4634758080) (.leaf 4468192333))) (.branch 5 (.branch 4 (.leaf 4309185228) (.leaf 4157309766)) (.branch 6 (.leaf 4012168522) (.leaf 3873391127)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3740632015) (.leaf 3613568396)) (.branch 10 (.leaf 3491898437) (.leaf 3375339616))) (.branch 13 (.branch 12 (.leaf 3263627238) (.leaf 3156513082)) (.branch 14 (.leaf 3053764182) (.leaf 2955161703))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2860499932) (.branch 17 (.leaf 2769585342) (.leaf 2682235742))) (.branch 20 (.branch 19 (.leaf 2598279497) (.leaf 2517554809)) (.branch 21 (.leaf 2439909057) (.leaf 2365198190)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2293286166) (.leaf 2224044435)) (.branch 25 (.leaf 2157351456) (.leaf 2093092259))) (.branch 28 (.branch 27 (.leaf 2031158032) (.leaf 1971445737)) (.branch 29 (.leaf 1913857761) (.leaf 1858301582)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1804689467) (.branch 32 (.leaf 1752938183) (.leaf 1702968735))) (.branch 35 (.branch 34 (.leaf 1654706114) (.leaf 1608079069)) (.branch 36 (.leaf 1563019890) (.leaf 1519464203)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1477350787) (.leaf 1436621390)) (.branch 40 (.leaf 1397220569) (.leaf 1359095531))) (.branch 43 (.branch 42 (.leaf 1322195991) (.leaf 1286474029)) (.branch 44 (.leaf 1251883971) (.leaf 1218382258))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1185927342) (.branch 47 (.leaf 1154479575) (.leaf 1124001106))) (.branch 50 (.branch 49 (.leaf 1094455796) (.leaf 1065809118)) (.branch 51 (.leaf 1038028082) (.leaf 1011081154)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 984938178) (.leaf 959570312)) (.branch 55 (.leaf 934949956) (.leaf 911050697))) (.branch 58 (.branch 57 (.leaf 887847241) (.leaf 865315366)) (.branch 59 (.leaf 843431864) (.leaf 822174494))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 801521935) (.branch 62 (.leaf 781453739) (.leaf 761950295))) (.branch 65 (.branch 64 (.leaf 742992780) (.leaf 724563132)) (.branch 66 (.leaf 706644007) (.leaf 689218746)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 672271349) (.leaf 655786437)) (.branch 70 (.leaf 639749227) (.leaf 624145507))) (.branch 73 (.branch 72 (.leaf 608961605) (.leaf 594184369)) (.branch 74 (.leaf 579801142) (.leaf 565799740))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 552168430) (.branch 77 (.leaf 538895913) (.leaf 525971302))) (.branch 80 (.branch 79 (.leaf 513384107) (.leaf 501124216)) (.branch 81 (.leaf 489181876) (.leaf 477547686)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 466212574) (.leaf 455167785)) (.branch 85 (.leaf 444404872) (.leaf 433915678))) (.branch 88 (.branch 87 (.leaf 423692325) (.leaf 413727208)) (.branch 89 (.leaf 404012974) (.leaf 394542522)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 385308985) (.branch 92 (.leaf 376305727) (.leaf 367526327))) (.branch 95 (.branch 94 (.leaf 358964577) (.leaf 350614470)) (.branch 96 (.leaf 342470194) (.leaf 334526123)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 326776808) (.leaf 319216977)) (.branch 100 (.leaf 311841522) (.leaf 304645494))) (.branch 103 (.branch 102 (.leaf 297624098) (.leaf 290772689)) (.branch 104 (.leaf 284086764) (.leaf 277561955))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 271194030) (.leaf 264978882)) (.branch 108 (.leaf 258912529) (.leaf 252991107))) (.branch 111 (.branch 110 (.leaf 247210866) (.leaf 241568166)) (.branch 112 (.leaf 236059477) (.leaf 230681367)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 225430507) (.leaf 220303662)) (.branch 116 (.leaf 215297692) (.leaf 210409544))) (.branch 119 (.branch 118 (.leaf 205636253) (.leaf 200974937)) (.branch 120 (.leaf 196422796) (.leaf 191977107)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 348).prefactor = (4853994954650803/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 348).cutoff/(generalMeanRows 348).c)).2 =
    (175152349795239/500000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 348).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 348).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 348).q*(generalMeanRows 348).c/2-2 = (441/500:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable108.value]
    have hcontinuation : (generalMeanRows 348).q*(generalMeanRows 348).cutoff/2-2 = (2114/1011:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable147.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 348).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 348

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 348).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 348).criticalRate j.val*(generalMeanRows 348).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 348).c*(generalMeanRows 348).criticalPoint j.val)).2-
      (generalMeanRows 348).J/2-(generalMeanRows 348).error (generalMeanGrid j.val)+
      (generalMeanRows 348).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 348).c)).2-
      (generalMeanRows 348).J/2-(generalMeanRows 348).error 4 := by
  have he : (generalMeanRows 348).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 348) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 348)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0348

/-! Kernel-checked entropy margins for general spectral rectangle 349. -/
namespace SingularValueBounds.KL.Certificates.EntropyRow0349
open SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private noncomputable def errorNumerators (j : Fin 121) : ℤ :=
  ((.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf 4880044749) (.branch 2 (.leaf 4705187179) (.leaf 4538335098))) (.branch 5 (.branch 4 (.leaf 4379029164) (.leaf 4226842475)) (.branch 6 (.leaf 4081377747) (.leaf 3942264788)))) (.branch 11 (.branch 9 (.branch 8 (.leaf 3809158237) (.leaf 3681735542)) (.branch 10 (.leaf 3559695131) (.leaf 3442754766))) (.branch 13 (.branch 12 (.leaf 3330650054) (.leaf 3223133092)) (.branch 14 (.leaf 3119971245) (.leaf 3020946025))))) (.branch 22 (.branch 18 (.branch 16 (.leaf 2925852070) (.branch 17 (.leaf 2834496214) (.leaf 2746696634))) (.branch 20 (.branch 19 (.leaf 2662282065) (.leaf 2581091083)) (.branch 21 (.leaf 2502971443) (.leaf 2427779470)))) (.branch 26 (.branch 24 (.branch 23 (.leaf 2355379498) (.leaf 2285643349)) (.branch 25 (.leaf 2218449855) (.leaf 2153684415))) (.branch 28 (.branch 27 (.leaf 2091238579) (.leaf 2031009670)) (.branch 29 (.leaf 1972900430) (.leaf 1916818685)))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf 1862677046) (.branch 32 (.leaf 1810392616) (.leaf 1759886729))) (.branch 35 (.branch 34 (.leaf 1711084700) (.leaf 1663915594)) (.branch 36 (.leaf 1618312008) (.leaf 1574209871)))) (.branch 41 (.branch 39 (.branch 38 (.leaf 1531548252) (.leaf 1490269186)) (.branch 40 (.leaf 1450317506) (.leaf 1411640690))) (.branch 43 (.branch 42 (.leaf 1374188713) (.leaf 1337913910)) (.branch 44 (.leaf 1302770849) (.leaf 1268716212))))) (.branch 52 (.branch 48 (.branch 46 (.leaf 1235708679) (.branch 47 (.leaf 1203708824) (.leaf 1172679011))) (.branch 50 (.branch 49 (.leaf 1142583306) (.leaf 1113387382)) (.branch 51 (.leaf 1085058440) (.leaf 1057565129)))) (.branch 56 (.branch 54 (.branch 53 (.leaf 1030877472) (.leaf 1004966795)) (.branch 55 (.leaf 979805663) (.leaf 955367815))) (.branch 58 (.branch 57 (.leaf 931628110) (.leaf 908562467)) (.branch 59 (.leaf 886147815) (.leaf 864362042))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf 843183952) (.branch 62 (.leaf 822593214) (.leaf 802570328))) (.branch 65 (.branch 64 (.leaf 783096579) (.leaf 764154006)) (.branch 66 (.leaf 745725358) (.leaf 727794070)))) (.branch 71 (.branch 69 (.branch 68 (.leaf 710344223) (.leaf 693360520)) (.branch 70 (.leaf 676828253) (.leaf 660733281))) (.branch 73 (.branch 72 (.leaf 645061998) (.leaf 629801313)) (.branch 74 (.leaf 614938626) (.leaf 600461807))))) (.branch 82 (.branch 78 (.branch 76 (.leaf 586359173) (.branch 77 (.leaf 572619469) (.leaf 559231851))) (.branch 80 (.branch 79 (.leaf 546185865) (.leaf 533471435)) (.branch 81 (.leaf 521078840) (.leaf 508998705)))) (.branch 86 (.branch 84 (.branch 83 (.leaf 497221983) (.leaf 485739943)) (.branch 85 (.leaf 474544154) (.leaf 463626477))) (.branch 88 (.branch 87 (.leaf 452979047) (.leaf 442594269)) (.branch 89 (.leaf 432464799) (.leaf 422583541)))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf 412943632) (.branch 92 (.leaf 403538437) (.leaf 394361536))) (.branch 95 (.branch 94 (.leaf 385406716) (.leaf 376667966)) (.branch 96 (.leaf 368139467) (.leaf 359815584)))) (.branch 101 (.branch 99 (.branch 98 (.leaf 351690860) (.leaf 343760010)) (.branch 100 (.leaf 336017911) (.leaf 328459601))) (.branch 103 (.branch 102 (.leaf 321080270) (.leaf 313875252)) (.branch 104 (.leaf 306840027) (.leaf 299970207))))) (.branch 113 (.branch 109 (.branch 107 (.branch 106 (.leaf 293261538) (.leaf 286709892)) (.branch 108 (.leaf 280311261) (.leaf 274061758))) (.branch 111 (.branch 110 (.leaf 267957608) (.leaf 261995145)) (.branch 112 (.leaf 256170810) (.leaf 250481145)))) (.branch 117 (.branch 115 (.branch 114 (.leaf 244922792) (.leaf 239492486)) (.branch 116 (.leaf 234187057) (.leaf 229003422))) (.branch 119 (.branch 118 (.leaf 223938584) (.leaf 218989630)) (.branch 120 (.leaf 214153728) (.leaf 209428121)))))))) : IntegerLookupTree).get j.val

private noncomputable def errorValues (j : Fin 121) : ℚ := (errorNumerators j : ℚ)/10000000000

private theorem prefactorValue : (generalMeanRows 349).prefactor = (4853112585829407/1000000000000000) := by
  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument,
    logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  try simp only [expUpperRoundedQ_eq_integer]
  decide +kernel

private theorem cutoffLogValue : (logRoundedQ ((generalMeanRows 349).cutoff/(generalMeanRows 349).c)).2 =
    (359452353603627/1000000000000000) := by
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem errorValue (j : ℕ) (hj : j < 121) :
    (generalMeanRows 349).error (generalMeanGrid j) = errorValues ⟨j,hj⟩ := by
  have hall : ∀ j : Fin 121, (generalMeanRows 349).error (generalMeanGrid j.val) = errorValues j := by
    simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue, cutoffLogValue]
    have hfirst : (generalMeanRows 349).q*(generalMeanRows 349).c/2-2 = (43/50:ℚ) := by decide +kernel
    simp only [hfirst, GeneralMeanDecayTable020.value]
    have hcontinuation : (generalMeanRows 349).q*(generalMeanRows 349).cutoff/2-2 = (4234/2019:ℚ) := by decide +kernel
    simp only [hcontinuation, GeneralMeanDecayTable149.value]
    try simp only [expUpperRoundedQ_eq_integer]
    decide +kernel
  exact hall ⟨j,hj⟩

private theorem prefactorDomain : roundUpQ (generalMeanRows 349).prefactorArgument < 82 :=
  generalMeanRows_prefactorDomain 349

private theorem slopePositive (j : Fin 120) : 0 < (generalMeanRows 349).criticalRate j.val := by
  simp only [GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  rw [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  decide +kernel

private theorem criticalMargin (j : Fin 120) :
    0 ≤ 2+(generalMeanRows 349).criticalRate j.val*(generalMeanRows 349).criticalPoint j.val-
      (logRoundedQ ((generalMeanRows 349).c*(generalMeanRows 349).criticalPoint j.val)).2-
      (generalMeanRows 349).J/2-(generalMeanRows 349).error (generalMeanGrid j.val)+
      (generalMeanRows 349).slope j.val*generalMeanGrid j.val := by
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope]
  simp only [errorValue j.val (by omega), errorValue (j.val+1) (by omega)]
  revert j
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*(generalMeanRows 349).c)).2-
      (generalMeanRows 349).J/2-(generalMeanRows 349).error 4 := by
  have he : (generalMeanRows 349).error 4 = errorValues 120 := by
    convert errorValue 120 (by decide) using 1 <;> norm_num [generalMeanGrid]
  rw [he]
  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
  decide +kernel

theorem numerical : GeneralMeanNumericalConditions (generalMeanRows 349) :=
  generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains 349)
    prefactorDomain slopePositive criticalMargin finalMargin

end SingularValueBounds.KL.Certificates.EntropyRow0349

namespace SingularValueBounds.KL.Certificates
theorem generalMeanEntropyBlock04 (i : Fin 70) :
    GeneralMeanNumericalConditions (generalMeanRowBlocks 4 i) := by
  fin_cases i
  · exact EntropyRow0280.numerical
  · exact EntropyRow0281.numerical
  · exact EntropyRow0282.numerical
  · exact EntropyRow0283.numerical
  · exact EntropyRow0284.numerical
  · exact EntropyRow0285.numerical
  · exact EntropyRow0286.numerical
  · exact EntropyRow0287.numerical
  · exact EntropyRow0288.numerical
  · exact EntropyRow0289.numerical
  · exact EntropyRow0290.numerical
  · exact EntropyRow0291.numerical
  · exact EntropyRow0292.numerical
  · exact EntropyRow0293.numerical
  · exact EntropyRow0294.numerical
  · exact EntropyRow0295.numerical
  · exact EntropyRow0296.numerical
  · exact EntropyRow0297.numerical
  · exact EntropyRow0298.numerical
  · exact EntropyRow0299.numerical
  · exact EntropyRow0300.numerical
  · exact EntropyRow0301.numerical
  · exact EntropyRow0302.numerical
  · exact EntropyRow0303.numerical
  · exact EntropyRow0304.numerical
  · exact EntropyRow0305.numerical
  · exact EntropyRow0306.numerical
  · exact EntropyRow0307.numerical
  · exact EntropyRow0308.numerical
  · exact EntropyRow0309.numerical
  · exact EntropyRow0310.numerical
  · exact EntropyRow0311.numerical
  · exact EntropyRow0312.numerical
  · exact EntropyRow0313.numerical
  · exact EntropyRow0314.numerical
  · exact EntropyRow0315.numerical
  · exact EntropyRow0316.numerical
  · exact EntropyRow0317.numerical
  · exact EntropyRow0318.numerical
  · exact EntropyRow0319.numerical
  · exact EntropyRow0320.numerical
  · exact EntropyRow0321.numerical
  · exact EntropyRow0322.numerical
  · exact EntropyRow0323.numerical
  · exact EntropyRow0324.numerical
  · exact EntropyRow0325.numerical
  · exact EntropyRow0326.numerical
  · exact EntropyRow0327.numerical
  · exact EntropyRow0328.numerical
  · exact EntropyRow0329.numerical
  · exact EntropyRow0330.numerical
  · exact EntropyRow0331.numerical
  · exact EntropyRow0332.numerical
  · exact EntropyRow0333.numerical
  · exact EntropyRow0334.numerical
  · exact EntropyRow0335.numerical
  · exact EntropyRow0336.numerical
  · exact EntropyRow0337.numerical
  · exact EntropyRow0338.numerical
  · exact EntropyRow0339.numerical
  · exact EntropyRow0340.numerical
  · exact EntropyRow0341.numerical
  · exact EntropyRow0342.numerical
  · exact EntropyRow0343.numerical
  · exact EntropyRow0344.numerical
  · exact EntropyRow0345.numerical
  · exact EntropyRow0346.numerical
  · exact EntropyRow0347.numerical
  · exact EntropyRow0348.numerical
  · exact EntropyRow0349.numerical
end SingularValueBounds.KL.Certificates
